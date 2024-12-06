// Copyright 2017 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package main

import (
	"bytes"
	"fmt"
	"math/rand"
	"os"
	"runtime/debug"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/google/syzkaller/pkg/cover"
	"github.com/google/syzkaller/pkg/hash"
	"github.com/google/syzkaller/pkg/ipc"
	"github.com/google/syzkaller/pkg/log"
	"github.com/google/syzkaller/pkg/osutil"
	"github.com/google/syzkaller/pkg/rpctype"
	"github.com/google/syzkaller/pkg/signal"
	"github.com/google/syzkaller/prog"
)

const (
	programLength = 30
)

// Proc represents a single fuzzing process (executor).
type Proc struct {
	fuzzer            *Fuzzer
	pid               int
	env               *ipc.Env
	rnd               *rand.Rand
	execOpts          *ipc.ExecOpts
	execOptsCover     *ipc.ExecOpts
	execOptsComps     *ipc.ExecOpts
	execOptsNoCollide *ipc.ExecOpts
}

func newProc(fuzzer *Fuzzer, pid int) (*Proc, error) {
	env, err := ipc.MakeEnv(fuzzer.config, pid)
	if err != nil {
		return nil, err
	}
	rnd := rand.New(rand.NewSource(time.Now().UnixNano() + int64(pid)*1e12))
	execOptsNoCollide := *fuzzer.execOpts
	execOptsNoCollide.Flags &= ^ipc.FlagCollide
	execOptsCover := execOptsNoCollide
	execOptsCover.Flags |= ipc.FlagCollectCover
	execOptsComps := execOptsNoCollide
	execOptsComps.Flags |= ipc.FlagCollectComps
	proc := &Proc{
		fuzzer:            fuzzer,
		pid:               pid,
		env:               env,
		rnd:               rnd,
		execOpts:          fuzzer.execOpts,
		execOptsCover:     &execOptsCover,
		execOptsComps:     &execOptsComps,
		execOptsNoCollide: &execOptsNoCollide,
	}
	return proc, nil
}

func (proc *Proc) loop() {
	generatePeriod := 100
	if proc.fuzzer.config.Flags&ipc.FlagSignal == 0 {
		// If we don't have real coverage signal, generate programs more frequently
		// because fallback signal is weak.
		generatePeriod = 2
	}
	for i := 0; ; i++ {
		item := proc.fuzzer.workQueue.dequeue()
		if item != nil {
			switch item := item.(type) {
			case *WorkTriage:
				proc.triageInput(item)
			case *WorkCandidate:
				proc.execute(proc.execOpts, item.p, item.flags, StatCandidate)
			case *WorkSmash:
				proc.smashInput(item)
			default:
				log.Fatalf("unknown work type: %#v", item)
			}
			continue
		}

		ct := proc.fuzzer.choiceTable
		fuzzerSnapshot := proc.fuzzer.snapshot()
		if len(fuzzerSnapshot.corpus) == 0 || i%generatePeriod == 0 {
			// Generate a new prog.
			p := proc.fuzzer.target.Generate(proc.rnd, programLength, ct)
			log.Logf(1, "#%v: generated", proc.pid)
			proc.execute(proc.execOpts, p, ProgNormal, StatGenerate)
		} else {
			// Mutate an existing prog.
			p := fuzzerSnapshot.chooseProgram(proc.rnd).Clone()
			p.Mutate(proc.rnd, programLength, ct, fuzzerSnapshot.corpus)
			log.Logf(1, "#%v: mutated", proc.pid)
			proc.execute(proc.execOpts, p, ProgNormal, StatFuzz)
		}
	}
}

func (proc *Proc) triageInput(item *WorkTriage) {
	// Alper
	log.Logf(0, "TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT triage called") // DELETE(Alper)
	syscallNumber := uint32(1000000000)
	syscallArg := uint32(1000000000)
	syscallResults := []byte{97, 10}

	log.Logf(1, "#%v: triaging type=%x", proc.pid, item.flags)

	prio := signalPrio(item.p, &item.info, item.call)
	inputSignal := signal.FromRaw(item.info.Signal, prio)
	newSignal := proc.fuzzer.corpusSignalDiff(inputSignal)
	if newSignal.Empty() {
		return
	}
	callName := ".extra"
	logCallName := "extra"
	if item.call != -1 {
		callName = item.p.Calls[item.call].Meta.Name
		logCallName = fmt.Sprintf("call #%v %v", item.call, callName)
	}
	log.Logf(3, "triaging input for %v (new signal=%v)", logCallName, newSignal.Len())
	var inputCover cover.Cover
	const (
		signalRuns       = 3
		minimizeAttempts = 3
	)
	// Compute input coverage and non-flaky signal for minimization.
	notexecuted := 0
	for i := 0; i < signalRuns; i++ {
		info := proc.executeRaw(proc.execOptsCover, item.p, StatTriage)
		if !reexecutionSuccess(info, &item.info, item.call) {
			// The call was not executed or failed.
			notexecuted++
			if notexecuted > signalRuns/2+1 {
				return // if happens too often, give up
			}
			continue
		}
		thisSignal, thisCover := getSignalAndCover(item.p, info, item.call)
		newSignal = newSignal.Intersection(thisSignal)
		// Without !minimized check manager starts losing some considerable amount
		// of coverage after each restart. Mechanics of this are not completely clear.
		if newSignal.Empty() && item.flags&ProgMinimized == 0 {
			return
		}
		inputCover.Merge(thisCover)

		// Alper
		// TODO(Alper) merge taint results
		syscallNumber = info.SyscallNumber
		syscallArg = info.SyscallArg
		syscallResults = info.SyscallResults
	}
	if item.flags&ProgMinimized == 0 {
		item.p, item.call = prog.Minimize(item.p, item.call, false,
			func(p1 *prog.Prog, call1 int) bool {
				for i := 0; i < minimizeAttempts; i++ {
					// TODO(Alper): do I want to save this taint information?
					info := proc.execute(proc.execOptsNoCollide, p1, ProgNormal, StatMinimize)
					if !reexecutionSuccess(info, &item.info, call1) {
						// The call was not executed or failed.
						continue
					}
					thisSignal, _ := getSignalAndCover(p1, info, call1)
					if newSignal.Intersection(thisSignal).Len() == newSignal.Len() {
						return true
					}
				}
				return false
			})
	}

	data := item.p.Serialize()
	sig := hash.Hash(data)

	log.Logf(2, "added new input for %v to corpus:\n%s", logCallName, data)
	log.Logf(0, "GGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGG") // DELETE(Alper)
	// TODO(Alper): fill in syscall data, also make them a slice or serialize it before this point
	// TODO(Alper): new rpc for thingy
	proc.fuzzer.sendInputToManager(rpctype.RPCInput{
		Call:   callName,
		Prog:   data,
		Signal: inputSignal.Serialize(),
		Cover:  inputCover.Serialize(),

		// Alper
		SyscallNumber:  syscallNumber,
		SyscallArg:     syscallArg,
		SyscallResults: syscallResults,
	})

	proc.fuzzer.addInputToCorpus(item.p, inputSignal, sig)

	if item.flags&ProgSmashed == 0 {
		proc.fuzzer.workQueue.enqueue(&WorkSmash{item.p, item.call})
	}
}

func reexecutionSuccess(info *ipc.ProgInfo, oldInfo *ipc.CallInfo, call int) bool {
	if info == nil || len(info.Calls) == 0 {
		return false
	}
	if call != -1 {
		// Don't minimize calls from successful to unsuccessful.
		// Successful calls are much more valuable.
		if oldInfo.Errno == 0 && info.Calls[call].Errno != 0 {
			return false
		}
		return len(info.Calls[call].Signal) != 0
	}
	return len(info.Extra.Signal) != 0
}

func getSignalAndCover(p *prog.Prog, info *ipc.ProgInfo, call int) (signal.Signal, []uint32) {
	inf := &info.Extra
	if call != -1 {
		inf = &info.Calls[call]
	}
	return signal.FromRaw(inf.Signal, signalPrio(p, inf, call)), inf.Cover
}

func (proc *Proc) smashInput(item *WorkSmash) {
	if proc.fuzzer.faultInjectionEnabled && item.call != -1 {
		proc.failCall(item.p, item.call)
	}
	if proc.fuzzer.comparisonTracingEnabled && item.call != -1 {
		proc.executeHintSeed(item.p, item.call)
	}
	fuzzerSnapshot := proc.fuzzer.snapshot()
	for i := 0; i < 100; i++ {
		p := item.p.Clone()
		p.Mutate(proc.rnd, programLength, proc.fuzzer.choiceTable, fuzzerSnapshot.corpus)
		log.Logf(1, "#%v: smash mutated", proc.pid)
		proc.execute(proc.execOpts, p, ProgNormal, StatSmash)
	}
}

func (proc *Proc) failCall(p *prog.Prog, call int) {
	for nth := 0; nth < 100; nth++ {
		log.Logf(1, "#%v: injecting fault into call %v/%v", proc.pid, call, nth)
		opts := *proc.execOpts
		opts.Flags |= ipc.FlagInjectFault
		opts.FaultCall = call
		opts.FaultNth = nth
		info := proc.executeRaw(&opts, p, StatSmash)
		if info != nil && len(info.Calls) > call && info.Calls[call].Flags&ipc.CallFaultInjected == 0 {
			break
		}
	}
}

func (proc *Proc) executeHintSeed(p *prog.Prog, call int) {
	log.Logf(1, "#%v: collecting comparisons", proc.pid)
	// First execute the original program to dump comparisons from KCOV.
	info := proc.execute(proc.execOptsComps, p, ProgNormal, StatSeed)
	if info == nil {
		return
	}

	// Then mutate the initial program for every match between
	// a syscall argument and a comparison operand.
	// Execute each of such mutants to check if it gives new coverage.
	p.MutateWithHints(call, info.Calls[call].Comps, func(p *prog.Prog) {
		log.Logf(1, "#%v: executing comparison hint", proc.pid)
		proc.execute(proc.execOpts, p, ProgNormal, StatHint)
	})
}

func (proc *Proc) execute(execOpts *ipc.ExecOpts, p *prog.Prog, flags ProgTypes, stat Stat) *ipc.ProgInfo {
	log.Logf(0, "EEEEEEEEEEEEEEEEEEEEEEEEE execute called") // DELETE(Alper)
	info := proc.executeRaw(execOpts, p, stat)
	calls, extra := proc.fuzzer.checkNewSignal(p, info)
	for _, callIndex := range calls {
		proc.enqueueCallTriage(p, flags, callIndex, info.Calls[callIndex])
	}
	if extra {
		proc.enqueueCallTriage(p, flags, -1, info.Extra)
	}
	return info
}

func (proc *Proc) enqueueCallTriage(p *prog.Prog, flags ProgTypes, callIndex int, info ipc.CallInfo) {
	// info.Signal points to the output shmem region, detach it before queueing.
	info.Signal = append([]uint32{}, info.Signal...)
	// None of the caller use Cover, so just nil it instead of detaching.
	// Note: triage input uses executeRaw to get coverage.
	info.Cover = nil
	proc.fuzzer.workQueue.enqueue(&WorkTriage{
		p:     p.Clone(),
		call:  callIndex,
		info:  info,
		flags: flags,
	})
}

var tmpCtr = 0 ////

// Alper
var mycounter = 0

func (proc *Proc) executeRaw(opts *ipc.ExecOpts, p *prog.Prog, stat Stat) *ipc.ProgInfo {
	if opts.Flags&ipc.FlagDedupCover == 0 {
		log.Fatalf("dedup cover is not enabled")
	}

	// Ensures rpc calls unrelated to snapshotting are not made during testing
	proc.fuzzer.rpcMu.Lock()
	defer proc.fuzzer.rpcMu.Unlock()

	// Limit concurrency window and do leak checking once in a while.
	ticket := proc.fuzzer.gate.Enter()
	defer proc.fuzzer.gate.Leave(ticket)

	// Alper
	// Generate random syscall taint config. This has to be called before the state save or it will not advance the
	// rng internal state for the next execution.
	// TODO(Alper): keep this automatically updated
	var syscallNumbers = []int{90, 92, 85, 91, 268, 93, 260, 72, 62, 94, 265, 28, 149, 151, 9, 240, 71, 68, 70, 69, 150, 257, 82,
		264, 84, 142, 66, 64, 106, 141, 114, 119, 117, 113, 105, 30, 31, 67, 29, 87, 263, 280}
	var syscallArgs = []int{2, 3, 2, 2, 3, 3, 5, 3, 2, 3, 5, 3, 2, 1, 6, 4, 3, 2, 5, 4, 2, 4, 2, 4, 1, 2, 4, 3, 1, 3, 2, 3, 3, 2,
		1, 3, 3, 1, 3, 1, 3, 4}
	// TODO(Alper): make the rng work
	syscallIdx := rand.Intn(len(syscallArgs))
	syscallConfigNumber := syscallNumbers[syscallIdx]
	syscallConfigArg := rand.Intn(syscallArgs[syscallIdx])

	enableKdfsan := false
	if tmpCtr != 0 { ////
		log.Logf(0, "*** proc.executeRaw: Requesting snapshot save... ***\n")
		enableKdfsan = proc.fuzzer.cmdManagerToSaveSnapshot()
		log.Logf(0, "*** proc.executeRaw: Snapshot taken! Returned enableKdfsan: %t ***\n", enableKdfsan)
	}

	proc.logProgram(opts, p)

	// MARK(Alper): this is where kdfsan is configured
	if enableKdfsan {
		log.Logf(0, "*** proc.executeRaw: Enabling Kdfsan... ***\n")
		if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", "cat /sys/kernel/debug/kdfsan/enable"); err != nil {
			log.Logf(0, "Failed to enable Kdfsan: %v", err)
		}
		log.Logf(0, "*** proc.executeRaw: Kdfsan enabled ***\n")
	}

	// Alper
	// Test the taint results logger
	if enableKdfsan {
		testMyResults := false
		if testMyResults {
			log.Logf(0, "*** Filling myresults with example data ***\n")
			if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", "cat /sys/kernel/debug/alper/example"); err != nil {
				log.Logf(0, "Failed myresults example: %v", err)
			}
			log.Logf(0, "*** proc.executeRaw: Example data filled ***\n")
		}
		// Forward the config
		if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", fmt.Sprintf("echo %v > /sys/kernel/debug/alper/syscall_config_syscall", syscallConfigNumber)); err != nil {
			log.Logf(0, "Failed setting syscall nr: %v", err)
		}
		if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", fmt.Sprintf("echo %v > /sys/kernel/debug/alper/syscall_config_arg", syscallConfigArg)); err != nil {
			log.Logf(0, "Failed setting syscall nr: %v", err)
		}
		if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", "cat /sys/kernel/debug/alper/syscall_config_commit"); err != nil {
			log.Logf(0, "Failed commiting syscall config: %v", err)
		}

		log.Logf(0, "IIIIIIIIIIIIIIIIIIIIIIIIIIIII %v %v\n", syscallConfigNumber, syscallConfigArg)
	}

	for try := 0; ; try++ {
		atomic.AddUint64(&proc.fuzzer.stats[stat], 1)
		output, info, hanged, err := proc.env.Exec(opts, p)
		if err != nil {
			if try > 10 {
				log.Fatalf("executor %v failed %v times:\n%v", proc.pid, try, err)
			}
			log.Logf(4, "fuzzer detected executor failure='%v', retrying #%d", err, try+1)
			debug.FreeOSMemory()
			time.Sleep(time.Second)
			continue
		}
		log.Logf(2, "result hanged=%v: %s", hanged, output)

		// Alper
		// Read the kdfsan taint results before the snapshot is restored
		if enableKdfsan {
			data, err2 := os.ReadFile("/sys/kernel/debug/alper/results")
			if err2 != nil {
				log.Logf(0, "Failed to read /sys/kernel/debug/alper/results: %v", err2)
			} else {
				// TODO store data into info
				//log.Logf(0, "data: %v", string(data)) // print the results file
				info.SyscallNumber = uint32(syscallConfigNumber)
				info.SyscallArg = uint32(syscallConfigArg)
				info.SyscallResults = data
			}
			// Send taint log to manager before snapshot restore
			proc.fuzzer.sendTaintToManager(rpctype.RPCInput{
				SyscallNumber:  info.SyscallNumber,
				SyscallArg:     info.SyscallArg,
				SyscallResults: info.SyscallResults,
			})
		} else {
			info.SyscallNumber = uint32(1000000000)
			info.SyscallArg = uint32(1000000000)
			info.SyscallResults = []byte{98, 10}
		}

		if tmpCtr != 0 { ////
			if enableKdfsan {
				log.Logf(0, "*** proc.executeRaw: Finished test WITH Kdfsan! Requesting snapshot load... ***\n")
				proc.fuzzer.cmdManagerToLoadSnapshot()
				log.Fatalf("cmdManagerToLoadSnapshot should not return")
			} else {
				log.Logf(0, "*** proc.executeRaw: Finished test WITHOUT Kdfsan! Continuing... ***\n")
			}
		}
		tmpCtr++ ////

		return info
	}
}

func (proc *Proc) logProgram(opts *ipc.ExecOpts, p *prog.Prog) {
	if proc.fuzzer.outputType == OutputNone {
		return
	}

	data := p.Serialize()
	strOpts := ""
	if opts.Flags&ipc.FlagInjectFault != 0 {
		strOpts = fmt.Sprintf(" (fault-call:%v fault-nth:%v)", opts.FaultCall, opts.FaultNth)
	}

	// The following output helps to understand what program crashed kernel.
	// It must not be intermixed.
	switch proc.fuzzer.outputType {
	case OutputStdout:
		now := time.Now()
		proc.fuzzer.logMu.Lock()
		fmt.Printf("%02v:%02v:%02v executing program %v%v:\n%s\n",
			now.Hour(), now.Minute(), now.Second(),
			proc.pid, strOpts, data)
		proc.fuzzer.logMu.Unlock()
	case OutputDmesg:
		fd, err := syscall.Open("/dev/kmsg", syscall.O_WRONLY, 0)
		if err == nil {
			buf := new(bytes.Buffer)
			fmt.Fprintf(buf, "syzkaller: executing program %v%v:\n%s\n",
				proc.pid, strOpts, data)
			syscall.Write(fd, buf.Bytes())
			syscall.Close(fd)
		}
	case OutputFile:
		f, err := os.Create(fmt.Sprintf("%v-%v.prog", proc.fuzzer.name, proc.pid))
		if err == nil {
			if strOpts != "" {
				fmt.Fprintf(f, "#%v\n", strOpts)
			}
			f.Write(data)
			f.Close()
		}
	default:
		log.Fatalf("unknown output type: %v", proc.fuzzer.outputType)
	}
}
