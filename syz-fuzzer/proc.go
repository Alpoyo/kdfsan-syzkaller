// Copyright 2017 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package main

import (
	//"bytes"
	"fmt"
	"math"
	"math/rand"
	"os"
	"runtime/debug"
	"strconv"
	"sync/atomic"
	//"syscall"
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

// Alper
// Convenience functions
func intsSum(ints []int) int {
	sum := 0
	for i := 0; i < len(ints); i++ {
		sum += ints[i]
	}
	return sum
}
func floatsSum(floats []float64) float64 {
	var sum float64 = 0
	for i := 0; i < len(floats); i++ {
		sum += floats[i]
	}
	return sum
}
func floatsMax(floats []float64) float64 {
	var max float64 = float64(math.Inf(-1))
	for i := 0; i < len(floats); i++ {
		if floats[i] > max {
			max = floats[i]
		}
	}
	return max
}

// Alper
func u64_to_hex(n uint64) string {
	return fmt.Sprintf("0x%016x", n)
}
func u48_to_hex(n uint64) string {
	return fmt.Sprintf("0x%012x", n&0xffffffffffff)
}
func u32_to_hex(n uint32) string {
	return fmt.Sprintf("0x%08x", n)
}
func u16_to_hex(n uint16) string {
	return fmt.Sprintf("0x%04x", n)
}
func u8_to_hex(n uint8) string {
	return fmt.Sprintf("0x%02x", n)
}

// Alper
// Define syscall configurations and mappings
var attemptBuffer = [118]int{}
var syscallNumbers = []int{90, 92, 85, 91, 268, 93, 260, 72, 62, 94, 265, 28, 149, 151, 9, 240, 71, 68, 70, 69, 150, 257, 82,
	264, 84, 142, 66, 64, 106, 141, 114, 119, 117, 113, 105, 30, 31, 67, 29, 87, 263, 280}
var syscallToIdx = map[int]int{90: 0, 92: 1, 85: 2, 91: 3, 268: 4, 93: 5, 260: 6, 72: 7, 62: 8, 94: 9, 265: 10, 28: 11,
	149: 12, 151: 13, 9: 14, 240: 15, 71: 16, 68: 17, 70: 18, 69: 19, 150: 20, 257: 21, 82: 22, 264: 23, 84: 24,
	142: 25, 66: 26, 64: 27, 106: 28, 141: 29, 114: 30, 119: 31, 117: 32, 113: 33, 105: 34, 30: 35, 31: 36, 67: 37,
	29: 38, 87: 39, 263: 40, 280: 41}
var syscallArgs = []int{2, 3, 2, 2, 3, 3, 5, 3, 2, 3, 5, 3, 2, 1, 6, 4, 3, 2, 5, 4, 2, 4, 2, 4, 1, 2, 4, 3, 1, 3, 2, 3,
	3, 2, 1, 3, 3, 1, 3, 1, 3, 4}
var syscallToFlat = [][]int{{0, 1}, {2, 3, 4}, {5, 6}, {7, 8}, {9, 10, 11}, {12, 13, 14}, {15, 16, 17, 18, 19},
	{20, 21, 22}, {23, 24}, {25, 26, 27}, {28, 29, 30, 31, 32}, {33, 34, 35}, {36, 37}, {38}, {39, 40, 41, 42, 43, 44},
	{45, 46, 47, 48}, {49, 50, 51}, {52, 53}, {54, 55, 56, 57, 58}, {59, 60, 61, 62}, {63, 64}, {65, 66, 67, 68},
	{69, 70}, {71, 72, 73, 74}, {75}, {76, 77}, {78, 79, 80, 81}, {82, 83, 84}, {85}, {86, 87, 88}, {89, 90},
	{91, 92, 93}, {94, 95, 96}, {97, 98}, {99}, {100, 101, 102}, {103, 104, 105}, {106}, {107, 108, 109}, {110},
	{111, 112, 113}, {114, 115, 116, 117}}
var flatToIdx = []int{0, 0, 1, 1, 1, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 8, 8, 9, 9, 9, 10, 10, 10, 10,
	10, 11, 11, 11, 12, 12, 13, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 16, 16, 16, 17, 17, 18, 18, 18, 18, 18, 19, 19,
	19, 19, 20, 20, 21, 21, 21, 21, 22, 22, 23, 23, 23, 23, 24, 25, 25, 26, 26, 26, 26, 27, 27, 27, 28, 29, 29, 29, 30,
	30, 31, 31, 31, 32, 32, 32, 33, 33, 34, 35, 35, 35, 36, 36, 36, 37, 38, 38, 38, 39, 40, 40, 40, 41, 41, 41, 41}
var flatToSys = []int{90, 90, 92, 92, 92, 85, 85, 91, 91, 268, 268, 268, 93, 93, 93, 260, 260, 260, 260, 260, 72, 72, 72,
	62, 62, 94, 94, 94, 265, 265, 265, 265, 265, 28, 28, 28, 149, 149, 151, 9, 9, 9, 9, 9, 9, 240, 240, 240, 240, 71,
	71, 71, 68, 68, 70, 70, 70, 70, 70, 69, 69, 69, 69, 150, 150, 257, 257, 257, 257, 82, 82, 264, 264, 264, 264, 84,
	142, 142, 66, 66, 66, 66, 64, 64, 64, 106, 141, 141, 141, 114, 114, 119, 119, 119, 117, 117, 117, 113, 113, 105, 30,
	30, 30, 31, 31, 31, 67, 29, 29, 29, 87, 263, 263, 263, 280, 280, 280, 280}
var flatToArg = []int{0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2, 3, 4, 0, 1, 2, 0, 1, 0, 1, 2, 0, 1, 2, 3, 4,
	0, 1, 2, 0, 1, 0, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 0, 1, 0,
	1, 2, 3, 0, 0, 1, 0, 1, 2, 3, 0, 1, 2, 0, 0, 1, 2, 0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 0, 0, 1, 2, 0, 1, 2, 0, 0, 1, 2, 0,
	0, 1, 2, 0, 1, 2, 3}
var aggrAttempts = [118]int{}
var aggrHits = [118]int{}

// Alper
var attemptCommCounter = 0

func (proc *Proc) executeRaw(opts *ipc.ExecOpts, p *prog.Prog, stat Stat) *ipc.ProgInfo {
	if opts.Flags&ipc.FlagDedupCover == 0 {
		log.Fatalf("dedup cover is not enabled")
	}

	// Alper
	// Define constants
	const doMylog = false    // Default: false
	const logResults = false // Default: false
	const doSyscallOnly = -1 // Default: -1
	const doVerbose = false  // Default: false

	// Ensures rpc calls unrelated to snapshotting are not made during testing
	proc.fuzzer.rpcMu.Lock()
	defer proc.fuzzer.rpcMu.Unlock()

	// Limit concurrency window and do leak checking once in a while.
	ticket := proc.fuzzer.gate.Enter()
	defer proc.fuzzer.gate.Leave(ticket)

	// Alper
	// check whether the tainted is present in the input program
	// TODO . . .
	var inputProgStr = "input program: "
	for _, call := range p.Calls {
		inputProgStr += call.Meta.CallName
		inputProgStr += ", "
	}

	// Alper
	// Generate random syscall taint config. Use inverse hit rates as the weights for the random sampling
	numHits := intsSum(aggrHits[:])
	const hitlessFactor float64 = 2.0
	var syscallIdx int
	var syscallConfigNumber int
	var syscallConfigArg int
	if numHits == 0 {
		syscallIdx = proc.rnd.Intn(len(syscallArgs))
		syscallConfigNumber = syscallNumbers[syscallIdx]
		syscallConfigArg = proc.rnd.Intn(syscallArgs[syscallIdx])
	} else {
		// Calculate weights
		inverseHitRates := [118]float64{}
		for i := 0; i < 118; i++ {
			if aggrHits[i] == 0 {
				inverseHitRates[i] = -1
			} else {
				inverseHitRates[i] = float64(aggrAttempts[i]) / float64(aggrHits[i])
			}
		}
		noHitWeight := floatsMax(inverseHitRates[:]) * hitlessFactor
		for i := 0; i < 118; i++ {
			if inverseHitRates[i] == -1 {
				inverseHitRates[i] = noHitWeight
			}
		}
		// Now sample config by weight
		rndCur := proc.rnd.Float64() * floatsSum(inverseHitRates[:])
		var cumSum float64 = 0
		var syscallConfigFlat int = 0
		for i := 0; i < 118; i++ {
			cumSum += inverseHitRates[i]
			if cumSum > rndCur {
				syscallConfigFlat = i
				break
			}
		}

		syscallConfigNumber = flatToSys[syscallConfigFlat]
		syscallConfigArg = flatToArg[syscallConfigFlat]
		syscallIdx = flatToIdx[syscallConfigFlat]
	}

	// Just a single configuration
	if doSyscallOnly != -1 {
		syscallConfigNumber = doSyscallOnly
		syscallIdx = 0
		for i := 0; i < len(syscallNumbers); i++ {
			if syscallNumbers[i] == doSyscallOnly {
				syscallIdx = i
				break
			}
		}
		syscallConfigArg = proc.rnd.Intn(syscallArgs[syscallIdx])
	}

	proc.logProgram(opts, p)

	// MARK(Alper): this is where kdfsan is configured
	//if enableKdfsan {
	// TODO(Alper): move to vm init or something
	if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", "cat /sys/kernel/debug/kdfsan/enable"); err != nil {
		log.Logf(0, "Failed to enable Kdfsan: %v", err)
	}

	// Alper
	// Forward the config to kernel
	var configStr = u16_to_hex(uint16(syscallConfigNumber)) + " " + u8_to_hex(uint8(syscallConfigArg))
	if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c",
		fmt.Sprintf("echo '%v' > /sys/kernel/debug/alper/syscall_config", configStr)); err != nil {
		log.Logf(0, "Failed commiting syscall config: %v", err)
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
		// Print the log during this execution
		mylogStr := ""
		if doMylog {
			mylogData, err := os.ReadFile("/sys/kernel/debug/alper/mylog")
			if err != nil {
				log.Logf(0, "Failed to read /sys/kernel/debug/alper/mylog: %v", err)
			}
			mylogStr = string(mylogData)
			log.Logf(0, "\033[38;2;0;150;255mMYLOG\n%v\033[0m", mylogStr)
			_, err = os.ReadFile("/sys/kernel/debug/alper/mylog_clear")
			if err != nil {
				log.Logf(0, "Failed to read /sys/kernel/debug/alper/mylog_clear: %v", err)
			}
		}
		// Read the kdfsan taint results
		// Disable tainted syscalls
		if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", "echo 0xffffffffffffffff > /sys/kernel/debug/alper/syscall_config_syscall"); err != nil {
			log.Logf(0, "Failed setting syscall nr: %v", err)
		}
		if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", "echo 0xffffffffffffffff > /sys/kernel/debug/alper/syscall_config_arg"); err != nil {
			log.Logf(0, "Failed setting syscall arg: %v", err)
		}
		if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", "echo 0xffffffffffffffff > /sys/kernel/debug/alper/syscall_config_layer"); err != nil {
			log.Logf(0, "Failed setting syscall layer: %v", err)
		}
		if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", "cat /sys/kernel/debug/alper/syscall_config_commit"); err != nil {
			log.Logf(0, "Failed commiting syscall config: %v", err)
		}
		if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", "cat /sys/kernel/debug/alper/flush"); err != nil {
			log.Logf(0, "Failed flushing shadow mem: %v", err)
		}

		// Read and clear the results file
		data, err2 := os.ReadFile("/sys/kernel/debug/alper/results")
		if err2 != nil {
			log.Logf(0, "Failed to read /sys/kernel/debug/alper/results: %v", err2)
		} else {
			//log.Logf(0, "data: %v", string(data)) // print the results file
			info.SyscallNumber = uint32(syscallConfigNumber)
			info.SyscallArg = uint32(syscallConfigArg)
			info.SyscallResults = data
		}
		_, err3 := os.ReadFile("/sys/kernel/debug/alper/clear")
		if err3 != nil {
			log.Logf(0, "Failed to read /sys/kernel/debug/alper/clear: %v", err3)
		}

		// Send taint log to manager before snapshot restore, if there was any taint
		if logResults {
			log.Logf(0, "\033[38;2;255;255;0m%v\033[0m\n", string(data))
		}
		myresult_count, errParse := strconv.ParseInt(string(data[21:29]), 16, 32)
		if myresult_count > 0 && errParse == nil {
			proc.fuzzer.sendTaintToManager(rpctype.RPCInput{
				SyscallNumber:  info.SyscallNumber,
				SyscallArg:     info.SyscallArg,
				SyscallResults: info.SyscallResults,
				InputProgram:   inputProgStr,
				InputProgram2:  p.Serialize(),
				MyLog:          mylogStr,
			})
		} else {
			var configFlat = syscallToFlat[syscallToIdx[syscallConfigNumber]][syscallConfigArg]
			attemptBuffer[configFlat]++

			const attemptCommInterval = 10
			attemptCommCounter++
			if attemptCommCounter >= attemptCommInterval {
				/* Send attempt buffer and clear */
				attemptCommCounter = 0
				var r = proc.fuzzer.sendAttemptToManager(rpctype.NewAttempt{
					Attempts: attemptBuffer,
				})
				for i := 0; i < len(attemptBuffer); i++ {
					attemptBuffer[i] = 0
					aggrAttempts[i] = r[i]
					aggrHits[i] = r[i+118]
				}
			}
		}

		return info
	}
}

func (proc *Proc) logProgram(opts *ipc.ExecOpts, p *prog.Prog) {
	// Alper
	// Fake log to speed it up. The manager expects a log, so we provide a fake one so it's not killed
	// TODO maybe disable this?
	now := time.Now()        //
	proc.fuzzer.logMu.Lock() //
	fmt.Printf("%02v:%02v:%02v executing program 0:\nmmap\n", //
		now.Hour(), now.Minute(), now.Second()) //
	proc.fuzzer.logMu.Unlock()                  //
	return                                      //

	//if proc.fuzzer.outputType == OutputNone {
	//	return
	//}
	//
	//data := p.Serialize()
	//strOpts := ""
	//if opts.Flags&ipc.FlagInjectFault != 0 {
	//	strOpts = fmt.Sprintf(" (fault-call:%v fault-nth:%v)", opts.FaultCall, opts.FaultNth)
	//}
	//
	//// The following output helps to understand what program crashed kernel.
	//// It must not be intermixed.
	//switch proc.fuzzer.outputType {
	//case OutputStdout:
	//	now := time.Now()
	//	proc.fuzzer.logMu.Lock()
	//	fmt.Printf("%02v:%02v:%02v executing program %v%v:\n%s\n",
	//		now.Hour(), now.Minute(), now.Second(),
	//		proc.pid, strOpts, data)
	//	proc.fuzzer.logMu.Unlock()
	//case OutputDmesg:
	//	fd, err := syscall.Open("/dev/kmsg", syscall.O_WRONLY, 0)
	//	if err == nil {
	//		buf := new(bytes.Buffer)
	//		fmt.Fprintf(buf, "syzkaller: executing program %v%v:\n%s\n",
	//			proc.pid, strOpts, data)
	//		syscall.Write(fd, buf.Bytes())
	//		syscall.Close(fd)
	//	}
	//case OutputFile:
	//	f, err := os.Create(fmt.Sprintf("%v-%v.prog", proc.fuzzer.name, proc.pid))
	//	if err == nil {
	//		if strOpts != "" {
	//			fmt.Fprintf(f, "#%v\n", strOpts)
	//		}
	//		f.Write(data)
	//		f.Close()
	//	}
	//default:
	//	log.Fatalf("unknown output type: %v", proc.fuzzer.outputType)
	//}
}
