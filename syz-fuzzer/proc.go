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
	}
	if item.flags&ProgMinimized == 0 {
		item.p, item.call = prog.Minimize(item.p, item.call, false,
			func(p1 *prog.Prog, call1 int) bool {
				for i := 0; i < minimizeAttempts; i++ {
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
	proc.fuzzer.sendInputToManager(rpctype.RPCInput{
		Call:   callName,
		Prog:   data,
		Signal: inputSignal.Serialize(),
		Cover:  inputCover.Serialize(),
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
func intsShuffle(ints []int, rnd *rand.Rand) {
	if ints == nil {
		return
	}
	// Knuth
	for i := 0; i < len(ints); i++ {
		j := rnd.Intn(len(ints)-i) + i
		swap := ints[j]
		ints[j] = ints[i]
		ints[i] = swap
	}
}
func intsSeq(n int) []int {
	ints := make([]int, n)
	for i := 0; i < n; i++ {
		ints[i] = i
	}
	return ints
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
var syscallNames = []string{
	"chmod", "chown", "creat", "fchmod", "fchmodat", "fchown", "fchownat", "fcntl",
	"kill", "lchown", "linkat", "madvise", "mlock", "mlockall", "mmap", "mq_open",
	"msgctl", "msgget", "msgrcv", "msgsnd", "munlock", "openat", "rename", "renameat",
	"rmdir", "sched_setparam", "semctl", "semget", "setgid", "setpriority", "setregid", "setresgid",
	"setresuid", "setreuid", "setuid", "shmat", "shmctl", "shmdt", "shmget", "unlink", "unlinkat", "utimensat"}
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
var noneConfig = 65535
var aggrAttempts = [118]int{}
var aggrHits = [118]int{}

// Alper
var attemptCommCounter = 0
var initIsDone = false
var tmpCtr = 0 ////

// Return the index of the sampled element
func pmfSample(pmf []float64, rnd *rand.Rand) int {
	rndCur := rnd.Float64() * floatsSum(pmf)
	var cmfCur float64 = 0
	var elementIdx int = 0
	for i := 0; i < 118; i++ {
		if pmf[i] == 0 {
			continue
		}
		cmfCur += pmf[i]
		if cmfCur > rndCur {
			elementIdx = i
			break
		}
	}

	// Just in case: handle float jank, if something with 0 probability is picked, pick the first one with non-zero
	// probability.
	if pmf[elementIdx] == 0 {
		for i := 0; i < len(pmf); i++ {
			if pmf[i] != 0 {
				return i
			}
		}
	}

	return elementIdx
}

func (proc *Proc) executeRaw(opts *ipc.ExecOpts, p *prog.Prog, stat Stat) *ipc.ProgInfo {
	if opts.Flags&ipc.FlagDedupCover == 0 {
		log.Fatalf("dedup cover is not enabled")
	}

	// Alper
	// Define constants
    const useFlush = true       // Default: true
	const doMylog = false       // Default: false
	const doUniformOnly = true  // Default: true
	const logResults = false    // Default: false
	const doSyscallOnly = -1    // Default: -1
	const doVerbose = false     // Default: false
	const hitLimit = 1000000000 // Default: 1000000000
    const useMultiTaint = true  // Default: true
    const useParseInput = true  // Default: true

	// Ensures rpc calls unrelated to snapshotting are not made during testing
	proc.fuzzer.rpcMu.Lock()
	defer proc.fuzzer.rpcMu.Unlock()

	// Limit concurrency window and do leak checking once in a while.
	ticket := proc.fuzzer.gate.Enter()
	defer proc.fuzzer.gate.Leave(ticket)

	if !initIsDone {
		initIsDone = true
        if useFlush {
            if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", "cat /sys/kernel/debug/kdfsan/enable"); err != nil {
                log.Logf(0, "Failed to enable Kdfsan: %v", err)
            }

            // flush for good measure
            os.ReadFile("/sys/kernel/debug/alper/flush")
        }
		
        // Request the attempts statistics on startup
		var r = proc.fuzzer.sendAttemptToManager(rpctype.NewAttempt{
			Attempts: [118]int{},
		})
		for i := 0; i < len(aggrAttempts); i++ {
			aggrAttempts[i] = r[i]
			aggrHits[i] = r[i+118]
		}
	}

    enableKdfsan := false
    if !useFlush {
        if tmpCtr != 0 { ////
            log.Logf(0, "*** proc.executeRaw: Requesting snapshot save... ***\n")
            enableKdfsan = proc.fuzzer.cmdManagerToSaveSnapshot()
            log.Logf(0, "*** proc.executeRaw: Snapshot taken! Returned enableKdfsan: %t ***\n", enableKdfsan)
        }
    }

	// Alper
	// check whether the tainted is present in the input program
	var inputProgStr = "input program: "
	var progSyscalls []string
	var presentMask = [118]int{}
	presentCount := 0
    for _, call := range p.Calls {
        sysNameCur := call.Meta.CallName
        progSyscalls = append(progSyscalls, sysNameCur)

        // append to program string
        inputProgStr += sysNameCur
        inputProgStr += ", "
    }
    if useParseInput {
        for i := 0; i < len(syscallNames); i++ {
            for j := 0; j < len(progSyscalls); j++ {
                if progSyscalls[j] == syscallNames[i] {
                    for k := 0; k < syscallArgs[i]; k++ {
                        flatCur := syscallToFlat[i][k]
                        presentMask[flatCur] = 1
                        presentCount++
                    }
                    break
                }
            }
        }
    } else {
        for i := 0; i < len(presentMask); i++ {
            presentMask[i] = 1
        }
        presentCount = len(presentMask)
    }

	// Alper
	// Generate random syscall taint config. Use inverse hit rates as the weights for the random sampling
	numHits := intsSum(aggrHits[:])
	const hitlessFactor float64 = 2.0
	var syscallConfigs [8]int
	for i := 0; i < 8; i++ {
		syscallConfigs[i] = -1
	}
	if numHits == 0 || doUniformOnly {
		// No hit-rate statistics -> use uniform distribution
		var seq []int
		for i := 0; i < len(presentMask); i++ {
			if presentMask[i] == 1 {
				seq = append(seq, i)
			}
		}
		intsShuffle(seq, proc.rnd)
		for i := 0; i < 8 && i < len(seq); i++ {
			syscallConfigs[i] = seq[i]
		}
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
		// Apply present mask
		for i := 0; i < len(presentMask); i++ {
			inverseHitRates[i] *= float64(presentMask[i])
		}
		// Apply 10K limit
		for i := 0; i < len(inverseHitRates); i++ {
			if aggrHits[i] >= hitLimit {
				inverseHitRates[i] = 0
			}
		}
		// Now sample up to 8 configs by weight
		for i := 0; i < 8 && floatsSum(inverseHitRates[:]) != 0; i++ {
			idxCur := pmfSample(inverseHitRates[:], proc.rnd)
			syscallConfigs[i] = idxCur
			inverseHitRates[idxCur] = 0
			presentCount--
			if presentCount == 0 {
				break
			}
		}
	}

	// Just a single configuration
	if doSyscallOnly != -1 {
		sysIdx := syscallToIdx[doSyscallOnly]
		sysArg := proc.rnd.Intn(syscallArgs[sysIdx])
		syscallConfigs[0] = syscallToFlat[sysIdx][sysArg]
		for i := 1; i < len(syscallConfigs); i++ {
			syscallConfigs[i] = -1
		}
	}

    if !useMultiTaint {
		for i := 1; i < len(syscallConfigs); i++ {
			syscallConfigs[i] = -1
		}
    }

	proc.logProgram(opts, p)

    if !useFlush {
        if enableKdfsan {
            log.Logf(0, "*** proc.executeRaw: Enabling Kdfsan... ***\n")
            if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c", "cat /sys/kernel/debug/kdfsan/enable"); err != nil {
                log.Logf(0, "Failed to enable Kdfsan: %v", err)
            }
            log.Logf(0, "*** proc.executeRaw: Kdfsan enabled ***\n")
        }
    }

	// Alper
	// Forward the config to kernel
	var configStr = ""
	for i := 0; i < 8; i++ {
		var sysCur uint16 = math.MaxUint16
		var argCur uint8 = math.MaxUint8
		if syscallConfigs[i] >= 0 {
			sysCur = uint16(flatToSys[syscallConfigs[i]])
			argCur = uint8(flatToArg[syscallConfigs[i]])
		}
		configStr += u16_to_hex(uint16(sysCur)) + " " + u8_to_hex(uint8(argCur)) + " "
	}
    if useFlush || enableKdfsan {
        if _, err := osutil.RunCmd(time.Minute, "", "bash", "-c",
            fmt.Sprintf("echo '%v' > /sys/kernel/debug/alper/syscall_config", configStr)); err != nil {
            log.Logf(0, "Failed commiting syscall config: %v", err)
        }
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

		// Read and clear the results file
        var data []byte
        if useFlush || enableKdfsan {
            var err2 error
            data, err2 = os.ReadFile("/sys/kernel/debug/alper/results")
            if err2 != nil {
                log.Logf(0, "Failed to read /sys/kernel/debug/alper/results: %v", err2)
            }
        }
        
        if useFlush {
            for i := 0; i < 16; i++ {
                _, err_flush := os.ReadFile("/sys/kernel/debug/alper/flush")
                if err_flush != nil {
                    log.Logf(0, "\033[38;2;0;150;255mFailed to flush Kdfsan: %v\033[0m", err_flush)
                }
            }
        }

		// Send taint log to manager before snapshot restore, if there was any taint
		if logResults {
			log.Logf(0, "\033[38;2;255;255;0m%v\033[0m\n", string(data))
		}
        if useFlush || enableKdfsan {
            myresult_count, errParse := strconv.ParseUint(string(data[151+2:151+2+8]), 16, 32)
            hitmask, errParse2 := strconv.ParseUint(string(data[127+2:127+2+2]), 16, 8)
            if myresult_count > 0 && errParse == nil && errParse2 == nil {
                proc.fuzzer.sendTaintToManager(rpctype.NewTaintResult{
                    SyscallConfigs: syscallConfigs,
                    HitMask:        uint8(hitmask),
                    SyscallResults: data,
                    InputProgram:   inputProgStr,
                    InputProgram2:  p.Serialize(),
                    MyLog:          mylogStr,
                })
            } else {
                // None of the taint values hit anything, count up to 8 attempts
                for i := 0; i < len(syscallConfigs); i++ {
                    if syscallConfigs[i] < 0 {
                        continue
                    }
                    attemptBuffer[syscallConfigs[i]]++
                }

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
        }

        // Possibly restore snapshot
        if !useFlush {
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
        }

		return info
	}
}

func (proc *Proc) logProgram(opts *ipc.ExecOpts, p *prog.Prog) {
	// Alper
	// Fake log to speed it up. The manager expects a log, so we provide a fake one so it's not killed
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
