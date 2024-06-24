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
	"github.com/google/syzkaller/pkg/rpctype"
	"github.com/google/syzkaller/pkg/signal"
	"github.com/google/syzkaller/prog"
)

// Proc represents a single fuzzing process (executor).
type Proc struct {
	fuzzer          *Fuzzer
	pid             int
	env             *ipc.Env
	rnd             *rand.Rand
	execOpts        *ipc.ExecOpts
	execOptsCollide *ipc.ExecOpts
	execOptsCover   *ipc.ExecOpts
	execOptsComps   *ipc.ExecOpts
}

func newProc(fuzzer *Fuzzer, pid int) (*Proc, error) {
	log.Logf(0, "newProc")
	env, err := ipc.MakeEnv(fuzzer.config, pid)
	if err != nil {
		return nil, err
	}
	seed := int64(123456)
	// seed := int64(time.Now().UnixNano() + int64(pid)*1e12)
	rnd := rand.New(rand.NewSource(seed))
	execOptsCollide := *fuzzer.execOpts
	execOptsCollide.Flags &= ^ipc.FlagCollectSignal
	execOptsCover := *fuzzer.execOpts
	execOptsCover.Flags |= ipc.FlagCollectCover
	execOptsComps := *fuzzer.execOpts
	execOptsComps.Flags |= ipc.FlagCollectComps
	proc := &Proc{
		fuzzer:          fuzzer,
		pid:             pid,
		env:             env,
		rnd:             rnd,
		execOpts:        fuzzer.execOpts,
		execOptsCollide: &execOptsCollide,
		execOptsCover:   &execOptsCover,
		execOptsComps:   &execOptsComps,
	}
	return proc, nil
}

func (proc *Proc) loop() {
	log.Logf(0, "[proc loop] fuzzer corpus size: %v", len(proc.fuzzer.corpus))
	totalCorpus := len(proc.fuzzer.corpus)
	for i := 0; i < totalCorpus; i++ {
		p := proc.fuzzer.corpus[i]

		progCoverHistory := make([][]uint32, 0)

		// use original Syzkaller arg mutation for 500 times
		for j := 0; j < 800; j++ {
			log.Logf(0, "prog %v, mutation index: %v", i, j)
			pe := p.Clone()

			progs := pe.Mutate(proc.rnd, prog.RecommendedCalls, proc.fuzzer.choiceTable, proc.fuzzer.noMutate, prog.Syzkaller)

			if len(progs) != 1 {
				panic("len(progs) != 1")
			}
			var mutatedAggregatedCover cover.Cover
			for idx, p := range progs {
				log.Logf(0, "prog %v, mutation index %v, mutated program %v: %v", i, j, idx, hash.String(p.Serialize()))
				currentCover, err := proc.executeAndCollectCoverage(p)
				if err != nil {
					log.Logf(0, "executeAndCollectCoverage error: %v", err)
					continue
				}
				mutatedAggregatedCover.Merge(currentCover)
			}
			log.Logf(0, "aggregated coverage for this mutation: %v", len(mutatedAggregatedCover))
			progCoverHistory = append(progCoverHistory, mutatedAggregatedCover.Serialize())
		}

		log.Logf(0, "len(progCoverHistory): %v", len(progCoverHistory))
		var aggCover cover.Cover
		coverCounter := make(map[int]int)
		useML := true
		for idx, cover := range progCoverHistory {
			aggCover.Merge(cover)

			// double check: collect the last 200 coverages
			if idx >= len(progCoverHistory)-200 {
				coverCounter[len(cover)]++
				if idx == len(progCoverHistory)-1 {
					continue
				}
				// if the current coverage is not the same as the next one, then we won't use the ML
				if len(cover) != len(progCoverHistory[idx+1]) {
					useML = false
				}
			}
		}

		log.Logf(0, "coverCounter: %v", coverCounter)
		var mutatedProgs []*prog.Prog
		if useML {
			pe := p.Clone()
			mutatedProgs = pe.Mutate(proc.rnd, prog.RecommendedCalls, proc.fuzzer.choiceTable, proc.fuzzer.noMutate, prog.ML)
		} else {
			pe := p.Clone()
			mutatedProgs = pe.Mutate(proc.rnd, prog.RecommendedCalls, proc.fuzzer.choiceTable, proc.fuzzer.noMutate, prog.SyzkallerModified)
		}
		var mutatedAggregatedCover cover.Cover
		log.Logf(0, "len(mutatedProgs): %v", len(mutatedProgs))
		for idx, p := range mutatedProgs {
			log.Logf(0, "[final mutation] prog %v, mutated program %v: %v", i, idx, hash.String(p.Serialize()))
			currentCover, err := proc.executeAndCollectCoverage(p)
			if err != nil {
				log.Logf(0, "executeAndCollectCoverage error: %v", err)
				continue
			}
			mutatedAggregatedCover.Merge(currentCover)
		}
		log.Logf(0, "[final mutation] aggregated mutated coverage for this mutation: %v", len(mutatedAggregatedCover))

		aggCover.Merge(mutatedAggregatedCover.Serialize())

		log.Logf(0, "coverage for current iteration: %v", len(aggCover))
		proc.fuzzer.sendCoverageToManager(aggCover.Serialize())
	}
}

func (proc *Proc) executeAndCollectCoverage(p *prog.Prog) ([]uint32, error) {
	log.Logf(0, "executeAndCollectCoverage: %v", hash.String(p.Serialize()))
	initial_info := proc.executeRaw(proc.execOpts, p, StatTriage)
	// log.Logf(0, "executeAndCollectCoverage: initial_info: %v", initial_info)
	if initial_info == nil {
		return []uint32{}, fmt.Errorf("initial_info is nil")
	}
	log.Logf(0, "executeAndCollectCoverage::executeRaw() is completed")
	calls, extra := proc.fuzzer.checkNewSignal(p, initial_info)

	log.Logf(0, "executeAndCollectCoverage: calls=%v, extra=%v", calls, extra)

	var progCover cover.Cover

	for _, callIndex := range calls {
		log.Logf(0, "executeAndCollectCoverage: callIndex=%v", callIndex)
		initial_info.Calls[callIndex].Signal = append([]uint32{}, initial_info.Calls[callIndex].Signal...)
		initial_info.Calls[callIndex].Cover = nil

		callName := p.Calls[callIndex].Meta.Name
		logCallName := fmt.Sprintf("call #%v %v", callIndex, callName)
		log.Logf(0, "executeAndCollectCoverage: %v", logCallName)

		callInfo := initial_info.Calls[callIndex]
		notexecuted := 0
		rawCover := []uint32{}
		var syscallCover cover.Cover

		for i := 0; i < 3; i++ {
			info := proc.executeRaw(proc.execOptsCover, p, StatTriage)

			if !reexecutionSuccess(info, &callInfo, callIndex) {
				log.Logf(0, "not executed success")
				notexecuted++
				if notexecuted > 3/2+1 {
					log.Logf(0, "[early return] not executed too many times: %v", notexecuted)
					return []uint32{}, fmt.Errorf("not executed too many times")
				}
				continue
			}

			_, thisCover := getSignalAndCover(p, info, callIndex)
			log.Logf(0, "[call %v] thisCover: %v", callIndex, len(thisCover))
			if len(rawCover) == 0 && proc.fuzzer.fetchRawCover {
				rawCover = append([]uint32{}, thisCover...)
			}
			syscallCover.Merge(thisCover)
		}

		progCover.Merge(syscallCover.Serialize())

	}

	if extra {
		panic("executeAndCollectCoverage: extra")
	}

	log.Logf(0, "executeAndCollectCoverage: progCover: %v", len(progCover.Serialize()))

	// proc.fuzzer.sendCoverageToManager(progCover.Serialize())
	return progCover.Serialize(), nil
}

func (proc *Proc) triageProg(p *prog.Prog) {
	log.Logf(0, "triageProg: %v", hash.String(p.Serialize()))
	info := proc.executeRaw(proc.execOpts, p, StatTriage)
	if info == nil {
		return
	}
	calls, extra := proc.fuzzer.checkNewSignal(p, info)

	log.Logf(0, "triageProg executeRaw info:")
	for i, callInfo := range info.Calls {
		log.Logf(0, "call %v: signal: %v", i, callInfo.Signal)
		log.Logf(0, "")
	}

	log.Logf(0, "triageProg: calls=%v, extra=%v", calls, extra)
	for _, callIndex := range calls {
		log.Logf(0, "triageProg: callIndex=%v", callIndex)
		info.Calls[callIndex].Signal = append([]uint32{}, info.Calls[callIndex].Signal...)
		info.Calls[callIndex].Cover = nil
		item := &WorkTriage{
			p:     p.Clone(),
			call:  callIndex,
			info:  info.Calls[callIndex],
			flags: ProgNormal,
		}
		proc.triageInput(item)
	}
	if extra {
		log.Logf(0, "triageProg: extra")
		info.Extra.Signal = append([]uint32{}, info.Extra.Signal...)
		info.Extra.Cover = nil
		item := &WorkTriage{
			p:     p.Clone(),
			call:  -1,
			info:  info.Extra,
			flags: ProgNormal,
		}
		proc.triageInput(item)
	}
}

func (proc *Proc) triageInput(item *WorkTriage) {
	log.Logf(1, "#%v: triaging type=%x", proc.pid, item.flags)

	prio := signalPrio(item.p, &item.info, item.call)
	inputSignal := signal.FromRaw(item.info.Signal, prio)
	log.Logf(0, "inputSignal: %v", inputSignal)
	newSignal := proc.fuzzer.corpusSignalDiff(inputSignal)
	log.Logf(0, "newSignal: %v", newSignal)
	if newSignal.Empty() {
		log.Logf(0, "[early return] newSignal is empty")
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
	rawCover := []uint32{}
	for i := 0; i < signalRuns; i++ {
		info := proc.executeRaw(proc.execOptsCover, item.p, StatTriage)

		if !reexecutionSuccess(info, &item.info, item.call) {
			log.Logf(0, "[early return] reexecution failed")
			// The call was not executed or failed.
			notexecuted++
			if notexecuted > signalRuns/2+1 {
				log.Logf(0, "[early return] not executed too many times: %v", notexecuted)
				return // if happens too often, give up
			}
			continue
		}

		for i, callInfo := range info.Calls {
			log.Logf(0, "call %v: cover %v", i, callInfo.Cover)
			log.Logf(0, "call %v: signal %v", i, callInfo.Cover)
		}

		thisSignal, thisCover := getSignalAndCover(item.p, info, item.call)
		log.Logf(0, "[call %v] thisSignal: %v", item.call, thisSignal)
		log.Logf(0, "[call %v] thisCover: %v", item.call, thisCover)
		if len(rawCover) == 0 && proc.fuzzer.fetchRawCover {
			rawCover = append([]uint32{}, thisCover...)
		}
		newSignal = newSignal.Intersection(thisSignal)
		log.Logf(0, "newSignal after Intersection: %v", newSignal)
		// Without !minimized check manager starts losing some considerable amount
		// of coverage after each restart. Mechanics of this are not completely clear.
		if newSignal.Empty() && item.flags&ProgMinimized == 0 {
			log.Logf(0, "newSignal.Empty(): %v", newSignal.Empty())
			log.Logf(0, "item.flags: %v", item.flags)
			log.Logf(0, "ProgMinimized: %v", ProgMinimized)
			log.Logf(0, "[early return] newSignal is empty and item.flags&ProgMinimized == 0")
			return
		}
		inputCover.Merge(thisCover)
	}
	log.Logf(0, "inputCover: %v", inputCover)
	log.Logf(0, "currentCoverage: %v", len(inputCover.Serialize()))
	// if item.flags&ProgMinimized == 0 {
	// 	item.p, item.call = prog.Minimize(item.p, item.call, false,
	// 		func(p1 *prog.Prog, call1 int) bool {
	// 			for i := 0; i < minimizeAttempts; i++ {
	// 				info := proc.execute(proc.execOpts, p1, ProgNormal, StatMinimize)
	// 				if !reexecutionSuccess(info, &item.info, call1) {
	// 					// The call was not executed or failed.
	// 					continue
	// 				}
	// 				thisSignal, _ := getSignalAndCover(p1, info, call1)
	// 				if newSignal.Intersection(thisSignal).Len() == newSignal.Len() {
	// 					return true
	// 				}
	// 			}
	// 			return false
	// 		})
	// }

	data := item.p.Serialize()
	// sig := hash.Hash(data)

	log.Logf(2, "added new input for %v to corpus:\n%s", logCallName, data)
	proc.fuzzer.sendInputToManager(rpctype.Input{
		Call:     callName,
		CallID:   item.call,
		Prog:     data,
		Signal:   inputSignal.Serialize(),
		Cover:    inputCover.Serialize(),
		RawCover: rawCover,
	})

	// proc.fuzzer.addInputToCorpus(item.p, inputSignal, sig)

	// if item.flags&ProgSmashed == 0 {
	// 	proc.fuzzer.workQueue.enqueue(&WorkSmash{item.p, item.call})
	// }
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
	if !checkProgProfiled(item.p) {
		log.Logf(0, "WONT SMASH: program not profiled: %v", hash.String(item.p.Serialize()))
		return // Don't smash unprofiled programs.
	}

	// fuzzerSnapshot := proc.fuzzer.snapshot()
	for i := 0; i < 100; i++ {
		p := item.p.Clone()
		log.Logf(0, "[BM] to be smashed program: %v", hash.String(p.Serialize()))
		p.Mutate(proc.rnd, prog.RecommendedCalls, proc.fuzzer.choiceTable, proc.fuzzer.noMutate, prog.Syzkaller)
		log.Logf(1, "#%v: smash mutated", proc.pid)
		proc.executeAndCollide(proc.execOpts, p, ProgNormal, StatSmash)
	}
}

func (proc *Proc) failCall(p *prog.Prog, call int) {
	for nth := 1; nth <= 100; nth++ {
		log.Logf(1, "#%v: injecting fault into call %v/%v", proc.pid, call, nth)
		newProg := p.Clone()
		newProg.Calls[call].Props.FailNth = nth
		info := proc.executeRaw(proc.execOpts, newProg, StatSmash)
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
	if info == nil {
		return nil
	}
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

func (proc *Proc) executeAndCollide(execOpts *ipc.ExecOpts, p *prog.Prog, flags ProgTypes, stat Stat) {
	proc.execute(execOpts, p, flags, stat)

	if proc.execOptsCollide.Flags&ipc.FlagThreaded == 0 {
		// We cannot collide syscalls without being in the threaded mode.
		return
	}
	const collideIterations = 2
	for i := 0; i < collideIterations; i++ {
		proc.executeRaw(proc.execOptsCollide, proc.randomCollide(p), StatCollide)
	}
}

func (proc *Proc) randomCollide(origP *prog.Prog) *prog.Prog {
	if proc.rnd.Intn(5) == 0 {
		// Old-style collide with a 20% probability.
		p, err := prog.DoubleExecCollide(origP, proc.rnd)
		if err == nil {
			return p
		}
	}
	if proc.rnd.Intn(4) == 0 {
		// Duplicate random calls with a 20% probability (25% * 80%).
		p, err := prog.DupCallCollide(origP, proc.rnd)
		if err == nil {
			return p
		}
	}
	p := prog.AssignRandomAsync(origP, proc.rnd)
	if proc.rnd.Intn(2) != 0 {
		prog.AssignRandomRerun(p, proc.rnd)
	}
	return p
}

func (proc *Proc) executeRaw(opts *ipc.ExecOpts, p *prog.Prog, stat Stat) *ipc.ProgInfo {
	log.Logf(0, "[executeRaw] opts: %v", opts)
	log.Logf(0, "prog: %v", hash.String(p.Serialize()))

	proc.fuzzer.checkDisabledCalls(p)

	// Limit concurrency window and do leak checking once in a while.
	ticket := proc.fuzzer.gate.Enter()
	defer proc.fuzzer.gate.Leave(ticket)

	proc.logProgram(opts, p)
	for try := 0; ; try++ {
		atomic.AddUint64(&proc.fuzzer.stats[stat], 1)
		output, info, hanged, err := proc.env.Exec(opts, p)
		if err != nil {
			if err == prog.ErrExecBufferTooSmall {
				// It's bad if we systematically fail to serialize programs,
				// but so far we don't have a better handling than counting this.
				// This error is observed a lot on the seeded syz_mount_image calls.
				atomic.AddUint64(&proc.fuzzer.stats[StatBufferTooSmall], 1)
				return nil
			}
			if try > 10 {
				log.SyzFatalf("executor %v failed %v times: %v", proc.pid, try, err)
			}
			log.Logf(4, "fuzzer detected executor failure='%v', retrying #%d", err, try+1)
			debug.FreeOSMemory()
			time.Sleep(time.Second)
			continue
		}
		log.Logf(2, "result hanged=%v: %s", hanged, output)
		return info
	}
}

func (proc *Proc) logProgram(opts *ipc.ExecOpts, p *prog.Prog) {
	if proc.fuzzer.outputType == OutputNone {
		return
	}

	data := p.Serialize()

	// The following output helps to understand what program crashed kernel.
	// It must not be intermixed.
	switch proc.fuzzer.outputType {
	case OutputStdout:
		now := time.Now()
		proc.fuzzer.logMu.Lock()
		fmt.Printf("%02v:%02v:%02v executing program %v:\n%s\n",
			now.Hour(), now.Minute(), now.Second(),
			proc.pid, data)
		proc.fuzzer.logMu.Unlock()
	case OutputDmesg:
		fd, err := syscall.Open("/dev/kmsg", syscall.O_WRONLY, 0)
		if err == nil {
			buf := new(bytes.Buffer)
			fmt.Fprintf(buf, "syzkaller: executing program %v:\n%s\n",
				proc.pid, data)
			syscall.Write(fd, buf.Bytes())
			syscall.Close(fd)
		}
	case OutputFile:
		f, err := os.Create(fmt.Sprintf("%v-%v.prog", proc.fuzzer.name, proc.pid))
		if err == nil {
			f.Write(data)
			f.Close()
		}
	default:
		log.SyzFatalf("unknown output type: %v", proc.fuzzer.outputType)
	}
}
