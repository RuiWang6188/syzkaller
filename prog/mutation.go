// Copyright 2015 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package prog

import (
	"encoding/binary"
	"encoding/csv"
	"fmt"
	"math"
	"math/rand"
	"os"
	"path"
	"path/filepath"
	"sort"
	"strconv"

	"github.com/google/syzkaller/pkg/hash"
	"github.com/google/syzkaller/pkg/image"
	"github.com/google/syzkaller/pkg/log"
)

type MLProgMutateInfo struct {
	ProgCallIndex int // the syscall index in the program
	CallIndex     int // the syscall index in the original label file without offset
	CallName      string
	ArgIndex      int // the argument index in the original label file without offset
	ArgName       string
	ArgType       string
	Mutated       bool
}

// Maximum length of generated binary blobs inserted into the program.
const maxBlobLen = uint64(100 << 10)

// Mutate program p.
//
// p:           The program to mutate.
// rs:          Random source.
// ncalls:      The allowed maximum calls in mutated program.
// ct:          ChoiceTable for syscalls.
// noMutate:    Set of IDs of syscalls which should not be mutated.
// corpus:      The entire corpus, including original program p.
func (p *Prog) Mutate(rs rand.Source, ncalls int, ct *ChoiceTable, noMutate map[int]bool, useML bool) []*Prog {
	log.Logf(0, "[Mutate] mutating program: %v", hash.String(p.Serialize()))
	r := newRand(p.Target, rs)
	if ncalls < len(p.Calls) {
		ncalls = len(p.Calls)
	}
	ctx := &mutator{
		p:        p,
		r:        r,
		ncalls:   ncalls,
		ct:       ct,
		noMutate: noMutate,
		corpus:   nil,
	}

	log.Logf(0, "start mutation loop for prog: %v", hash.String(p.Serialize()))

	// for stop, ok := false, false; !stop; stop = ok && len(p.Calls) != 0 && r.oneOf(3) {
	// 	switch {
	// 	case r.oneOf(5):
	// 		// Not all calls have anything squashable,
	// 		// so this has lower priority in reality.
	// 		ok = ctx.squashAny()
	// 	case r.nOutOf(1, 100):
	// 		ok = ctx.splice()
	// 	case r.nOutOf(20, 31):
	// 		ok = ctx.insertCall()
	// 	case r.nOutOf(10, 11):
	// 		ok = ctx.mutateArg()
	// 	default:
	// 		ok = ctx.removeCall()
	// 	}
	// }
	mutatedProgs := make([]*Prog, 0)
	for stop, ok := false, false; !stop; stop = ok && len(p.Calls) != 0 {
		if !useML {
			mutatedProgs, ok = ctx.mutateArgSyz()
		} else {
			mutatedProgs, ok = ctx.mutateArg()

		}
		log.Logf(0, "[Mutate] mutation success: %v", ok)
		log.Logf(0, "p.Calls len: %v", len(p.Calls))
	}

	for _, prog := range mutatedProgs {
		prog.sanitizeFix()
		prog.debugValidate()
		if got := len(prog.Calls); got < 1 || got > ncalls {
			panic(fmt.Sprintf("bad number of calls after mutation: %v, want [1, %v]", got, ncalls))
		}
	}

	log.Logf(0, "len(mutatedProgs): %v", len(mutatedProgs))

	return mutatedProgs
}

// Internal state required for performing mutations -- currently this matches
// the arguments passed to Mutate().
type mutator struct {
	p        *Prog        // The program to mutate.
	r        *randGen     // The randGen instance.
	ncalls   int          // The allowed maximum calls in mutated program.
	ct       *ChoiceTable // ChoiceTable for syscalls.
	noMutate map[int]bool // Set of IDs of syscalls which should not be mutated.
	corpus   []*Prog      // The entire corpus, including original program p.
}

// This function selects a random other program p0 out of the corpus, and
// mutates ctx.p as follows: preserve ctx.p's Calls up to a random index i
// (exclusive) concatenated with p0's calls from index i (inclusive).
func (ctx *mutator) splice() bool {
	p, r := ctx.p, ctx.r
	if len(ctx.corpus) == 0 || len(p.Calls) == 0 || len(p.Calls) >= ctx.ncalls {
		return false
	}
	p0 := ctx.corpus[r.Intn(len(ctx.corpus))]
	p0c := p0.Clone()
	idx := r.Intn(len(p.Calls))
	p.Calls = append(p.Calls[:idx], append(p0c.Calls, p.Calls[idx:]...)...)
	for i := len(p.Calls) - 1; i >= ctx.ncalls; i-- {
		p.RemoveCall(i)
	}
	return true
}

// Picks a random complex pointer and squashes its arguments into an ANY.
// Subsequently, if the ANY contains blobs, mutates a random blob.
func (ctx *mutator) squashAny() bool {
	p, r := ctx.p, ctx.r
	complexPtrs := p.complexPtrs()
	if len(complexPtrs) == 0 {
		return false
	}
	ptr := complexPtrs[r.Intn(len(complexPtrs))]
	if ctx.noMutate[ptr.call.Meta.ID] {
		return false
	}
	if !p.Target.isAnyPtr(ptr.arg.Type()) {
		p.Target.squashPtr(ptr.arg)
	}
	var blobs []*DataArg
	var bases []*PointerArg
	ForeachSubArg(ptr.arg, func(arg Arg, ctx *ArgCtx) {
		if data, ok := arg.(*DataArg); ok && arg.Dir() != DirOut {
			blobs = append(blobs, data)
			bases = append(bases, ctx.Base)
		}
	})
	if len(blobs) == 0 {
		return false
	}
	// Note: we need to call analyze before we mutate the blob.
	// After mutation the blob can grow out of bounds of the data area
	// and analyze will crash with out-of-bounds access while marking existing allocations.
	s := analyze(ctx.ct, ctx.corpus, p, ptr.call)
	// TODO(dvyukov): we probably want special mutation for ANY.
	// E.g. merging adjacent ANYBLOBs (we don't create them,
	// but they can appear in future); or replacing ANYRES
	// with a blob (and merging it with adjacent blobs).
	idx := r.Intn(len(blobs))
	arg := blobs[idx]
	base := bases[idx]
	baseSize := base.Res.Size()
	arg.data = mutateData(r, arg.Data(), 0, maxBlobLen)
	// Update base pointer if size has increased.
	if baseSize < base.Res.Size() {
		newArg := r.allocAddr(s, base.Type(), base.Dir(), base.Res.Size(), base.Res)
		*base = *newArg
	}
	return true
}

// Inserts a new call at a randomly chosen point (with bias towards the end of
// existing program). Does not insert a call if program already has ncalls.
func (ctx *mutator) insertCall() bool {
	p, r := ctx.p, ctx.r
	if len(p.Calls) >= ctx.ncalls {
		return false
	}
	idx := r.biasedRand(len(p.Calls)+1, 5)
	var c *Call
	if idx < len(p.Calls) {
		c = p.Calls[idx]
	}
	s := analyze(ctx.ct, ctx.corpus, p, c)
	calls := r.generateCall(s, p, idx)
	p.insertBefore(c, calls)
	for len(p.Calls) > ctx.ncalls {
		p.RemoveCall(idx)
	}
	return true
}

// Removes a random call from program.
func (ctx *mutator) removeCall() bool {
	p, r := ctx.p, ctx.r
	if len(p.Calls) == 0 {
		return false
	}
	idx := r.Intn(len(p.Calls))
	p.RemoveCall(idx)
	return true
}

func collectSubdirectories(dir string) ([]string, error) {
	var subdirs []string
	err := filepath.Walk(dir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		if info.IsDir() && path != dir {
			subdirs = append(subdirs, path)
		}

		return nil
	})
	return subdirs, err
}

func readCSVMutated(filePath string) (MLProgMutateInfo, error) {
	// Step 1: Open the CSV file
	file, err := os.Open(filePath)
	if err != nil {
		return MLProgMutateInfo{}, fmt.Errorf("could not open file %s: %v", filePath, err)
	}
	defer file.Close()

	// Step 2: Create a CSV reader
	reader := csv.NewReader(file)

	// Step 3: Read all records from the CSV file
	records, err := reader.ReadAll()
	if err != nil {
		return MLProgMutateInfo{}, fmt.Errorf("could not read CSV file: %v", err)
	}

	// Step 4: Find the record with 'mutated' label marked as true
	if len(records) < 2 {
		return MLProgMutateInfo{}, fmt.Errorf("number of records is less than 1")
	}

	offset, err := strconv.Atoi(records[1][0])
	if err != nil {
		return MLProgMutateInfo{}, fmt.Errorf("could not convert offset to int: %v", err)
	}

	progCallIdx := -1
	prevCallIdx := -1
	prevSyscallName := ""
	for _, record := range records[1:] {
		if record[2] == "0" {
			progCallIdx += 1
			prevCallIdx, err = strconv.Atoi(record[0])
			if err != nil {
				return MLProgMutateInfo{}, fmt.Errorf("could not convert call index to int: %v", err)
			}
			prevCallIdx -= offset
			prevSyscallName = record[1]
		}

		if record[3] == "true" {
			index, err := strconv.Atoi(record[0])
			if err != nil {
				return MLProgMutateInfo{}, fmt.Errorf("could not convert index to int: %v", err)
			}
			return MLProgMutateInfo{
				ProgCallIndex: progCallIdx,
				CallIndex:     prevCallIdx,
				CallName:      prevSyscallName,
				ArgIndex:      index - offset,
				ArgName:       record[1],
				ArgType:       record[2],
				Mutated:       true,
			}, nil
		}

	}
	return MLProgMutateInfo{}, fmt.Errorf("no record found")
}

func loadMLMutationDataset(csvFilePath string) (MLProgMutateInfo, error) {
	// read the prog node label csv file and find the record with mutated label
	modelOutput, err := readCSVMutated(csvFilePath)
	if err != nil {
		return MLProgMutateInfo{}, err
	}
	return modelOutput, nil
}

func getModelOutput(p *Prog, r *randGen) (MLProgMutateInfo, error) {
	// 1. find the corresponding base prog dir in the corpus
	// TODO (Rui): make this configurable
	modelOutputDir := "/root/1000"
	progHash := hash.String(p.Serialize())
	log.Logf(0, "prog hash: %v", progHash)
	progHashDir := path.Join(modelOutputDir, progHash)
	log.Logf(0, "progHashDir: %v", progHashDir)

	// check if progHashDir exists
	if _, err := os.Stat(progHashDir); os.IsNotExist(err) {
		log.Logf(0, "progHashDir doesn't exist: %v", progHashDir)
		return MLProgMutateInfo{}, fmt.Errorf("prog hash directory does not exist: %s", progHashDir)
	}

	log.Logf(0, "progHashDir exists: %v", progHashDir)

	// 2. choose a random mutation under the progHashDir
	subdirs, err := collectSubdirectories(progHashDir)
	if err != nil {
		panic(err)
	}
	if len(subdirs) == 0 {
		return MLProgMutateInfo{}, fmt.Errorf("no mutation subdirectories found in %s", subdirs)
	}

	selectedMutation := subdirs[r.Intn(len(subdirs))]

	log.Logf(0, "selectedMutation: %v", selectedMutation)

	// 3. load the csv file from the selected mutation
	csvFilePath := path.Join(selectedMutation, "prog.node.label.csv")
	if _, err := os.Stat(csvFilePath); os.IsNotExist(err) {
		return MLProgMutateInfo{}, fmt.Errorf("no csv file found in %s", csvFilePath)
	}

	return loadMLMutationDataset(csvFilePath)
}

func findArg(p *Prog, modelOutput MLProgMutateInfo) (Arg, ArgCtx) {
	nodeType := modelOutput.ArgType
	argIndex := modelOutput.ArgIndex
	callIndex := modelOutput.CallIndex
	progCallIndex := modelOutput.ProgCallIndex

	if nodeType != "1" {
		panic("ML model mutated node is not an argument node")
	}

	if progCallIndex < 0 || progCallIndex >= len(p.Calls) {
		panic("progCallIndex is out of bounds")
	}

	c := p.Calls[progCallIndex]

	log.Logf(0, "syscall name: %v", c.Meta.Name)

	ma := &mutationArgs{target: p.Target}
	ForeachArgNonstop(c, ma.collectArgNonstop)
	if len(ma.args) == 0 {
		panic("no args found in mutation args")
	}

	argIdxOffset := argIndex - callIndex - 1

	log.Logf(0, "mutate call index: %v", progCallIndex)
	log.Logf(0, "mutate call: %v", c.Meta.Name)

	log.Logf(0, "mutate arg index : %v", argIdxOffset)
	log.Logf(0, "chosen arg: %v", ma.args[argIdxOffset].arg.Type().Name())
	// log.Logf(0, "argIndex: %v", argIndex)
	// log.Logf(0, "callIndex: %v", callIndex)
	// log.Logf(0, "len(ma.args): %v", len(ma.args))

	if argIdxOffset < 0 || argIdxOffset >= len(ma.args) {
		panic("argIdxOffset is out of bound")
	}

	maArgType := "unknown"
	switch ma.args[argIdxOffset].arg.(type) {
	case *ConstArg:
		maArgType = "constant"
	case *PointerArg:
		maArgType = "pointer"
	case *DataArg:
		maArgType = "data"
	case *GroupArg:
		maArgType = "group"
	case *UnionArg:
		maArgType = "union"
	case *ResultArg:
		maArgType = "resource"
	default:
		panic("arg type is not support")
	}

	log.Logf(0, "ma arg type: %v", maArgType)
	log.Logf(0, "arg name from model: %v", modelOutput.ArgName)

	if maArgType != modelOutput.ArgName {
		panic("arg type from model does not match with the arg type in the program")
	}

	return ma.args[argIdxOffset].arg, ma.args[argIdxOffset].ctx
}

func (ctx *mutator) mutateArgSyz() ([]*Prog, bool) {
	log.Logf(0, "mutateArgSyz()")
	p, r := ctx.p, ctx.r
	if len(p.Calls) == 0 {
		return nil, false
	}

	idx := chooseCall(p, r)
	if idx < 0 {
		return nil, false
	}
	c := p.Calls[idx]
	if ctx.noMutate[c.Meta.ID] {
		return nil, false
	}
	mutatedProgs := make([]*Prog, 0)
	log.Logf(0, "mutate call index: %v", idx)
	log.Logf(0, "mutate call: %v", c.Meta.Name)
	updateSizes := true
	for stop, ok := false, false; !stop; stop = ok && r.oneOf(3) {
		mutatedProgs = make([]*Prog, 0)
		ok = true
		ma := &mutationArgs{target: p.Target}
		ForeachArg(c, ma.collectArg)
		if len(ma.args) == 0 {
			return nil, false
		}
		s := analyze(ctx.ct, ctx.corpus, p, c)
		arg, argCtx := ma.chooseArg(r.Rand)
		calls, ok1 := p.Target.mutateArg(r, s, arg, argCtx, &updateSizes)
		if !ok1 {
			ok = false
			continue
		}
		p.insertBefore(c, calls)
		idx += len(calls)
		for len(p.Calls) > ctx.ncalls {
			idx--
			p.RemoveCall(idx)
		}
		if idx < 0 || idx >= len(p.Calls) || p.Calls[idx] != c {
			panic(fmt.Sprintf("wrong call index: idx=%v calls=%v p.Calls=%v ncalls=%v",
				idx, len(calls), len(p.Calls), ctx.ncalls))
		}
		if updateSizes {
			p.Target.assignSizesCall(c)
		}
		mutatedProgs = append(mutatedProgs, p.Clone())
	}
	return mutatedProgs, true
}

// Mutate an argument of a random call.
func (ctx *mutator) mutateArg() ([]*Prog, bool) {
	log.Logf(0, "mutateArg()")
	p, r := ctx.p, ctx.r
	if len(p.Calls) == 0 {
		return nil, false
	}
	p_origin := p.Clone()

	log.Logf(0, "p.Calls:")
	for i, call := range p.Calls {
		log.Logf(0, "call %v: %v", i, call)
	}

	modelOutput, err := getModelOutput(p, r)
	if err != nil {
		fmt.Println("get model output failed: ", err)
		return nil, false
	}

	log.Logf(0, "p.Calls after after getModelOutput():")
	for i, call := range p.Calls {
		log.Logf(0, "call %v: %v", i, call)
	}

	callIdx := modelOutput.ProgCallIndex

	if callIdx < 0 {
		return nil, false
	}

	log.Logf(0, "callIdx: %v", callIdx)

	log.Logf(0, "p.Calls after after analyze():")
	for i, call := range p.Calls {
		log.Logf(0, "call %v: %v", i, call)
	}

	arg, argCtx := findArg(p, modelOutput)
	// arg, argCtx := ma.chooseArg(r.Rand)

	log.Logf(0, "p.Calls after after findArg():")
	for i, call := range p.Calls {
		log.Logf(0, "call %v: %v", i, call)
	}

	mutatedProgs := make([]*Prog, 0)

	// mutate arg for N times for a given selected arg
	for i := 0; i < 50; i++ {
		log.Logf(0, "mutateArg index: %v", i)

		idx := callIdx
		cp := p_origin.Clone()

		cp_c := cp.Calls[idx]

		if ctx.noMutate[cp_c.Meta.ID] {
			log.Logf(0, "no mutate syscall")
			return nil, false
		}
		updateSizes := true

		s := analyze(ctx.ct, ctx.corpus, cp, cp_c)

		calls, ok := cp.Target.mutateArg(r, s, arg, argCtx, &updateSizes)

		if !ok {
			log.Logf(0, "Target.mutateArg failed")
			continue
		}
		cp.insertBefore(cp_c, calls)

		idx += len(calls)
		for len(cp.Calls) > ctx.ncalls {
			idx--
			cp.RemoveCall(idx)
		}

		if idx < 0 || idx >= len(cp.Calls) || cp.Calls[idx] != cp_c {
			panic(fmt.Sprintf("wrong call index: idx=%v calls=%v cp.Calls=%v ncalls=%v",
				idx, len(calls), len(cp.Calls), ctx.ncalls))
		}
		if updateSizes {
			cp.Target.assignSizesCall(cp_c)
		}

		mutatedProgs = append(mutatedProgs, cp)
	}

	return mutatedProgs, true
}

// Select a call based on the complexity of the arguments.
func chooseCall(p *Prog, r *randGen) int {
	var prioSum float64
	var callPriorities []float64
	for _, c := range p.Calls {
		var totalPrio float64
		ForeachArg(c, func(arg Arg, ctx *ArgCtx) {
			prio, stopRecursion := arg.Type().getMutationPrio(p.Target, arg, false)
			totalPrio += prio
			ctx.Stop = stopRecursion
		})
		prioSum += totalPrio
		callPriorities = append(callPriorities, prioSum)
	}
	if prioSum == 0 {
		return -1 // All calls are without arguments.
	}
	return sort.SearchFloat64s(callPriorities, prioSum*r.Float64())
}

func (target *Target) mutateArg(r *randGen, s *state, arg Arg, ctx ArgCtx, updateSizes *bool) ([]*Call, bool) {
	// seed := int64(12345)
	// src := rand.NewSource(seed)
	// r := newRand(target, src)
	var baseSize uint64
	if ctx.Base != nil {
		baseSize = ctx.Base.Res.Size()
	}
	calls, retry, preserve := arg.Type().mutate(r, s, arg, ctx)
	if retry {
		return nil, false
	}
	if preserve {
		*updateSizes = false
	}
	// Update base pointer if size has increased.
	if base := ctx.Base; base != nil && baseSize < base.Res.Size() {
		newArg := r.allocAddr(s, base.Type(), base.Dir(), base.Res.Size(), base.Res)
		replaceArg(base, newArg)
	}
	return calls, true
}

func regenerate(r *randGen, s *state, arg Arg) (calls []*Call, retry, preserve bool) {
	var newArg Arg
	newArg, calls = r.generateArg(s, arg.Type(), arg.Dir())
	replaceArg(arg, newArg)
	return
}

func mutateInt(r *randGen, a *ConstArg, t *IntType) uint64 {
	switch {
	case r.nOutOf(1, 3):
		return a.Val + (uint64(r.Intn(4)) + 1)
	case r.nOutOf(1, 2):
		return a.Val - (uint64(r.Intn(4)) + 1)
	default:
		return a.Val ^ (1 << uint64(r.Intn(int(t.TypeBitSize()))))
	}
}

func mutateAlignedInt(r *randGen, a *ConstArg, t *IntType) uint64 {
	rangeEnd := t.RangeEnd
	if t.RangeBegin == 0 && int64(rangeEnd) == -1 {
		// Special [0:-1] range for all possible values.
		rangeEnd = uint64(1<<t.TypeBitSize() - 1)
	}
	index := (a.Val - t.RangeBegin) / t.Align
	misalignment := (a.Val - t.RangeBegin) % t.Align
	switch {
	case r.nOutOf(1, 3):
		index += uint64(r.Intn(4)) + 1
	case r.nOutOf(1, 2):
		index -= uint64(r.Intn(4)) + 1
	default:
		index ^= 1 << uint64(r.Intn(int(t.TypeBitSize())))
	}
	lastIndex := (rangeEnd - t.RangeBegin) / t.Align
	index %= lastIndex + 1
	return t.RangeBegin + index*t.Align + misalignment
}

func (t *IntType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	if r.bin() {
		return regenerate(r, s, arg)
	}
	a := arg.(*ConstArg)
	if t.Align == 0 {
		a.Val = mutateInt(r, a, t)
	} else {
		a.Val = mutateAlignedInt(r, a, t)
	}
	a.Val = truncateToBitSize(a.Val, t.TypeBitSize())
	return
}

func (t *FlagsType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	a := arg.(*ConstArg)
	for oldVal := a.Val; oldVal == a.Val; {
		a.Val = r.flags(t.Vals, t.BitMask, a.Val)
	}
	return
}

func (t *LenType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	if !r.mutateSize(arg.(*ConstArg), *ctx.Parent, ctx.Fields) {
		retry = true
		return
	}
	preserve = true
	return
}

func (t *ResourceType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	return regenerate(r, s, arg)
}

func (t *VmaType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	return regenerate(r, s, arg)
}

func (t *ProcType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	return regenerate(r, s, arg)
}

func (t *BufferType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	minLen, maxLen := uint64(0), maxBlobLen
	if t.Kind == BufferBlobRange {
		minLen, maxLen = t.RangeBegin, t.RangeEnd
	}
	a := arg.(*DataArg)
	if a.Dir() == DirOut {
		if t.Kind == BufferFilename && r.oneOf(100) {
			a.size = uint64(r.randFilenameLength())
		} else {
			mutateBufferSize(r, a, minLen, maxLen)
		}
		return
	}
	switch t.Kind {
	case BufferBlobRand, BufferBlobRange:
		data := append([]byte{}, a.Data()...)
		a.data = mutateData(r, data, minLen, maxLen)
	case BufferString:
		if len(t.Values) != 0 {
			a.data = r.randString(s, t)
		} else {
			if t.TypeSize != 0 {
				minLen, maxLen = t.TypeSize, t.TypeSize
			}
			data := append([]byte{}, a.Data()...)
			a.data = mutateData(r, data, minLen, maxLen)
		}
	case BufferFilename:
		a.data = []byte(r.filename(s, t))
	case BufferGlob:
		if len(t.Values) != 0 {
			a.data = r.randString(s, t)
		} else {
			a.data = []byte(r.filename(s, t))
		}
	case BufferText:
		data := append([]byte{}, a.Data()...)
		a.data = r.mutateText(t.Text, data)
	case BufferCompressed:
		a.data, retry = r.mutateImage(a.Data())
	default:
		panic("unknown buffer kind")
	}
	return
}

func (r *randGen) mutateImage(compressed []byte) (data []byte, retry bool) {
	data, dtor := image.MustDecompress(compressed)
	defer dtor()
	if len(data) == 0 {
		return compressed, true // Do not mutate empty data.
	}
	hm := MakeGenericHeatmap(data, r.Rand)
	for i := hm.NumMutations(); i > 0; i-- {
		index := hm.ChooseLocation()
		width := 1 << uint(r.Intn(4))
		if index+width > len(data) {
			width = 1
		}
		storeInt(data[index:], r.randInt(uint64(width*8)), width)
	}
	return image.Compress(data), false
}

func mutateBufferSize(r *randGen, arg *DataArg, minLen, maxLen uint64) {
	for oldSize := arg.Size(); oldSize == arg.Size(); {
		arg.size += uint64(r.Intn(33)) - 16
		// Cast to int64 to prevent underflows.
		if int64(arg.size) < int64(minLen) {
			arg.size = minLen
		}
		if arg.size > maxLen {
			arg.size = maxLen
		}
	}
}

func (t *ArrayType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	// TODO: swap elements of the array
	a := arg.(*GroupArg)
	count := uint64(0)
	switch t.Kind {
	case ArrayRandLen:
		if r.bin() {
			for count = uint64(len(a.Inner)); r.bin(); {
				count++
			}
		} else {
			for count == uint64(len(a.Inner)) {
				count = r.randArrayLen()
			}
		}
	case ArrayRangeLen:
		if t.RangeBegin == t.RangeEnd {
			panic("trying to mutate fixed length array")
		}
		for count == uint64(len(a.Inner)) {
			count = r.randRange(t.RangeBegin, t.RangeEnd)
		}
	}
	if count > uint64(len(a.Inner)) {
		for count > uint64(len(a.Inner)) {
			newArg, newCalls := r.generateArg(s, t.Elem, a.Dir())
			a.Inner = append(a.Inner, newArg)
			calls = append(calls, newCalls...)
			for _, c := range newCalls {
				s.analyze(c)
			}
		}
	} else if count < uint64(len(a.Inner)) {
		for _, arg := range a.Inner[count:] {
			removeArg(arg)
		}
		a.Inner = a.Inner[:count]
	}
	return
}

func (t *PtrType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	a := arg.(*PointerArg)
	if r.oneOf(1000) {
		removeArg(a.Res)
		index := r.rand(len(r.target.SpecialPointers))
		newArg := MakeSpecialPointerArg(t, a.Dir(), index)
		replaceArg(arg, newArg)
		return
	}
	newArg := r.allocAddr(s, t, a.Dir(), a.Res.Size(), a.Res)
	replaceArg(arg, newArg)
	return
}

func (t *StructType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	gen := r.target.SpecialTypes[t.Name()]
	if gen == nil {
		panic("bad arg returned by mutationArgs: StructType")
	}
	var newArg Arg
	newArg, calls = gen(&Gen{r, s}, t, arg.Dir(), arg)
	a := arg.(*GroupArg)
	for i, f := range newArg.(*GroupArg).Inner {
		replaceArg(a.Inner[i], f)
	}
	return
}

func (t *UnionType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	if gen := r.target.SpecialTypes[t.Name()]; gen != nil {
		var newArg Arg
		newArg, calls = gen(&Gen{r, s}, t, arg.Dir(), arg)
		replaceArg(arg, newArg)
		return
	}
	a := arg.(*UnionArg)
	index := r.Intn(len(t.Fields) - 1)
	if index >= a.Index {
		index++
	}
	optType, optDir := t.Fields[index].Type, t.Fields[index].Dir(a.Dir())
	removeArg(a.Option)
	var newOpt Arg
	newOpt, calls = r.generateArg(s, optType, optDir)
	replaceArg(arg, MakeUnionArg(t, a.Dir(), newOpt, index))
	return
}

func (t *CsumType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	panic("CsumType can't be mutated")
}

func (t *ConstType) mutate(r *randGen, s *state, arg Arg, ctx ArgCtx) (calls []*Call, retry, preserve bool) {
	panic("ConstType can't be mutated")
}

type mutationArgs struct {
	target        *Target
	ignoreSpecial bool
	prioSum       float64
	args          []mutationArg
	argsBuffer    [16]mutationArg
}

type mutationArg struct {
	arg      Arg
	ctx      ArgCtx
	priority float64
}

const (
	maxPriority = float64(10)
	minPriority = float64(1)
	dontMutate  = float64(0)
)

func (ma *mutationArgs) collectArgNonstop(arg Arg, ctx *ArgCtx) {
	ignoreSpecial := ma.ignoreSpecial
	ma.ignoreSpecial = false

	typ := arg.Type()
	prio, stopRecursion := typ.getMutationPrio(ma.target, arg, ignoreSpecial)
	ctx.Stop = stopRecursion

	// if prio == dontMutate {
	// 	log.Logf(0, "don't mutate arg: %v", arg.Type().Name())
	// 	return
	// }

	// _, isArrayTyp := typ.(*ArrayType)
	// _, isBufferTyp := typ.(*BufferType)
	// if !isBufferTyp && !isArrayTyp && arg.Dir() == DirOut || !typ.Varlen() && typ.Size() == 0 {
	// 	log.Logf(0, "return early")
	// 	return
	// }

	if len(ma.args) == 0 {
		ma.args = ma.argsBuffer[:0]
	}
	ma.prioSum += prio
	ma.args = append(ma.args, mutationArg{arg, *ctx, ma.prioSum})
}

// TOOD (Rui): check the early termination
func (ma *mutationArgs) collectArg(arg Arg, ctx *ArgCtx) {
	ignoreSpecial := ma.ignoreSpecial
	ma.ignoreSpecial = false

	typ := arg.Type()
	prio, stopRecursion := typ.getMutationPrio(ma.target, arg, ignoreSpecial)
	ctx.Stop = stopRecursion

	if prio == dontMutate {
		log.Logf(0, "don't mutate arg: %v", arg.Type().Name())
		return
	}

	_, isArrayTyp := typ.(*ArrayType)
	_, isBufferTyp := typ.(*BufferType)
	if !isBufferTyp && !isArrayTyp && arg.Dir() == DirOut || !typ.Varlen() && typ.Size() == 0 {
		log.Logf(0, "return early")
		return
	}

	if len(ma.args) == 0 {
		ma.args = ma.argsBuffer[:0]
	}
	ma.prioSum += prio
	ma.args = append(ma.args, mutationArg{arg, *ctx, ma.prioSum})
}

func (ma *mutationArgs) chooseArg(r *rand.Rand) (Arg, ArgCtx) {
	goal := ma.prioSum * r.Float64()
	chosenIdx := sort.Search(len(ma.args), func(i int) bool { return ma.args[i].priority >= goal })
	arg := ma.args[chosenIdx]

	log.Logf(0, "goal: %v, chosenIdx: %v, prioSum: %v", goal, chosenIdx, ma.prioSum)
	log.Logf(0, "chosen arg: %v", arg.arg.Type().Name())
	return arg.arg, arg.ctx
}

// TODO: find a way to estimate optimal priority values.
// Assign a priority for each type. The boolean is the reference type and it has
// the minimum priority, since it has only two possible values.
func (t *IntType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	// For a integer without a range of values, the priority is based on
	// the number of bits occupied by the underlying type.
	plainPrio := math.Log2(float64(t.TypeBitSize())) + 0.1*maxPriority
	if t.Kind != IntRange {
		return plainPrio, false
	}

	size := t.RangeEnd - t.RangeBegin + 1
	if t.Align != 0 {
		if t.RangeBegin == 0 && int64(t.RangeEnd) == -1 {
			// Special [0:-1] range for all possible values.
			size = (1<<t.TypeBitSize()-1)/t.Align + 1
		} else {
			size = (t.RangeEnd-t.RangeBegin)/t.Align + 1
		}
	}
	switch {
	case size <= 15:
		// For a small range, we assume that it is effectively
		// similar with FlagsType and we need to try all possible values.
		prio = rangeSizePrio(size)
	case size <= 256:
		// We consider that a relevant range has at most 256
		// values (the number of values that can be represented on a byte).
		prio = maxPriority
	default:
		// Ranges larger than 256 are equivalent with a plain integer.
		prio = plainPrio
	}
	return prio, false
}

func (t *StructType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	if target.SpecialTypes[t.Name()] == nil || ignoreSpecial {
		return dontMutate, false
	}
	return maxPriority, true
}

func (t *UnionType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	if target.SpecialTypes[t.Name()] == nil && len(t.Fields) == 1 || ignoreSpecial {
		return dontMutate, false
	}
	// For a non-special type union with more than one option
	// we mutate the union itself and also the value of the current option.
	if target.SpecialTypes[t.Name()] == nil {
		return maxPriority, false
	}
	return maxPriority, true
}

func (t *FlagsType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	prio = rangeSizePrio(uint64(len(t.Vals)))
	if t.BitMask {
		// We want a higher priority because the mutation will include
		// more possible operations (bitwise operations).
		prio += 0.1 * maxPriority
	}
	return prio, false
}

// Assigns a priority based on the range size.
func rangeSizePrio(size uint64) (prio float64) {
	switch size {
	case 0:
		prio = dontMutate
	case 1:
		prio = minPriority
	default:
		// Priority proportional with the number of values. After a threshold, the priority is constant.
		// The threshold is 15 because most of the calls have <= 15 possible values for a flag.
		prio = math.Min(float64(size)/3+0.4*maxPriority, 0.9*maxPriority)
	}
	return prio
}

func (t *PtrType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	if arg.(*PointerArg).IsSpecial() {
		// TODO: we ought to mutate this, but we don't have code for this yet.
		return dontMutate, false
	}
	return 0.3 * maxPriority, false
}

func (t *ConstType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	return dontMutate, false
}

func (t *CsumType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	return dontMutate, false
}

func (t *ProcType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	return 0.5 * maxPriority, false
}

func (t *ResourceType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	return 0.5 * maxPriority, false
}

func (t *VmaType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	return 0.5 * maxPriority, false
}

func (t *LenType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	// Mutating LenType only produces "incorrect" results according to descriptions.
	return 0.1 * maxPriority, false
}

func (t *BufferType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	if arg.Dir() == DirOut && !t.Varlen() {
		return dontMutate, false
	}
	if t.Kind == BufferString && len(t.Values) == 1 {
		// These are effectively consts (and frequently file names).
		return dontMutate, false
	}
	if t.Kind == BufferCompressed {
		// Prioritise mutation of compressed buffers, e.g. disk images (`compressed_image`).
		return maxPriority, false
	}
	return 0.8 * maxPriority, false
}

func (t *ArrayType) getMutationPrio(target *Target, arg Arg, ignoreSpecial bool) (prio float64, stopRecursion bool) {
	if t.Kind == ArrayRangeLen && t.RangeBegin == t.RangeEnd {
		return dontMutate, false
	}
	return maxPriority, false
}

func mutateData(r *randGen, data []byte, minLen, maxLen uint64) []byte {
	for stop := false; !stop; stop = stop && r.oneOf(3) {
		f := mutateDataFuncs[r.Intn(len(mutateDataFuncs))]
		data, stop = f(r, data, minLen, maxLen)
	}
	return data
}

// The maximum delta for integer mutations.
const maxDelta = 35

var mutateDataFuncs = [...]func(r *randGen, data []byte, minLen, maxLen uint64) ([]byte, bool){
	// TODO(dvyukov): duplicate part of data.
	// Flip bit in byte.
	func(r *randGen, data []byte, minLen, maxLen uint64) ([]byte, bool) {
		if len(data) == 0 {
			return data, false
		}
		byt := r.Intn(len(data))
		bit := r.Intn(8)
		data[byt] ^= 1 << uint(bit)
		return data, true
	},
	// Insert random bytes.
	func(r *randGen, data []byte, minLen, maxLen uint64) ([]byte, bool) {
		if len(data) == 0 || uint64(len(data)) >= maxLen {
			return data, false
		}
		n := r.Intn(16) + 1
		if r := int(maxLen) - len(data); n > r {
			n = r
		}
		pos := r.Intn(len(data))
		for i := 0; i < n; i++ {
			data = append(data, 0)
		}
		copy(data[pos+n:], data[pos:])
		for i := 0; i < n; i++ {
			data[pos+i] = byte(r.Int31())
		}
		if uint64(len(data)) > maxLen || r.bin() {
			data = data[:len(data)-n] // preserve original length
		}
		return data, true
	},
	// Remove bytes.
	func(r *randGen, data []byte, minLen, maxLen uint64) ([]byte, bool) {
		if len(data) == 0 {
			return data, false
		}
		n := r.Intn(16) + 1
		if n > len(data) {
			n = len(data)
		}
		pos := 0
		if n < len(data) {
			pos = r.Intn(len(data) - n)
		}
		copy(data[pos:], data[pos+n:])
		data = data[:len(data)-n]
		if uint64(len(data)) < minLen || r.bin() {
			for i := 0; i < n; i++ {
				data = append(data, 0) // preserve original length
			}
		}
		return data, true
	},
	// Append a bunch of bytes.
	func(r *randGen, data []byte, minLen, maxLen uint64) ([]byte, bool) {
		if uint64(len(data)) >= maxLen {
			return data, false
		}
		const max = 256
		n := max - r.biasedRand(max, 10)
		if r := int(maxLen) - len(data); n > r {
			n = r
		}
		for i := 0; i < n; i++ {
			data = append(data, byte(r.rand(256)))
		}
		return data, true
	},
	// Replace int8/int16/int32/int64 with a random value.
	func(r *randGen, data []byte, minLen, maxLen uint64) ([]byte, bool) {
		width := 1 << uint(r.Intn(4))
		if len(data) < width {
			return data, false
		}
		i := r.Intn(len(data) - width + 1)
		storeInt(data[i:], r.Uint64(), width)
		return data, true
	},
	// Add/subtract from an int8/int16/int32/int64.
	func(r *randGen, data []byte, minLen, maxLen uint64) ([]byte, bool) {
		width := 1 << uint(r.Intn(4))
		if len(data) < width {
			return data, false
		}
		i := r.Intn(len(data) - width + 1)
		v := loadInt(data[i:], width)
		delta := r.rand(2*maxDelta+1) - maxDelta
		if delta == 0 {
			delta = 1
		}
		if r.oneOf(10) {
			v = swapInt(v, width)
			v += delta
			v = swapInt(v, width)
		} else {
			v += delta
		}
		storeInt(data[i:], v, width)
		return data, true
	},
	// Set int8/int16/int32/int64 to an interesting value.
	func(r *randGen, data []byte, minLen, maxLen uint64) ([]byte, bool) {
		width := 1 << uint(r.Intn(4))
		if len(data) < width {
			return data, false
		}
		i := r.Intn(len(data) - width + 1)
		value := r.randInt64()
		if r.oneOf(10) {
			value = swap64(value)
		}
		storeInt(data[i:], value, width)
		return data, true
	},
}

func swap16(v uint16) uint16 {
	v0 := byte(v >> 0)
	v1 := byte(v >> 8)
	v = 0
	v |= uint16(v1) << 0
	v |= uint16(v0) << 8
	return v
}

func swap32(v uint32) uint32 {
	v0 := byte(v >> 0)
	v1 := byte(v >> 8)
	v2 := byte(v >> 16)
	v3 := byte(v >> 24)
	v = 0
	v |= uint32(v3) << 0
	v |= uint32(v2) << 8
	v |= uint32(v1) << 16
	v |= uint32(v0) << 24
	return v
}

func swap64(v uint64) uint64 {
	v0 := byte(v >> 0)
	v1 := byte(v >> 8)
	v2 := byte(v >> 16)
	v3 := byte(v >> 24)
	v4 := byte(v >> 32)
	v5 := byte(v >> 40)
	v6 := byte(v >> 48)
	v7 := byte(v >> 56)
	v = 0
	v |= uint64(v7) << 0
	v |= uint64(v6) << 8
	v |= uint64(v5) << 16
	v |= uint64(v4) << 24
	v |= uint64(v3) << 32
	v |= uint64(v2) << 40
	v |= uint64(v1) << 48
	v |= uint64(v0) << 56
	return v
}

func swapInt(v uint64, size int) uint64 {
	switch size {
	case 1:
		return v
	case 2:
		return uint64(swap16(uint16(v)))
	case 4:
		return uint64(swap32(uint32(v)))
	case 8:
		return swap64(v)
	default:
		panic(fmt.Sprintf("swapInt: bad size %v", size))
	}
}

func loadInt(data []byte, size int) uint64 {
	switch size {
	case 1:
		return uint64(data[0])
	case 2:
		return uint64(binary.LittleEndian.Uint16(data))
	case 4:
		return uint64(binary.LittleEndian.Uint32(data))
	case 8:
		return binary.LittleEndian.Uint64(data)
	default:
		panic(fmt.Sprintf("loadInt: bad size %v", size))
	}
}

func storeInt(data []byte, v uint64, size int) {
	switch size {
	case 1:
		data[0] = uint8(v)
	case 2:
		binary.LittleEndian.PutUint16(data, uint16(v))
	case 4:
		binary.LittleEndian.PutUint32(data, uint32(v))
	case 8:
		binary.LittleEndian.PutUint64(data, v)
	default:
		panic(fmt.Sprintf("storeInt: bad size %v", size))
	}
}
