// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package kernel

import (
	"fmt"
	"path/filepath"
	"slices"
	"strconv"
	"strings"

	"github.com/google/syzkaller/pkg/aflow"
	"github.com/google/syzkaller/pkg/cover/backend"
	"github.com/google/syzkaller/pkg/mgrconfig"
	"github.com/google/syzkaller/pkg/symbolizer"
	"github.com/google/syzkaller/sys/targets"
)

// SymbolizePC action resolves the primary kernel PC address (PCs[0]) to a source file and line number.
var SymbolizePC = aflow.NewFuncAction("kernel-symbolize-pc", symbolizePC)

type symbolizePCArgs struct {
	PCs        []string
	KernelSrc  string
	KernelObj  string
	TargetOS   string
	TargetArch string
}

type InlineFrame struct {
	Func string
	File string
	Line int
}

type symbolizePCResult struct {
	// Innermost frame location (the exact location of the PC instruction,
	// which may be inside an inlined function).
	File string
	Line int
	Func string
	// Outermost frame location (the enclosing non-inlined top-level function,
	// useful as a fallback for locating the containing function definition).
	OuterFile string
	OuterLine int
	OuterFunc string
	// Complete inlined call stack from outermost enclosing function down to innermost inlined frame.
	Frames []InlineFrame
}

var makeSymbolizer = symbolizer.Make

func symbolizePC(ctx *aflow.Context, args symbolizePCArgs) (symbolizePCResult, error) {
	if len(args.PCs) == 0 {
		return symbolizePCResult{}, fmt.Errorf("invalid PC address: empty")
	}
	s := strings.TrimSpace(args.PCs[0])
	if !strings.HasPrefix(s, "0x") && !strings.HasPrefix(s, "0X") {
		return symbolizePCResult{}, fmt.Errorf("PC address must be hex and start with 0x: %q", args.PCs[0])
	}
	pc, err := strconv.ParseUint(s[2:], 16, 64)
	if err != nil {
		return symbolizePCResult{}, fmt.Errorf("invalid PC address %q: %w", args.PCs[0], err)
	}
	target := targets.Get(args.TargetOS, args.TargetArch)
	if target == nil {
		return symbolizePCResult{}, fmt.Errorf("unsupported target %s/%s", args.TargetOS, args.TargetArch)
	}
	vmlinux := filepath.Join(args.KernelObj, target.KernelObject)
	symb := makeSymbolizer(target)
	defer symb.Close()
	frames, err := symb.Symbolize(vmlinux, pc)
	if err != nil {
		return symbolizePCResult{}, fmt.Errorf("failed to symbolize PC 0x%x: %w", pc, err)
	}
	if len(frames) == 0 {
		return symbolizePCResult{}, fmt.Errorf("failed to symbolize PC 0x%x: no frames found", pc)
	}

	// frames[0] corresponds to the innermost inline or regular function frame.
	frame := frames[0]
	topFrame := frames[len(frames)-1]

	kernelDirs := KernelDirsFor(frames, args.KernelSrc, args.KernelObj)

	// Convert absolute path to relative path from the kernel source tree root.
	file, _ := backend.CleanPath(frame.File, kernelDirs, nil)
	outerFile, _ := backend.CleanPath(topFrame.File, kernelDirs, nil)

	var inlineFrames []InlineFrame
	for _, f := range slices.Backward(frames) {
		fFile, _ := backend.CleanPath(f.File, kernelDirs, nil)
		inlineFrames = append(inlineFrames, InlineFrame{
			Func: f.Func,
			File: fFile,
			Line: f.Line,
		})
	}

	return symbolizePCResult{
		File:      file,
		Line:      frame.Line,
		Func:      frame.Func,
		OuterFile: outerFile,
		OuterLine: topFrame.Line,
		OuterFunc: topFrame.Func,
		Frames:    inlineFrames,
	}, nil
}

// KernelDirsFor returns the kernel directories backend.CleanPath needs to turn the symbolizer's
// absolute file names into paths relative to the source tree.
//
// The kernel is not necessarily built from kernelSrc itself: the source cache entry may have
// been checked out (or hardlinked) into another workdir, and the kernel built from that copy,
// so DWARF records e.g. /other/cache/src/<id>/fs/ext4/inode.c while kernelSrc is
// /this/cache/src/<id>. Both copies share the cache id, so the build-time directory is
// recoverable from the frames themselves: it is the prefix ending in cache/src/<id>. Without
// it, CleanPath leaves the file names absolute, every tool that joins them onto kernelSrc
// opens a path that does not exist, and per-file coverage lookups never match.
func KernelDirsFor(frames []symbolizer.Frame, kernelSrc, kernelObj string) *mgrconfig.KernelDirs {
	dirs := &mgrconfig.KernelDirs{Src: kernelSrc, Obj: kernelObj}
	dirs.BuildSrc = inferBuildSrc(frames, kernelSrc)
	return dirs
}

func inferBuildSrc(frames []symbolizer.Frame, kernelSrc string) string {
	id := filepath.Base(filepath.Clean(kernelSrc))
	if id == "" || id == "." || id == string(filepath.Separator) {
		return ""
	}
	needle := string(filepath.Separator) + filepath.Join("cache", "src", id) + string(filepath.Separator)
	for _, f := range frames {
		// DWARF names are compdir-relative, e.g. <obj>/../../src/<id>/fs/x.c; Clean first,
		// as CleanPath itself does, so the cache/src/<id> segment is visible.
		file := filepath.Clean(f.File)
		if f.File == "" || !filepath.IsAbs(file) || strings.HasPrefix(file, kernelSrc) {
			continue
		}
		if i := strings.Index(file, needle); i >= 0 {
			return file[:i+len(needle)-1]
		}
	}
	return ""
}
