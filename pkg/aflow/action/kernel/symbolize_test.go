// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package kernel

import (
	"errors"
	"path/filepath"
	"testing"

	"github.com/google/syzkaller/pkg/cover/backend"
	"github.com/google/syzkaller/pkg/symbolizer"
	"github.com/google/syzkaller/sys/targets"
	"github.com/stretchr/testify/require"
)

type mockSymbolizer struct {
	recordedPCs []uint64
	recordedBin string
	frames      []symbolizer.Frame
	err         error
}

func (m *mockSymbolizer) Symbolize(bin string, pcs ...uint64) ([]symbolizer.Frame, error) {
	m.recordedBin = bin
	m.recordedPCs = append(m.recordedPCs, pcs...)
	if m.err != nil {
		return nil, m.err
	}
	return m.frames, nil
}

func (m *mockSymbolizer) Close() {}

func TestSymbolizePC(t *testing.T) {
	oldMakeSymbolizer := makeSymbolizer
	defer func() { makeSymbolizer = oldMakeSymbolizer }()

	tempDir := t.TempDir()
	tests := []struct {
		name        string
		args        symbolizePCArgs
		mockFrames  []symbolizer.Frame
		mockErr     error
		wantRes     symbolizePCResult
		errContains string
	}{
		{
			name: "empty PC addresses",
			args: symbolizePCArgs{
				PCs: []string{},
			},
			errContains: "invalid PC address: empty",
		},
		{
			name: "PC missing 0x prefix",
			args: symbolizePCArgs{
				PCs: []string{"ffffffff8180a42e"},
			},
			errContains: "PC address must be hex and start with 0x",
		},
		{
			name: "invalid PC hex digits",
			args: symbolizePCArgs{
				PCs: []string{"0xZZZZ"},
			},
			errContains: "invalid PC address",
		},
		{
			name: "empty target OS and Arch",
			args: symbolizePCArgs{
				PCs: []string{"0xffffffff8180a42e"},
			},
			errContains: "unsupported target /",
		},
		{
			name: "unsupported target OS and Arch",
			args: symbolizePCArgs{
				PCs:        []string{"0xffffffff8180a42e"},
				TargetOS:   "unsupported_os",
				TargetArch: "unsupported_arch",
			},
			errContains: "unsupported target unsupported_os/unsupported_arch",
		},
		{
			name: "symbolizer error",
			args: symbolizePCArgs{
				PCs:        []string{"0xffffffff8180a42e"},
				TargetOS:   "linux",
				TargetArch: "amd64",
				KernelObj:  tempDir,
				KernelSrc:  tempDir,
			},
			mockErr:     errors.New("dwarf reading failure"),
			errContains: "failed to symbolize PC 0xffffffff8180a42e: dwarf reading failure",
		},
		{
			name: "no frames returned",
			args: symbolizePCArgs{
				PCs:        []string{"0xffffffff8180a42e"},
				TargetOS:   "linux",
				TargetArch: "amd64",
				KernelObj:  tempDir,
				KernelSrc:  tempDir,
			},
			mockFrames:  []symbolizer.Frame{},
			errContains: "failed to symbolize PC 0xffffffff8180a42e: no frames found",
		},
		{
			name: "single frame success",
			args: symbolizePCArgs{
				PCs:        []string{"0xffffffff8180a42e"},
				TargetOS:   "linux",
				TargetArch: "amd64",
				KernelObj:  tempDir,
				KernelSrc:  tempDir,
			},
			mockFrames: []symbolizer.Frame{
				{
					PC:   0xffffffff8180a42e,
					Func: "do_sys_open",
					File: filepath.Join(tempDir, "fs/open.c"),
					Line: 1234,
				},
			},
			wantRes: symbolizePCResult{
				File:      "fs/open.c",
				Line:      1234,
				Func:      "do_sys_open",
				OuterFile: "fs/open.c",
				OuterLine: 1234,
				OuterFunc: "do_sys_open",
				Frames: []InlineFrame{
					{
						Func: "do_sys_open",
						File: "fs/open.c",
						Line: 1234,
					},
				},
			},
		},
		{
			name: "multiple PCs uses first PC",
			args: symbolizePCArgs{
				PCs:        []string{"0xffffffff8180a42e", "0xffffffff8180a500"},
				TargetOS:   "linux",
				TargetArch: "amd64",
				KernelObj:  tempDir,
				KernelSrc:  tempDir,
			},
			mockFrames: []symbolizer.Frame{
				{
					PC:   0xffffffff8180a42e,
					Func: "do_sys_open",
					File: filepath.Join(tempDir, "fs/open.c"),
					Line: 1234,
				},
			},
			wantRes: symbolizePCResult{
				File:      "fs/open.c",
				Line:      1234,
				Func:      "do_sys_open",
				OuterFile: "fs/open.c",
				OuterLine: 1234,
				OuterFunc: "do_sys_open",
				Frames: []InlineFrame{
					{
						Func: "do_sys_open",
						File: "fs/open.c",
						Line: 1234,
					},
				},
			},
		},
		{
			name: "inlined frames success",
			args: symbolizePCArgs{
				PCs:        []string{"0xffffffff8180a42e"},
				TargetOS:   "linux",
				TargetArch: "amd64",
				KernelObj:  tempDir,
				KernelSrc:  tempDir,
			},
			mockFrames: []symbolizer.Frame{
				{
					PC:   0xffffffff8180a42e,
					Func: "__inline_lookup",
					File: filepath.Join(tempDir, "fs/namei.c"),
					Line: 45,
				},
				{
					PC:   0xffffffff8180a42e,
					Func: "path_lookupat",
					File: filepath.Join(tempDir, "fs/namei.c"),
					Line: 120,
				},
				{
					PC:   0xffffffff8180a42e,
					Func: "filename_lookup",
					File: filepath.Join(tempDir, "fs/namei.c"),
					Line: 230,
				},
			},
			wantRes: symbolizePCResult{
				File:      "fs/namei.c",
				Line:      45,
				Func:      "__inline_lookup",
				OuterFile: "fs/namei.c",
				OuterLine: 230,
				OuterFunc: "filename_lookup",
				Frames: []InlineFrame{
					{
						Func: "filename_lookup",
						File: "fs/namei.c",
						Line: 230,
					},
					{
						Func: "path_lookupat",
						File: "fs/namei.c",
						Line: 120,
					},
					{
						Func: "__inline_lookup",
						File: "fs/namei.c",
						Line: 45,
					},
				},
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			mock := &mockSymbolizer{
				frames: tt.mockFrames,
				err:    tt.mockErr,
			}
			makeSymbolizer = func(target *targets.Target) symbolizer.Symbolizer {
				return mock
			}

			res, err := symbolizePC(nil, tt.args)
			if tt.errContains != "" {
				require.Error(t, err)
				require.Contains(t, err.Error(), tt.errContains)
			} else {
				require.NoError(t, err)
				require.Equal(t, tt.wantRes, res)
			}
		})
	}
}

func TestKernelDirsFor(t *testing.T) {
	const id = "3cfceb10090214b4fe2231e0d3ae8aa37f3d0782"
	src := "/work/camp-w10/cache/src/" + id
	obj := "/work/gate-w0/cache/build/1233aa80e3de1f6904758e9534b7eb64ab5f9680"
	built := "/work/gate-w0/cache/src/" + id
	frames := []symbolizer.Frame{
		{File: built + "/drivers/media/usb/dvb-usb/vp702x.c", Line: 10},
		{File: built + "/include/linux/usb.h", Line: 20},
	}
	dirs := KernelDirsFor(frames, src, obj)
	if dirs.Src != src || dirs.Obj != obj {
		t.Fatalf("Src/Obj changed: %+v", dirs)
	}
	if dirs.BuildSrc != built {
		t.Fatalf("BuildSrc = %q, want %q", dirs.BuildSrc, built)
	}
	rel, abs := backend.CleanPath(frames[0].File, dirs, nil)
	if rel != "drivers/media/usb/dvb-usb/vp702x.c" {
		t.Fatalf("rel = %q", rel)
	}
	if abs != src+"/drivers/media/usb/dvb-usb/vp702x.c" {
		t.Fatalf("abs = %q", abs)
	}
	// What DWARF actually records: a path relative to the build directory, not yet cleaned.
	raw := []symbolizer.Frame{{File: "/work/gate-w0/cache/build/fa6faa102444/../../src/" + id + "/fs/ext4/inode.c"}}
	if d := KernelDirsFor(raw, src, obj); d.BuildSrc != built {
		t.Fatalf("BuildSrc from a compdir-relative name = %q, want %q", d.BuildSrc, built)
	}
	if rel, _ := backend.CleanPath(raw[0].File, KernelDirsFor(raw, src, obj), nil); rel != "fs/ext4/inode.c" {
		t.Fatalf("rel = %q", rel)
	}
	// Built from kernelSrc itself: nothing to infer, CleanPath's Src case applies as before.
	same := []symbolizer.Frame{{File: src + "/fs/ext4/inode.c"}}
	if d := KernelDirsFor(same, src, obj); d.BuildSrc != "" {
		t.Fatalf("BuildSrc inferred needlessly: %q", d.BuildSrc)
	}
	if rel, _ := backend.CleanPath(same[0].File, KernelDirsFor(same, src, obj), nil); rel != "fs/ext4/inode.c" {
		t.Fatalf("rel = %q", rel)
	}
	// A different cache id is not ours to strip.
	other := []symbolizer.Frame{{File: "/work/gate-w0/cache/src/0000000000000000000000000000000000000000/fs/x.c"}}
	if d := KernelDirsFor(other, src, obj); d.BuildSrc != "" {
		t.Fatalf("BuildSrc from a foreign entry: %q", d.BuildSrc)
	}
}
