// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package syzlang

import (
	"strings"
	"testing"

	"github.com/google/syzkaller/pkg/aflow"
	"github.com/google/syzkaller/pkg/aflow/syzspec"
	"github.com/google/syzkaller/sys/targets"
	"github.com/stretchr/testify/require"
)

// The image seed the campaign's filesystem bugs need, and the line the whole thing turns on.
const (
	jfsSeed     = "test/syz_mount_image_jfs_0"
	jfsImgLine  = 6
	truncMarker = "... <line truncated>"
)

func specState(t *testing.T) specToolsState {
	return specToolsState{SyzFS: syzspec.NewSyzFS(syzkallerRepoRoot(t), targets.Linux)}
}

func readSeedLine(t *testing.T, ctx *aflow.Context, st specToolsState) string {
	t.Helper()
	res, err := readSyzSpec(ctx, st, readSyzSpecArgs{File: jfsSeed, FirstLine: jfsImgLine, LineCount: 1})
	require.NoError(t, err)
	return res.Output
}

// Off by default: the image line is truncated exactly as it was before the gate existed. This is
// the property the running campaign depends on, so it is asserted without setting the env var at
// all rather than by setting it to "0".
func TestSeedBlobs_OffByDefault(t *testing.T) {
	require.False(t, seedBlobsEnabled(), "RECON_SEED_BLOBS must be unset for the default-off test")
	out := readSeedLine(t, aflow.NewTestContext(t), specState(t))
	require.Contains(t, out, truncMarker, "with the gate off the image line must still truncate")
	require.NotContains(t, out, "$BLOB_")
	require.Less(t, len(out), 700, "a truncated line plus prefix, not the whole image")
}

// Byte-identical output with the gate off, for an image seed and for ordinary description files.
// A nil ctx is included because the existing tool tests pass one.
func TestSeedBlobs_OffIsByteIdentical(t *testing.T) {
	require.False(t, seedBlobsEnabled())
	st := specState(t)
	for _, f := range []string{jfsSeed, "sys.txt", "dev_dri.txt"} {
		withCtx, err := readSyzSpec(aflow.NewTestContext(t), st, readSyzSpecArgs{File: f, FirstLine: 1, LineCount: 40})
		require.NoError(t, err)
		nilCtx, err := readSyzSpec(nil, st, readSyzSpecArgs{File: f, FirstLine: 1, LineCount: 40})
		require.NoError(t, err)
		require.Equal(t, nilCtx.Output, withCtx.Output, "gate off must not depend on ctx for %s", f)
	}
	g1, err := syzGrepper(aflow.NewTestContext(t), st, syzGrepperArgs{Expression: "syz_mount_image", PathPrefix: "test"})
	require.NoError(t, err)
	g2, err := syzGrepper(nil, st, syzGrepperArgs{Expression: "syz_mount_image", PathPrefix: "test"})
	require.NoError(t, err)
	require.Equal(t, g2.Output, g1.Output)
}

// On: the image arrives as a placeholder the agent can paste, and RestoreBlobs round-trips it
// back to the real payload. This is the whole point -- the program text stays short while the
// program that executes carries the full image.
func TestSeedBlobs_OnDeliversTheImage(t *testing.T) {
	t.Setenv("RECON_SEED_BLOBS", "1")
	require.True(t, seedBlobsEnabled())
	ctx := aflow.NewTestContext(t)
	out := readSeedLine(t, ctx, specState(t))

	require.Contains(t, out, "$BLOB_", "the image literal must be registered, not truncated")
	require.NotContains(t, out, truncMarker, "the line must now fit under maxLineLen")
	require.Contains(t, out, "syz_mount_image$jfs", "the call itself must survive intact")
	require.Less(t, len(out), 300, "line should collapse to roughly 109 chars plus the prefix")

	restored := ctx.RestoreBlobs(out)
	require.NotContains(t, restored, "$BLOB_", "every placeholder must resolve")
	require.Greater(t, len(restored), 30000, "the restored line must carry the whole image")
	require.Contains(t, restored, "eJzs", "the zlib+base64 payload itself")
}

// On, but only where there is something to register: ordinary description files are untouched,
// so turning the gate on cannot change how a non-image bug reads its specs.
func TestSeedBlobs_OnLeavesDescriptionFilesAlone(t *testing.T) {
	st := specState(t)
	var off string
	{
		res, err := readSyzSpec(aflow.NewTestContext(t), st, readSyzSpecArgs{File: "sys.txt", FirstLine: 1, LineCount: 100})
		require.NoError(t, err)
		off = res.Output
	}
	t.Setenv("RECON_SEED_BLOBS", "1")
	res, err := readSyzSpec(aflow.NewTestContext(t), st, readSyzSpecArgs{File: "sys.txt", FirstLine: 1, LineCount: 100})
	require.NoError(t, err)
	require.Equal(t, off, res.Output, "no description-file line carries a literal of minBlobLen")
	require.NotContains(t, res.Output, "$BLOB_")
}

// The grep path is the other way an agent meets a test seed, and it truncates at the same limit.
func TestSeedBlobs_OnAppliesToGrepperToo(t *testing.T) {
	t.Setenv("RECON_SEED_BLOBS", "1")
	ctx := aflow.NewTestContext(t)
	res, err := syzGrepper(ctx, specState(t), syzGrepperArgs{Expression: "syz_mount_image\\$jfs", PathPrefix: "test"})
	require.NoError(t, err)
	require.Contains(t, res.Output, "$BLOB_")
	require.False(t, strings.Contains(res.Output, truncMarker) && !strings.Contains(res.Output, "$BLOB_"))
	require.Greater(t, len(ctx.RestoreBlobs(res.Output)), len(res.Output)*5, "restoring must expand a lot")
}
