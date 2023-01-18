// Copyright 2023 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package match

import (
	"testing"

	"github.com/google/syzkaller/pkg/subsystem/entity"
	"github.com/stretchr/testify/assert"
)

func TestCoincidenceMatrix(t *testing.T) {
	cm := MakeCoincidenceMatrix()
	a, b, c := &entity.Subsystem{}, &entity.Subsystem{}, &entity.Subsystem{}
	cm.Record(a, b)
	cm.Record(b, c)

	// Test counts.
	assert.Equal(t, cm.Count(a), 1)
	assert.Equal(t, cm.Count(b), 2)
	assert.Equal(t, cm.Count(c), 1)

	// Test pairwise counts.
	assert.Equal(t, cm.Get(a, b), 1)
	assert.Equal(t, cm.Get(b, c), 1)
	assert.Equal(t, cm.Get(a, c), 0)

	// Test the iterator.
	type pair struct {
		a *entity.Subsystem
		b *entity.Subsystem
	}
	expected := []pair{{a, b}, {b, a}, {b, c}, {c, b}}
	got := []pair{}
	cm.NonEmptyPairs(func(a, b *entity.Subsystem, _ int) {
		got = append(got, pair{a, b})
	})
	assert.ElementsMatch(t, expected, got)
}
