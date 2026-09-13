// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package gemini

import (
	"errors"
	"fmt"
	"slices"
	"testing"
	"time"

	"github.com/google/syzkaller/pkg/aflow/backend"
	"github.com/stretchr/testify/require"
	"google.golang.org/genai"
)

func TestProviderResolveModels(t *testing.T) {
	tests := []struct {
		name          string
		modelOverride string
		category      backend.ModelCategory
		want          []string
	}{
		{
			name:     "resolves core model pool",
			category: backend.CoreModel,
			// Flash family only: the tool tier is shared by every arm of the experiment, so a
			// fallback to Pro would silently upgrade it for whichever arm happened to meet a
			// refusal (Rui, 2026-09-13).
			want: []string{"gemini-3.8-flash", "gemini-3.7-flash", "gemini-3.6-flash", "gemini-3.5-flash"},
		},
		{
			name:     "resolves lightweight model pool",
			category: backend.LightweightModel,
			want:     []string{"gemini-3.7-flash", "gemini-3.6-flash", "gemini-3.5-flash"},
		},
		{
			name:     "resolves deep reasoning model pool",
			category: backend.DeepReasoningModel,
			want:     []string{"gemini-3.1-pro-preview"},
		},
		{
			name:     "returns nil for unrecognized category",
			category: "custom-model",
			want:     nil,
		},
		{
			name:          "respects provider level override",
			modelOverride: "override-model",
			category:      backend.CoreModel,
			want:          []string{"override-model"},
		},
		{
			name:          "respects provider level override even for unrecognized model type",
			modelOverride: "override-model",
			category:      "custom-model",
			want:          []string{"override-model"},
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			provider := &Provider{modelOverride: tc.modelOverride}
			got := provider.ResolveModels(tc.category)
			if !slices.Equal(got, tc.want) {
				t.Errorf("provider.ResolveModels(%v) = %v, want %v", tc.category, got, tc.want)
			}
		})
	}
}

func TestParseLLMError(t *testing.T) {
	type Test struct {
		resp      *genai.GenerateContentResponse
		inputErr  error
		outputErr error
	}
	tpmError1 := genai.APIError{
		Code: 429,
		// nolint:lll
		Message: `You exceeded your current quota, please check your plan and billing details. For more information on this error, head to: https://ai.google.dev/gemini-api/docs/rate-limits. To monitor your current usage, head to: https://ai.dev/rate-limit. * Quota exceeded for metric: generativelanguage.googleapis.com/generate_content_paid_tier_input_token_count, limit: 1000000, model: gemini-3-flash Please retry in 24.180878813s.`,
	}
	tests := []Test{
		{
			inputErr:  tpmError1,
			outputErr: &backend.RetryError{Delay: 25 * time.Second, Err: tpmError1},
		},
		{
			inputErr: genai.APIError{
				Code:    429,
				Message: `Resource has been exhausted (e.g. check quota).`,
			},
			outputErr: &backend.RetryError{
				Delay: time.Minute,
				Err: genai.APIError{
					Code:    429,
					Message: `Resource has been exhausted (e.g. check quota).`,
				},
			},
		},
		{
			inputErr: genai.APIError{
				Code: 400,
				// nolint:lll
				Message: `The input token count exceeds the maximum limit for this model. The input token count is 1000001, but the maximum limit is 1000000.`,
			},
			outputErr: &backend.InputTokenOverflowError{
				Err: genai.APIError{
					Code: 400,
					// nolint:lll
					Message: `The input token count exceeds the maximum limit for this model. The input token count is 1000001, but the maximum limit is 1000000.`,
				},
			},
		},
		{
			resp: &genai.GenerateContentResponse{
				Candidates: []*genai.Candidate{
					{
						FinishReason: genai.FinishReasonMaxTokens,
					},
				},
			},
			outputErr: &backend.OutputTokenOverflowError{
				Err: errors.New("MAX_TOKENS"),
			},
		},
	}
	for i, test := range tests {
		t.Run(fmt.Sprint(i), func(t *testing.T) {
			var err error
			if test.inputErr != nil {
				err = parseLLMError(test.inputErr, "smarty")
			} else if test.resp != nil {
				err = parseLLMResp(test.resp)
			}
			if err == nil || test.outputErr == nil {
				if err != test.outputErr {
					t.Errorf("got %v, want %v", err, test.outputErr)
				}
			} else if err.Error() != test.outputErr.Error() {
				t.Errorf("got %v, want %v", err, test.outputErr)
			}
		})
	}
}

func TestParseLLMErrorBackoff(t *testing.T) {
	// Let's verify that RetryErrors are correctly parsed to backoff formats from code.
	err0 := genai.APIError{Code: 503}
	err := parseLLMError(err0, "model")
	var rErr *backend.RetryError
	if !errors.As(err, &rErr) || rErr.Delay != time.Second || !rErr.IsExponential {
		t.Errorf("expected RetryError with 1s exponential delay, got %v", err)
	}
}

// Every status that says "not now" must be retryable, not fatal. Each case below was fatal
// before: the 5xx list enumerated 500/502/503/504 so a gateway's 529 killed the run, a 429 whose
// wording matched none of three message patterns fell through to the fatal return, and a response
// with no candidates aborted the flow outright -- which on 2026-09-12 cost 24 runs inside one
// three-hour window, several of them multi-hour.
func TestTransientErrorsRetry(t *testing.T) {
	retryable := func(t *testing.T, err error, what string) {
		t.Helper()
		var rErr *backend.RetryError
		if !errors.As(err, &rErr) {
			t.Errorf("%s: got %T (%v), want *backend.RetryError", what, err, err)
		}
	}
	for _, code := range []int{500, 502, 503, 504, 520, 524, 529, 539, 599, 499} {
		retryable(t, parseLLMError(genai.APIError{Code: code}, "m"), fmt.Sprintf("status %d", code))
	}
	retryable(t, parseLLMError(genai.APIError{
		Code:    429,
		Message: "some wording we have never seen before",
	}, "m"), "unrecognised 429")
	retryable(t, parseLLMResp(&genai.GenerateContentResponse{
		PromptFeedback: &genai.GenerateContentResponsePromptFeedback{},
	}), "blocked prompt")

	// A hung request must NOT be a RetryError -- the identical retry hangs again, and only a
	// non-retry error lets the model loop fall back at once -- but it must carry
	// HungRequestError so the loop can tell it apart on the LAST model, where falling back is
	// not an option and ending the flow cost three runs on 2026-09-13.
	_, err := (&client{p: &Provider{}}).hungRequestError("m")
	if err == nil {
		t.Errorf("hung request: got nil, want an error")
	}
	if r := new(backend.RetryError); errors.As(err, &r) {
		t.Errorf("hung request: got a RetryError, want a plain HungRequestError")
	}
	if h := new(backend.HungRequestError); !errors.As(err, &h) {
		t.Errorf("hung request: got %T, want *backend.HungRequestError", err)
	}

	// Zero candidates with no PromptFeedback ("empty model response") is transient too.
	retryable(t, parseLLMResp(&genai.GenerateContentResponse{}), "empty model response")

	// A daily quota is not "not now", it is "not today": retrying inside one run only burns its
	// wall budget, so it stays fatal here and the campaign layer requeues the run instead.
	dq := parseLLMError(genai.APIError{
		Code:    429,
		Message: "Quota exceeded for metric: generate_requests_per_model_per_day, limit: 100",
	}, "m")
	var rErr *backend.RetryError
	if errors.As(dq, &rErr) {
		t.Errorf("daily quota: got a RetryError, want fatal")
	}
}

func TestToGenaiContentEmptyTextParts(t *testing.T) {
	msg := &backend.Message{
		Role: backend.RoleModel,
		Parts: []backend.Part{
			{Text: ""},                // Completely empty part -> skipped.
			{Text: "", Thought: true}, // Thought part with empty text -> replaced with fallback.
			{Text: "hello"},           // Normal text part -> kept as "hello".
			{FunctionCall: &backend.FunctionCall{Name: "test_tool"}}, // Tool call -> kept.
		},
	}
	got := toGenaiContent(msg)
	require.Equal(t, "model", got.Role)
	require.Len(t, got.Parts, 3)
	require.Equal(t, "<no text generated>", got.Parts[0].Text)
	require.True(t, got.Parts[0].Thought)
	require.Equal(t, "hello", got.Parts[1].Text)
	require.NotNil(t, got.Parts[2].FunctionCall)
	require.Equal(t, "test_tool", got.Parts[2].FunctionCall.Name)
}
