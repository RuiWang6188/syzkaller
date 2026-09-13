// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

// Package gemini implements an AI backend interfacing with the Gemini API.
package gemini

import (
	"context"
	"errors"
	"fmt"
	"maps"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/google/syzkaller/pkg/aflow/backend"
	"github.com/google/syzkaller/pkg/log"
	"google.golang.org/genai"
)

type Provider struct {
	mu              sync.Mutex
	client          *genai.Client
	models          map[string]*modelInfo
	modelPathPrefix string
	modelOverride   string
	err             error
}

type modelInfo struct {
	Thinking         bool
	MinThinkingLevel backend.ThinkingLevel
	MaxTemperature   float32
	InputTokenLimit  int
	OutputTokenLimit int
}

type Config struct {
	ModelOverride string
	ClientConfig  *genai.ClientConfig
}

func NewProvider(ctx context.Context, cfg Config) (*Provider, error) {
	p := &Provider{
		modelOverride: cfg.ModelOverride,
	}
	if err := p.init(ctx, cfg); err != nil {
		return nil, err
	}
	return p, nil
}

func (p *Provider) init(ctx context.Context, cfg Config) error {
	p.mu.Lock()
	defer p.mu.Unlock()
	if p.client != nil || p.err != nil {
		return p.err
	}

	p.models = map[string]*modelInfo{
		"gemini-3.8-flash": {
			Thinking: true,
			// Verified against the API on 2026-09-13: thinkingLevel MINIMAL returns
			// "Thinking level MINIMAL is not supported for this model", LOW is accepted.
			MinThinkingLevel: backend.ThinkingLevelLow,
			MaxTemperature:   2.0,
			InputTokenLimit:  1048576,
			OutputTokenLimit: 65536,
		},
		"gemini-3.7-flash": {
			Thinking: true,
			// Gemini 3.7 Flash does not support MINIMAL thinking.
			MinThinkingLevel: backend.ThinkingLevelLow,
			MaxTemperature:   2.0,
			InputTokenLimit:  1048576,
			OutputTokenLimit: 65536,
		},
		"gemini-3.6-flash": {
			Thinking:         true,
			MaxTemperature:   2.0,
			InputTokenLimit:  1048576,
			OutputTokenLimit: 65536,
		},
		"gemini-3.5-flash": {
			Thinking:         true,
			MaxTemperature:   2.0,
			InputTokenLimit:  1048576,
			OutputTokenLimit: 65536,
		},
		"gemini-3.1-pro-preview": {
			Thinking:         true,
			MaxTemperature:   2.0,
			InputTokenLimit:  1048576,
			OutputTokenLimit: 65536,
		},
	}
	if cfg.ClientConfig != nil && cfg.ClientConfig.Backend == genai.BackendVertexAI {
		// Vertex AI backend expects the bare model name, not prefixed with "models/".
		// E.g. "gemini-1.5-pro" instead of "models/gemini-1.5-pro".
		p.modelPathPrefix = ""
	} else {
		p.modelPathPrefix = "models/"
	}

	client, err := genai.NewClient(ctx, cfg.ClientConfig)
	if err != nil {
		p.err = err
		return err
	}
	p.client = client
	return nil
}

func (p *Provider) Client(ctx context.Context) (backend.Client, error) {
	return &client{p: p}, nil
}

func (p *Provider) Models(ctx context.Context) ([]string, error) {
	models := slices.Collect(maps.Keys(p.models))
	slices.Sort(models)
	return models, nil
}

func (p *Provider) ResolveModels(category backend.ModelCategory) []string {
	if p.modelOverride != "" {
		return []string{p.modelOverride}
	}
	switch category {
	case backend.DeepReasoningModel:
		return []string{"gemini-3.1-pro-preview"}
	case backend.CoreModel:
		// A pool, because a single entry left the model loop nowhere to go: on 2026-09-12/13
		// gemini-3.7-flash answered a few percent of tool requests with 429 / 503 / a
		// zero-candidate reply, the identical retry got the same answer, and six of eight
		// substrate runs sat frozen on one call for an hour.
		//
		// The fallbacks stay inside the flash family (Rui, 2026-09-13: «我觉得可以尝试
		// gemini-3.8-flash, gemini-3.7-flash, gemini-3.6-flash和gemini-3.5-flash同flash级别的
		// 模型，不要变成pro类型的»). An earlier version fell back to gemini-3.1-pro-preview,
		// which was wrong twice over: it silently upgraded the tool tier that `repro` and
		// `recon` are supposed to share -- the whole point of putting only the DRIVING agent on
		// Pro -- and it did so at a rate set by whichever arm happened to meet a refusal, so the
		// shared substrate differed between arms by chance. Staying in-family keeps every arm's
		// helper tier identical and the cost flash-tier. All four verified callable on
		// 2026-09-13.
		return []string{"gemini-3.8-flash", "gemini-3.7-flash", "gemini-3.6-flash", "gemini-3.5-flash"}
	case backend.LightweightModel:
		return []string{"gemini-3.7-flash", "gemini-3.6-flash", "gemini-3.5-flash"}
	default:
		return nil
	}
}

func (p *Provider) Close() error {
	return nil
}

type client struct {
	p *Provider
}

func (c *client) GenerateContent(ctx context.Context, model string, cfg *backend.GenerateConfig,
	history []*backend.Message) (*backend.GenerateResponse, error) {
	info := c.p.models[model]
	if info == nil {
		models := slices.Collect(maps.Keys(c.p.models))
		slices.Sort(models)
		return nil, fmt.Errorf("model %q does not exist (models: %v)", model, models)
	}

	genaiCfg := &genai.GenerateContentConfig{}
	if cfg != nil {
		if cfg.Temperature != nil {
			temp := min(*cfg.Temperature, info.MaxTemperature)
			genaiCfg.Temperature = &temp
		}
		if cfg.SystemInstruction != nil {
			genaiCfg.SystemInstruction = toGenaiContent(cfg.SystemInstruction)
		}
		if len(cfg.Tools) > 0 {
			for _, t := range cfg.Tools {
				genaiTool := &genai.Tool{}
				for _, fd := range t.FunctionDeclarations {
					genaiTool.FunctionDeclarations = append(genaiTool.FunctionDeclarations, &genai.FunctionDeclaration{
						Name:                 fd.Name,
						Description:          fd.Description,
						ParametersJsonSchema: fd.ParametersJSONSchema,
						ResponseJsonSchema:   fd.ResponseJSONSchema,
					})
				}
				genaiCfg.Tools = append(genaiCfg.Tools, genaiTool)
			}
		}
		thinkingLevel := max(cfg.ThinkingLevel, info.MinThinkingLevel)
		if info.Thinking && thinkingLevel != backend.ThinkingLevelMinimal {
			genaiCfg.ThinkingConfig = &genai.ThinkingConfig{}
			genaiCfg.ThinkingConfig.IncludeThoughts = cfg.IncludeThoughts
			switch thinkingLevel {
			case backend.ThinkingLevelLow:
				genaiCfg.ThinkingConfig.ThinkingLevel = genai.ThinkingLevelLow
			case backend.ThinkingLevelMedium:
				genaiCfg.ThinkingConfig.ThinkingLevel = genai.ThinkingLevelMedium
			case backend.ThinkingLevelHigh:
				genaiCfg.ThinkingConfig.ThinkingLevel = genai.ThinkingLevelHigh
			}
		}
	}

	var req []*genai.Content
	for _, msg := range history {
		req = append(req, toGenaiContent(msg))
	}

	// Sometimes LLM requests just hang dead for tens of minutes,
	// abort them after 10 minutes and retry. We don't stream reply tokens,
	// so some large requests can take several minutes.
	timedCtx, cancel := context.WithTimeout(ctx, 10*time.Minute)
	defer cancel()

	resp, err := c.p.client.Models.GenerateContent(timedCtx, c.p.modelPathPrefix+model, req, genaiCfg)
	if err != nil {
		if timedCtx.Err() == context.DeadlineExceeded && ctx.Err() == nil {
			// The internal 10-minute timeout expired, but the parent context is still alive:
			// the request hung. Not a RetryError -- a retry re-issues the identical request,
			// and a request that hung once mostly hangs again, so retrying it up to
			// maxLLMRetryIters times cost 100 x 10 min with nothing to show. A plain error
			// makes llm_agent's model loop break to the next model in the category's pool
			// (CoreModel now falls back to Pro), which is what actually unblocks the call.
			return c.hungRequestError(model)
		}
		return nil, parseLLMError(err, model)
	}

	if err := parseLLMResp(resp); err != nil {
		return nil, err
	}

	return fromGenaiResponse(resp), nil
}

var rePleaseRetry = regexp.MustCompile(`Please retry in (\d+)s\.`)

// hungRequestError is what a request that outlived the 10-minute timeout returns. Plain, not
// RetryError, on purpose: see the caller.
func (c *client) hungRequestError(model string) (*backend.GenerateResponse, error) {
	return nil, &backend.HungRequestError{
		Err: fmt.Errorf("request to %v hung for 10 minutes: %w", model, context.DeadlineExceeded),
	}
}

func parseLLMError(err error, model string) error {
	var apiErr genai.APIError
	if !errors.As(err, &apiErr) {
		return err
	}
	// 499 has server-dependent meaning, but for genapi we observed these
	// when a request was cancelled on some internal error.
	// Every 5xx, not an enumerated few: a server-side status is transient by definition, and the
	// enumeration (500/502/503/504) silently made everything else fatal -- 529 and 539 from a
	// gateway, Cloudflare's 520-524 -- killing a multi-hour agent run on a status that says
	// "try again". 500 had its own identical branch further down; this subsumes it.
	if apiErr.Code == 499 || (apiErr.Code >= 500 && apiErr.Code <= 599) {
		return &backend.RetryError{Delay: time.Second, IsExponential: true, Err: err}
	}
	if apiErr.Code == 429 && strings.Contains(apiErr.Message, "Quota exceeded for metric") {
		if match := rePleaseRetry.FindStringSubmatch(apiErr.Message); match != nil {
			sec, _ := strconv.Atoi(match[1])
			return &backend.RetryError{Delay: time.Duration(sec+1) * time.Second, Err: err}
		}
		if strings.Contains(apiErr.Message, "generate_requests_per_model_per_day") {
			// We can't return modelQuotaError here directly, so we just return a generic error.
			// In aflow, we can check for this specific error string if needed.
			return fmt.Errorf("model %q is over daily quota: %w", model, err)
		}
		return &backend.RetryError{Delay: time.Second, IsExponential: true, Err: err}
	}
	if apiErr.Code == 429 && strings.Contains(apiErr.Message, "You exceeded your current quota") {
		// Unclear what this is, the error does not contain details
		// (see the test for exact error message). But presumably this is some per-minute quota.
		return &backend.RetryError{Delay: time.Minute, Err: err}
	}
	if apiErr.Code == 429 && (strings.Contains(apiErr.Message, "Resource exhausted. Please try again later.") ||
		strings.Contains(apiErr.Message, "Resource has been exhausted")) {
		// Vertex AI specific rate limit error (e.g. RPM/TPM exhausted).
		return &backend.RetryError{Delay: time.Minute, Err: err}
	}
	if apiErr.Code == 429 {
		// Any other 429. The three branches above match specific message bodies, and a 429 whose
		// wording is not among them fell through to the fatal return -- but 429 never means the
		// request was wrong, only that it came too soon, so the correct response to every one of
		// them is to wait. Retries are bounded (llm_agent.go: maxLLMRetryIters).
		return &backend.RetryError{Delay: time.Minute, Err: err}
	}
	if apiErr.Code == 400 && strings.Contains(apiErr.Message, "The input token count exceeds the maximum") {
		return &backend.InputTokenOverflowError{Err: err}
	}
	return err
}

func parseLLMResp(resp *genai.GenerateContentResponse) error {
	if len(resp.Candidates) == 0 || resp.Candidates[0] == nil {
		if resp.PromptFeedback != nil {
			// Retry, do not abort the flow. This was fatal, on the assumption that a refusal is
			// a content-policy decision and so deterministic. 2026-09-12 refuted it: 24 runs
			// across three arms died on this inside one 18:13-21:15 window and none outside it,
			// and replaying a blocked prompt verbatim afterwards returned a normal candidate.
			// A fatal error here costs the whole run -- one bug lost 3.8h on one arm and 6.0h on
			// another. A fixed delay rather than exponential keeps the worst case predictable
			// (maxLLMRetryIters x 1min) instead of letting backoff eat the run's wall budget.
			// BlockReason as well as BlockReasonMessage: the message was empty every time, so the
			// log said only "request blocked:" and named nothing.
			return &backend.RetryError{Delay: time.Minute, Err: fmt.Errorf(
				"request blocked: %v %v", resp.PromptFeedback.BlockReason,
				resp.PromptFeedback.BlockReasonMessage)}
		}
		// Retry, like its sibling above. Zero candidates with no feedback at all is a provider
		// hiccup, not a verdict, and it was still fatal after the blocked-prompt branch was
		// made retryable on 2026-09-12: three runs died on it that night, one of them 3.0 h in
		// (repro/2860e758) and one 55 min in (rcond/21f86285).
		return &backend.RetryError{Delay: time.Minute, Err: errors.New("empty model response")}
	}
	candidate := resp.Candidates[0]
	if candidate.Content == nil || len(candidate.Content.Parts) == 0 {
		if candidate.FinishReason == genai.FinishReasonMalformedFunctionCall {
			// Let's consider this as a temp error, and that the next time it won't
			// generate the same buggy output. In either case we have maxLLMRetryIters.
			return &backend.RetryError{Delay: 0, IsExponential: false, Err: errors.New(string(candidate.FinishReason))}
		}
		if candidate.FinishReason == genai.FinishReasonMaxTokens {
			return &backend.OutputTokenOverflowError{Err: errors.New(string(candidate.FinishReason))}
		}
		return fmt.Errorf("%v (%v)", candidate.FinishMessage, candidate.FinishReason)
	}
	// We don't expect to receive these fields now.
	// Note: CitationMetadata may be present sometimes, but we don't have uses for it.
	if candidate.GroundingMetadata != nil || candidate.LogprobsResult != nil {
		return fmt.Errorf("unexpected reply fields (%+v)", *candidate)
	}
	for _, part := range candidate.Content.Parts {
		if part.VideoMetadata != nil || part.InlineData != nil ||
			part.FileData != nil || part.FunctionResponse != nil ||
			part.CodeExecutionResult != nil || part.ExecutableCode != nil {
			return fmt.Errorf("unexpected reply part (%+v)", *part)
		}
	}
	return nil
}

func toGenaiContent(msg *backend.Message) *genai.Content {
	c := &genai.Content{
		Role: string(msg.Role),
	}
	for _, p := range msg.Parts {
		if p.FunctionCall != nil {
			c.Parts = append(c.Parts, &genai.Part{
				FunctionCall: &genai.FunctionCall{
					ID:   p.FunctionCall.ID,
					Name: p.FunctionCall.Name,
					Args: p.FunctionCall.Args,
				},
				ThoughtSignature: p.ThoughtSignature,
			})
		} else if p.FunctionResponse != nil {
			c.Parts = append(c.Parts, &genai.Part{
				FunctionResponse: &genai.FunctionResponse{
					ID:       p.FunctionResponse.ID,
					Name:     p.FunctionResponse.Name,
					Response: p.FunctionResponse.Response,
				},
			})
		} else {
			if p.Text == "" && !p.Thought && len(p.ThoughtSignature) == 0 {
				log.Logf(2, "aflow/gemini: skipping empty text part without thought metadata")
				continue
			}
			text := p.Text
			if text == "" {
				log.Logf(2, "aflow/gemini: replacing empty text part with fallback to initialize proto oneof field")
				text = "<no text generated>"
			}
			c.Parts = append(c.Parts, &genai.Part{
				Text:             text,
				Thought:          p.Thought,
				ThoughtSignature: p.ThoughtSignature,
			})
		}
	}
	return c
}

func fromGenaiResponse(resp *genai.GenerateContentResponse) *backend.GenerateResponse {
	res := &backend.GenerateResponse{}
	if resp.UsageMetadata != nil {
		res.UsageMetadata = &backend.UsageMetadata{
			// We add ToolUsePromptTokenCount just in case, but Gemini does not use/set it.
			InputTokens:          int(resp.UsageMetadata.PromptTokenCount) + int(resp.UsageMetadata.ToolUsePromptTokenCount),
			OutputTokens:         int(resp.UsageMetadata.CandidatesTokenCount),
			OutputThoughtsTokens: int(resp.UsageMetadata.ThoughtsTokenCount),
		}
	}
	if len(resp.Candidates) > 0 && resp.Candidates[0].Content != nil {
		for _, p := range resp.Candidates[0].Content.Parts {
			if p.FunctionCall != nil {
				res.Parts = append(res.Parts, backend.Part{
					FunctionCall: &backend.FunctionCall{
						ID:   p.FunctionCall.ID,
						Name: p.FunctionCall.Name,
						Args: p.FunctionCall.Args,
					},
					ThoughtSignature: p.ThoughtSignature,
				})
			} else {
				res.Parts = append(res.Parts, backend.Part{
					Text:             p.Text,
					Thought:          p.Thought,
					ThoughtSignature: p.ThoughtSignature,
				})
			}
		}
	}
	return res
}
