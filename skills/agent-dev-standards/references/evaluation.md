# Evaluation

Golden test structure and CI integration for Agent evaluation.

## Evaluation Dimensions

| Dimension | What it measures | Target |
|-----------|-----------------|--------|
| Tool Selection | Agent picks the right tool for the task | >= 90% |
| Parameter Accuracy | Tool call parameters are correct | >= 95% |
| Chain Completion | Multi-step task completes without hang | >= 85% |
| Error Recovery | Agent recovers from tool failures gracefully | >= 80% |
| Output Quality | Final output meets requirements | >= 85% |

## Golden Test Structure

`
tests/golden/<agent-name>/
  happy-path/
    test_basic_review.json
    test_standard_pr.json
  edge-cases/
    test_empty_result.json
    test_max_input.json
  failure-modes/
    test_tool_timeout.json
    test_invalid_input.json
    test_partial_result.json
`

Each test case is a JSON file describing the expected behavior:

`json
{
  "input": {
    "pr_diff": "diff --git a/src/main.py b/src/main.py",
    "rules": "Check for security issues"
  },
  "expected_behavior": {
    "tool_calls": ["search_code", "comment"],
    "min_tool_calls": 1,
    "max_tool_calls": 5
  },
  "expected_output_contains": ["security issue", "vulnerability"],
  "expected_output_not_contains": ["I think", "might be"]
}
`

## CI Integration

1. Run golden suite on every prompt/tool change.
2. Compare scores against baseline (stored in registry.yaml).
3. Block merge if any dimension drops below threshold.
4. Generate diff report: "tool_selection 92% -> 88% (FAIL)".
