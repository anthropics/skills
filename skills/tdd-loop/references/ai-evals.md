# AI Output Evals — LLM-as-Judge Harness

Use this when testing features that produce AI-generated content (summaries, suggestions,
structured extractions, chat responses, etc.).

---

## When to use

- Feature calls the Anthropic API (or any LLM) and returns generated text
- Output quality can't be verified with a simple equality check
- You need to assert things like: "response is relevant", "tone is appropriate",
  "extracted fields are correct", "no hallucinated data"

---

## Pattern: LLM-as-Judge

Run your feature → capture LLM output → send to a judge prompt → assert on the judgment.

```typescript
// eval-judge.ts
import Anthropic from '@anthropic-ai/sdk'

interface JudgeResult {
  pass: boolean
  score: number        // 0–10
  reasoning: string
}

export async function judgeOutput(
  input: string,
  output: string,
  criteria: string
): Promise<JudgeResult> {
  const client = new Anthropic()

  const response = await client.messages.create({
    model: 'claude-sonnet-4-20250514',
    max_tokens: 512,
    messages: [{
      role: 'user',
      content: `You are an evaluator. Score the following output strictly.

INPUT:
${input}

OUTPUT:
${output}

CRITERIA:
${criteria}

Respond with JSON only:
{
  "pass": true|false,
  "score": 0-10,
  "reasoning": "one sentence"
}`
    }]
  })

  const text = (response.content[0] as { text: string }).text
  return JSON.parse(text.replace(/```json|```/g, '').trim())
}
```

---

## Example: Jest eval test

```typescript
import { judgeOutput } from '../eval/eval-judge'
import { summarizeCard } from '../features/card-summary'

describe('Card summary AI eval', () => {
  it('should produce a concise, accurate summary', async () => {
    const input = { name: 'Visa Platinum', last4: '1234', issuer: 'Chase', rewards: '2x travel' }
    const output = await summarizeCard(input)

    const result = await judgeOutput(
      JSON.stringify(input),
      output,
      'The summary must mention the card name and rewards rate. Must be under 30 words. No hallucinated details.'
    )

    expect(result.pass).toBe(true)
    expect(result.score).toBeGreaterThanOrEqual(7)
  }, TDD_CONFIG.ai_eval_timeout)
})
```

---

## Determinism note

LLM judge calls are non-deterministic. To handle variance:
- Run each eval **3 times**, take majority vote on `pass`
- Log all `reasoning` strings for manual review on failure
- Use `temperature: 0` on the judge call for consistency

```typescript
async function judgeWithMajority(
  input: string, output: string, criteria: string, runs = 3
): Promise<JudgeResult> {
  const results = await Promise.all(
    Array.from({ length: runs }, () => judgeOutput(input, output, criteria))
  )
  const passes = results.filter(r => r.pass).length
  const avgScore = results.reduce((sum, r) => sum + r.score, 0) / runs
  return {
    pass: passes > runs / 2,
    score: avgScore,
    reasoning: results.map(r => r.reasoning).join(' | ')
  }
}
```

---

## Criteria writing guide

Good criteria are **specific and falsifiable**:

| ❌ Vague | ✅ Specific |
|---|---|
| "Response is good" | "Response answers the user's question and stays under 100 words" |
| "Tone is appropriate" | "Tone is professional, no slang, no exclamation marks" |
| "No hallucinations" | "All card names mentioned must appear in the input data" |
| "Structured correctly" | "JSON output contains fields: id, name, amount — all non-null" |

---

## Running evals in CI

Tag AI eval tests to run separately from unit/integration:

```typescript
// jest.config.ts
projects: [
  { displayName: 'unit', testMatch: ['**/*.test.ts'] },
  { displayName: 'ai-evals', testMatch: ['**/*.eval.ts'], testTimeout: 30000 }
]
```

```yaml
# GitHub Actions
- name: Run AI evals
  run: npx jest --selectProjects ai-evals
  env:
    ANTHROPIC_API_KEY: ${{ secrets.ANTHROPIC_API_KEY }}
```

Keep AI evals out of the hot loop (they're slow and cost money). Run on PR merge or nightly.
