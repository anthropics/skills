# Eval Workflow Reference

Use this reference after you have drafted the skill and test prompts.

## Running and evaluating test cases

Treat this as one continuous sequence. Do not stop halfway through, and do not use `/skill-test` or any other testing skill.

Put results in `<skill-name>-workspace/` as a sibling to the skill directory. Within the workspace, organize results by iteration (`iteration-1/`, `iteration-2/`, etc.), and within each iteration create one directory per test case.

### Step 1: Spawn all runs in the same turn

For each test case, launch two runs in the same turn:
- **With-skill**: run the prompt with the current skill
- **Baseline**:
  - when creating a new skill, run the same prompt with no skill
  - when improving an existing skill, snapshot the old skill and run against that snapshot

Save outputs under sibling directories like `with_skill/outputs/` and `without_skill/outputs/` or `old_skill/outputs/`.

Create an `eval_metadata.json` per test case. Give each eval a descriptive name, not just `eval-0`.

```json
{
  "eval_id": 0,
  "eval_name": "descriptive-name-here",
  "prompt": "The user's task prompt",
  "assertions": []
}
```

### Step 2: Draft assertions while runs are in progress

Do not wait idly. Draft quantitative assertions while the runs execute.

Good assertions are objective, descriptive, and easy to interpret in the benchmark viewer. If the skill is fundamentally subjective, rely more on qualitative review instead of forcing brittle assertions.

Update both `eval_metadata.json` and `evals/evals.json` once assertions are ready.

### Step 3: Capture timing immediately

When each run completes, save the notification's timing data into `timing.json` right away. That notification is the only reliable source for `total_tokens` and `duration_ms`.

```json
{
  "total_tokens": 84852,
  "duration_ms": 23332,
  "total_duration_seconds": 23.3
}
```

### Step 4: Grade, aggregate, analyze, and launch the viewer

After all runs finish:

1. **Grade each run** using `agents/grader.md`. Save results to `grading.json`. The expectations array must use the exact fields `text`, `passed`, and `evidence` because the viewer depends on them.
2. **Aggregate the benchmark**:
   ```bash
   python -m scripts.aggregate_benchmark <workspace>/iteration-N --skill-name <name>
   ```
   This produces `benchmark.json` and `benchmark.md`.
3. **Do an analyst pass** using `agents/analyzer.md` to spot weak or flaky assertions and tradeoffs hidden by the averages.
4. **Launch the viewer** with `eval-viewer/generate_review.py`.
   - For local/browser environments, start the reviewer server.
   - For headless environments, use `--static <output_path>` and have the user open the generated HTML.
   - For iteration 2+, include `--previous-workspace <workspace>/iteration-<N-1>`.
5. **Tell the user** where to review the outputs and benchmark.

Always use `generate_review.py`; do not build a custom reviewer.

### What the user sees in the viewer

The viewer has two tabs:
- **Outputs**: prompt, output, optional previous output, formal grades, and feedback box
- **Benchmark**: pass rate, timing, token usage, per-eval breakdowns, and analyst observations

### Step 5: Read feedback and close the loop

When the user says they are done reviewing, read `feedback.json`.

```json
{
  "reviews": [
    {"run_id": "eval-0-with_skill", "feedback": "the chart is missing axis labels", "timestamp": "..."},
    {"run_id": "eval-1-with_skill", "feedback": "", "timestamp": "..."}
  ],
  "status": "complete"
}
```

Empty feedback usually means the user thought it was fine. Focus revisions on the cases with concrete complaints.

If you launched a local viewer server, kill it when finished:

```bash
kill $VIEWER_PID 2>/dev/null
```

## Improving the skill

After reviewing feedback:

1. Generalize from the feedback instead of overfitting to the small eval set.
2. Keep the prompt lean. Remove instructions that waste time without improving results.
3. Explain the *why* behind instructions instead of piling on rigid MUST/NEVER language.
4. If multiple evals independently create the same helper script or workflow, bundle that script into `scripts/`.

### Iteration loop

After each revision:
1. Update the skill
2. Rerun all test cases into a new `iteration-<N+1>/`
3. Launch the reviewer again, using `--previous-workspace` when applicable
4. Wait for user feedback
5. Revise and repeat

Stop when:
- the user says they are happy
- the feedback is effectively empty
- you are no longer making meaningful progress

## Advanced: Blind comparison

For a more rigorous A/B comparison between two skill versions, read `agents/comparator.md` and `agents/analyzer.md`. This is optional and usually unnecessary unless the user explicitly wants a blind quality comparison.
