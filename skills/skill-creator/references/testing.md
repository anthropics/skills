# Testing skills

Test a skill at the same boundaries where it can fail: package structure, triggering, and the work it produces. Keep these checks separate so a passing metadata check is not mistaken for a successful behavioral evaluation.

## 1. Validate the package shape

Run the repository's lightweight validator before spending time on model runs:

```bash
python skills/skill-creator/scripts/quick_validate.py path/to/my-skill
```

This checks that `SKILL.md` exists, its frontmatter is valid, the required `name` and `description` fields are present, and the fields meet the Agent Skills limits. It does not check whether the description triggers the skill or whether the instructions produce a correct result.

For a skill with executable helpers, add the cheapest deterministic checks next. Examples include `python -m py_compile` for Python scripts, a fixture-based unit test, or a dry-run that writes into a temporary directory. Keep network calls and provider credentials out of this layer.

## 2. Test triggering with paired evals

Create `evals/evals.json` next to the skill. Include both requests that should trigger the skill and near-neighbours that should not. Use the language a real user would use, and vary the wording instead of repeating the skill name.

```json
{
  "skill_name": "my-skill",
  "evals": [
    {
      "id": 1,
      "prompt": "Turn this meeting transcript into the team's decision record.",
      "expected_output": "A decision record is created using the skill workflow.",
      "files": ["evals/files/meeting.txt"],
      "expectations": ["The output contains a decision and its rationale."]
    },
    {
      "id": 2,
      "prompt": "What is the weather forecast for tomorrow?",
      "expected_output": "The skill is not needed.",
      "files": [],
      "expectations": []
    }
  ]
}
```

Use a balanced set of positive and negative cases. A positive case measures recall; a negative case measures precision. Include boundary cases that are easy to confuse with the skill, such as a related file type or a request that needs only one of the skill's tools.

Run the evaluation with the skill and with the same skill unavailable. For iterative work, keep each iteration's outputs and metadata under a separate workspace directory so that a new result can be compared with the previous version. Run repeated trials when a decision depends on a small change in trigger rate; a single model response is not a stable measurement.

## 3. Test the behavior and artifacts

Triggering only proves that the model selected the skill. Add assertions for the result that matters to the user:

- expected files exist at the requested paths;
- generated files can be opened or parsed by the relevant library;
- required fields, headings, or records are present;
- the skill's scripts were used when the workflow depends on them;
- invalid input produces a clear error and does not leave a partial artifact.

Prefer assertions that inspect structure over string presence alone. For example, parse a JSON file and check its keys, or inspect a document's paragraphs, rather than checking that the output contains a word that could appear in an explanation.

Keep fixtures small and representative. A fixture should exercise one behavior and be safe to commit. Do not commit credentials, private customer data, or generated files that are only useful for one model run.

## 4. Record and review results

For each eval, record the prompt, expected behavior, configuration, model, and whether the run used the current or previous skill version. Keep quantitative grading (`grading.json`) separate from qualitative review. The benchmark is useful for spotting regressions, but it does not replace checking the actual artifact.

Before publishing a change, review:

1. metadata validation passes;
2. deterministic helper checks pass;
3. positive and negative trigger cases behave as expected;
4. artifact assertions pass for representative inputs;
5. the skill still explains any multi-turn or interactive requirement;
6. no test depends on a live paid API unless the test is explicitly opt-in.

For the full paired-run workflow, result layout, grading schema, and benchmark commands, see the testing sections in [`SKILL.md`](../SKILL.md) and [`schemas.md`](schemas.md).
