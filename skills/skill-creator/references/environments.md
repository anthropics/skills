# Environment-specific guidance

The skill-creator workflow runs in Claude Code, Claude.ai, and Cowork. Each environment has different capabilities — subagents, browser access, display, package availability — and the procedure adapts accordingly. This reference describes the deltas per environment.

The default procedure (described in `SKILL.md` and `references/running-evals.md`) assumes the **Claude Code** environment. If the host is Claude.ai or Cowork, read the relevant section below for the substitutions.

---

## Claude Code

The default and most capable environment. Subagents, shell, browser, display — everything works. Use the procedures in `SKILL.md` and `references/running-evals.md` as-is.

---

## Claude.ai

The core workflow is the same (draft → test → review → improve → repeat), but Claude.ai doesn't have subagents and may not have a display, so several mechanics change.

### Running test cases

No subagents → no parallel execution. For each test case, read the skill's `SKILL.md`, then follow its instructions to accomplish the test prompt yourself. Do them one at a time.

This is less rigorous than independent subagents (you wrote the skill and you're also running it, so you have full context), but it's a useful sanity check — and the human review step compensates. **Skip the baseline runs** — just use the skill to complete the task as requested.

### Reviewing results

If you can't open a browser (Claude.ai's VM has no display, or you're on a remote server), skip the browser reviewer entirely. Present results directly in the conversation:

- For each test case, show the prompt and the output.
- If the output is a file the user needs to see (`.docx`, `.xlsx`, etc.), save it to the filesystem and tell them where it is so they can download and inspect.
- Ask for feedback inline: *"How does this look? Anything you'd change?"*

### Benchmarking

Skip the quantitative benchmarking — it relies on baseline comparisons which aren't meaningful without subagents. Focus on qualitative feedback from the user.

### The iteration loop

Same as the default — improve the skill, rerun the test cases, ask for feedback — just without the browser reviewer in the middle. You can still organize results into iteration directories on the filesystem if you have one.

### Description optimization

This step requires the `claude` CLI tool (specifically `claude -p`), which is only available in Claude Code. Skip it on Claude.ai.

### Blind comparison

Requires subagents. Skip on Claude.ai.

### Packaging

The `package_skill.py` script works anywhere with Python and a filesystem. On Claude.ai, you can run it and the user can download the resulting `.skill` file.

### Updating an existing skill

The user might be asking you to update an existing skill, not create a new one. In this case:

- **Preserve the original name.** Note the skill's directory name and `name` frontmatter field — use them unchanged. E.g., if the installed skill is `research-helper`, output `research-helper.skill` (not `research-helper-v2`).
- **Copy to a writeable location before editing.** The installed skill path may be read-only. Copy to `/tmp/skill-name/`, edit there, and package from the copy.
- **If packaging manually, stage in `/tmp/` first**, then copy to the output directory — direct writes may fail due to permissions.

---

## Cowork

Cowork has subagents but no browser or display. The main workflow runs, but the eval-viewer step adapts.

### What works as-is

- Subagents — the main workflow (spawn test cases in parallel, run baselines, grade, etc.) all works.
- If you run into severe timeout problems, it's OK to run the test prompts in series rather than parallel.
- `package_skill.py` — needs only Python and a filesystem.
- Description optimization (`run_loop.py` / `run_eval.py`) — uses `claude -p` via subprocess, not a browser.

### What adapts: the eval viewer

No browser → use `--static <output_path>` when generating the viewer to write a standalone HTML file instead of starting a server. Then provide a link the user can click to open the HTML in their browser.

**The Cowork environment seems to disincline Claude from generating the eval viewer after running tests**, so reinforce this in your TodoList. In Cowork specifically, add a task like:

> Create evals JSON and run `eval-viewer/generate_review.py` so human can review test cases

Whether in Cowork or Claude Code, after running tests you should always generate the eval viewer for the human to look at examples before revising the skill yourself and trying to make corrections. Use `generate_review.py` (do not write your own boutique HTML code). **Generate the eval viewer BEFORE evaluating outputs yourself.** You want to get them in front of the human ASAP.

### What adapts: feedback

Since there's no running server, the viewer's "Submit All Reviews" button will download `feedback.json` as a file. You can then read it from the user's downloads (you may have to request access first).

### Updating an existing skill

Follow the update guidance in the Claude.ai section above.

### Description optimization on Cowork

Works fine, but save it until you've fully finished making the skill and the user agrees it's in good shape — the optimization loop is expensive.

---

## Quick decision tree

```
Does the host have subagents?
├── No  → Use the Claude.ai adaptations
└── Yes → Does the host have a browser/display?
          ├── No  → Use the Cowork adaptations (subagents work, viewer needs --static)
          └── Yes → Use the default Claude Code procedure
```
