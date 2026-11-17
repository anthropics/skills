---
name: cc-for-codex
description: >
  Use an explicitly requested, locally installed Claude Code CLI as an
  independent second agent from Codex for reviews, bounded investigations,
  and resumable handoffs. Trigger when the user asks Codex to consult, review
  with, delegate to, or hand work to Claude Code; do not invoke it implicitly.
license: Complete terms in LICENSE.txt
---

# CC for Codex

This is a portable instruction skill for Codex. It describes how to use a
user-owned Claude Code installation from a Codex task. The production bridge,
permission guards, session ledger, and test suite live in the standalone
[CC for Codex repository](https://github.com/sanchitmonga22/cc-for-codex);
this skill deliberately keeps the Agent Skills layer small and portable.

## Before invoking Claude

1. Confirm that the user asked for Claude Code, or explicitly approved the
   delegation. Never invoke a second model merely because it might be useful.
2. Tell the user that the local Claude process will use their existing Claude
   login/provider configuration and may consume Anthropic plan or API usage.
3. Resolve the current repository and read its `AGENTS.md` and `CLAUDE.md`
   before requesting review or edits.
4. Verify the local CLI with `claude --version`. If the tested bridge is
   installed, run its local doctor command before a live request:

   ```text
   <cc-for-codex-checkout>/plugins/cc-for-codex/scripts/cc-for-codex doctor --json
   ```

   If the bridge is not installed, stop and offer the installation steps in
   [installation.md](references/installation.md). Do not silently assemble a
   raw shell command for an untrusted prompt.

## Default workflow

- Use a read-only review for a second opinion. Keep the scope explicit (the
  working tree, `HEAD`, or a user-selected base ref) and return Claude's
  response as attributed evidence, not as Codex's own conclusion.
- Use an adversarial review when the user asks for challenge, failure-mode
  analysis, or hidden-assumption checking.
- Use bounded delegation only when the user explicitly asks Claude to
  investigate or implement. A write task must use a fresh verified Git
  worktree and must never overlap with Codex edits.
- Preserve a returned session identifier only when the user asks for a
  resumable conversation. Do not put secrets in prompts or background process
  arguments.

The standalone bridge exposes these workflows as the `ask`, `review`,
`adversarial-review`, `delegate`, `handoff`, `resume`, and `sessions` commands.
Prefer its launchers and skill-specific contracts over direct `claude` calls.

## Safety boundaries

- Reviews are read-only: no edits, shell execution, network tools, MCP,
  Chrome, project hooks, or subagents.
- Writes require separate confirmation of the edit and the host-safety risk.
  The bridge's default write profile is dangerous zero-prompt mode; it is not
  an operating-system sandbox even inside a Git worktree. Use the guarded
  write profile when bypassing Claude's host checks is not explicitly wanted.
- Background sessions, native passthrough, cloud/ultrareview, configuration
  mutation, and destructive session operations each require their own
  confirmation. Never use one confirmation as a substitute for another.
- A worktree does not prove that a result is correct. Codex must inspect the
  diff and run the repository's validation after Claude finishes.

Read [safety.md](references/safety.md) before any opt-in write, background,
native, cloud, or stateful operation. Report failures plainly and leave the
user in control of authentication, billing, and merge/push decisions.

## Provenance

This skill is an independent contribution by Sanchit Monga. It is informed by
the official [OpenAI Codex plugin for Claude Code](https://github.com/openai/codex-plugin-cc)
and the tested implementation in [sanchitmonga22/cc-for-codex](https://github.com/sanchitmonga22/cc-for-codex).
The corresponding OpenAI marketplace submission is preserved in the
[pushed fork branch](https://github.com/sanchitmonga22/plugins/tree/add-cc-for-codex).

Created with GPT-6 Astra in Codex.
