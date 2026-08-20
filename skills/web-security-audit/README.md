# Web Security Audit Skill (web-security-audit)

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)

A general-purpose web application **security audit** skill: **white-box (source) root-cause analysis + black-box (live behavior) verification + a "negative behavior test" trio** — producing severity-graded risk reports with ready-to-paste fixes.

> Compliant with the [Agent Skills open standard](https://agentskills.io/specification) (initiated by Anthropic). Works with Claude Code, WorkBuddy, Codex CLI, Gemini CLI, Cursor, VS Code, GitHub Copilot, and more.

## Features

- **White-box + black-box combined** — statically inspect root causes (SQLi / XSS / auth / IDOR / CSRF / upload / path traversal / SSRF / info disclosure / dependencies), then verify attacker-observable behavior (status codes, response bodies, SPA fallbacks, sensitive-file reachability) and cross-validate both.
- **Negative behavior test trio** (the core; the part pure static analysis most often misses):
  1. **Malformed inputs on public endpoints** → assert `400/422`, not `500`;
  2. **Sensitive-path probing + `content-type` check** → distinguish SPA-fallback artifacts from real file leaks;
  3. **Unknown-path 404 semantics** → SPA fallback should only match extension-less frontend routes.
- **Runnable probe script** — `scripts/probe.sh <url>` runs the whole trio in one shot.
- **Safety built-in** — authorized targets only; fully non-destructive (no real injection, no brute-force, no data mutation).

## Installation

| Platform | How |
|---|---|
| Claude Code | `mkdir -p ~/.claude/skills && unzip web-security-audit-claude.zip -d ~/.claude/skills/` |
| WorkBuddy | Drop into `~/.workbuddy/skills/` |
| Other compatible platforms | Unzip into the corresponding skills directory |
| Standalone | This repo is the skill itself; `scripts/probe.sh` runs independently |

## Usage

```bash
# 1) Negative behavior test (malformed inputs / sensitive paths / unknown paths)
./scripts/probe.sh https://target.example.com

# 2) Full audit flow (driven by an AI agent)
#    recon → white-box pass → black-box pass → negative trio → cross-validation & report
```

**Output:** a severity-graded table (Critical / High / Medium / Low / Info); each finding with *symptom / impact / fix code / verification*; and direct answers to questions like *"any backdoors?"* or *"can the database be dumped?"*.

## Structure

```
web-security-audit/
├── SKILL.md                    # Skill definition: methodology + safety boundary + 5-step flow
├── references/checklist.md     # 10 white-box categories + trio commands & rules + report template + pitfalls
├── scripts/probe.sh            # Negative behavior test probe script (non-destructive)
├── README.md                   # This file
└── README.zh-CN.md             # 中文说明
```

## Safety statement

For **authorized** assessments only (your own projects or written authorization). All built-in probes are harmless verification requests. Never use against unauthorized targets.

## License

MIT
