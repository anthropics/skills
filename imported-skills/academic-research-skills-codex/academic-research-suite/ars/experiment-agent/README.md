# Experiment Agent

[![Version](https://img.shields.io/badge/version-1.0-blue)](https://github.com/Imbad0202/experiment-agent/releases)
[![License: CC BY-NC 4.0](https://img.shields.io/badge/license-CC%20BY--NC%204.0-lightgrey)](https://creativecommons.org/licenses/by-nc/4.0/)
[![Sponsor](https://img.shields.io/badge/sponsor-Buy%20Me%20a%20Coffee-orange?logo=buy-me-a-coffee)](https://buymeacoffee.com/crucify020v)

[繁體中文版](README.zh-TW.md)

A Claude Code skill for executing, monitoring, interpreting, and verifying experiments in academic research.

## What It Does

- **Runs code experiments** — executes scripts (Python, R, etc.), monitors for stalls/crashes in real-time, collects results
- **Manages human studies** — plans protocols, checks IRB ethics, tracks data collection progress
- **Interprets statistics** — reads p-values, effect sizes, CIs; checks 11 types of statistical fallacies (Simpson's Paradox, survivorship bias, etc.)
- **Verifies reproducibility** — re-runs experiments and compares results

## Why It Exists

Lu et al. (2026, *Nature*) demonstrated an Experiment Progress Manager for autonomous AI research. This skill brings the same execute-and-monitor capability to human-in-the-loop academic workflows — without the risks of full automation.

## Modes

| Mode | What It Does |
|------|-------------|
| `run` | Execute code + monitor process |
| `manage` | Plan + track human studies |
| `validate` | Statistical interpretation + reproducibility check |
| `plan` | Socratic dialogue to design experiments |

## Quick Start

1. Clone this repo into your project or `.claude/skills/`
2. Start a Claude Code session
3. Try: "Run my analysis: `Rscript analysis.R`"

## ARS Compatibility

This skill works independently. It also integrates optionally with [Academic Research Skills (ARS)](https://github.com/Imbad0202/academic-research-skills):

- Reads ARS Stage 1 output (RQ Brief, Methodology Blueprint) to pre-populate experiment design
- Produces Material Passport-compatible output, including an explicit verification status, for ARS Stage 2 consumption
- ARS requires zero modification — the user bridges manually

### When to use with ARS

In the ARS pipeline, experiment-agent fits **between Stage 1 (RESEARCH) and Stage 2 (WRITE)**:

```
ARS Stage 1 RESEARCH  →  you get RQ Brief + Methodology Blueprint
        ↓
  [pause ARS pipeline]
        ↓
  experiment-agent     →  plan → run/manage → validate → get analyzed or verified results
        ↓
  [resume ARS pipeline]
        ↓
ARS Stage 2 WRITE     →  write paper using your experiment results
```

Use experiment-agent when your research requires running experiments (code or human studies) before writing. If your paper is purely based on literature review or secondary data analysis, you don't need this — go directly from ARS Stage 1 to Stage 2.

### How to load

**Step 1**: Clone this repo alongside your ARS project (or anywhere on your machine):

```bash
cd ~/Projects/HEEACT
git clone https://github.com/Imbad0202/experiment-agent.git
```

**Step 2**: When you need to run experiments, open a Claude Code session **in the experiment-agent directory**:

```bash
cd ~/Projects/HEEACT/experiment-agent
claude
```

**Step 3**: Paste the relevant ARS Stage 1 output (RQ Brief, Methodology Blueprint) into the session. The agent will auto-detect the ARS headings and pre-populate your experiment plan.

**Step 4**: After your experiments are done and validated, copy the output (which includes a Material Passport header and verification status) back into your ARS session to continue Stage 2.

> You can also add this skill to any project via `.claude/skills/` symlink — see [Claude Code docs](https://docs.anthropic.com/en/docs/claude-code) for skill installation.

## Safety

- Only executes commands you specify — never auto-generates or modifies your code
- Never auto-retries crashed experiments
- Never touches raw participant data
- Statistical interpretation describes, never concludes
- Full list: see SKILL.md Safety Rules

## License

CC-BY-NC 4.0

## Author

Cheng-I Wu

---

## Changelog

See [CHANGELOG.md](CHANGELOG.md)
