# Quick Start

Get from zero to your first AI-assisted research in 3 steps.

## Step 1: Install

```bash
# Install Claude Code
curl -fsSL https://claude.ai/install.sh | bash

# Clone this repo somewhere stable
git clone https://github.com/Imbad0202/academic-research-skills.git ~/academic-research-skills

# Install each of the four skills into your project's .claude/skills/
cd /path/to/your/project
mkdir -p .claude/skills
ln -s ~/academic-research-skills/deep-research .claude/skills/deep-research
ln -s ~/academic-research-skills/academic-paper .claude/skills/academic-paper
ln -s ~/academic-research-skills/academic-paper-reviewer .claude/skills/academic-paper-reviewer
ln -s ~/academic-research-skills/academic-pipeline .claude/skills/academic-pipeline
```

Each skill must sit at `.claude/skills/<skill-name>/SKILL.md` for Claude Code to discover it. See [docs/SETUP.md](docs/SETUP.md) for the copy-based alternative, global `~/.claude/skills/` install, and the other installation methods (Claude Code plugin, Cowork via zip upload, claude.ai). Note that Cowork and claude.ai do not read `~/.claude/skills/` — they install skills through their own settings upload, not this path.

## Step 2: Launch

```bash
claude
```

## Step 3: Start researching

Tell Claude what you want to do. It will automatically pick the right skill and mode.

### Example: Guided research (Socratic mode)

```
You: "I have a vague idea about AI's impact on higher education quality assurance,
      but I'm not sure how to frame the research question. Can you guide me?"
```

Claude will enter Socratic mode — asking questions to help you clarify your thinking, not giving you answers directly. After 5-15 rounds of dialogue, you'll have a focused research question and methodology direction.

### Example: Write a paper

```
You: "Help me write a paper about the impact of declining birth rates
      on private universities in Taiwan"
```

### Example: Review an existing paper

```
You: "Review this paper" (then paste or attach the paper)
```

### Example: Full pipeline (research → write → review → revise → publish)

```
You: "I want to produce a complete research paper about how agentic AI
      is reshaping student learning outcome measurement"
```

This triggers the full 10-stage pipeline. Budget ~$4-6 in API costs and 2-4 hours of collaborative work.

## Which mode should I use?

| I want to... | Use this |
|-------------|----------|
| Explore a vague idea | `deep-research` socratic mode — just describe your interest |
| Get a quick literature summary | `deep-research` quick mode |
| Do a systematic review (PRISMA) | `deep-research` systematic-review mode |
| Write a paper from scratch | `academic-paper` full mode |
| Plan a paper chapter by chapter | `academic-paper` plan mode |
| Get my paper reviewed | `academic-paper-reviewer` full mode |
| Do everything end-to-end | `academic-pipeline` — say "I want a complete research paper" |

## What's next?

- [Full README](README.md) — all features, modes, installation options, and changelog
- [中文版](README.zh-TW.md) — Traditional Chinese version
- [Pipeline showcase](examples/showcase/) — real artifacts from a complete pipeline run
