---
name: geepers-readme
description: Generate polished, humanized GitHub READMEs with badges, MIT license, and Luke Steuber credit. Use when (1) creating READMEs for new projects, (2) improving existing READMEs, (3) preparing projects for public release, or (4) humanizing robotic documentation.
license: MIT
---

# README Generator Skill

Create professional, humanized GitHub READMEs.

## Usage

```
/geepers-readme                          # Generate README for current directory
/geepers-readme ~/projects/wordblocks    # Generate for specific project
/geepers-readme --update                 # Update existing README, preserve custom sections
```

## What It Does

1. Scans project files (`CLAUDE.md`, `package.json`, `setup.py`, code structure)
2. Identifies tech stack, entry points, live URLs
3. Generates a complete README with:
   - Badges (language, license, live site, package registry)
   - Screenshot/demo placeholder
   - Features list (verb phrases, scannable)
   - Quick start with real, working commands
   - Usage examples from actual code
   - Author block (Luke Steuber, dr.eamer.dev, Bluesky)
   - MIT License reference

## Humanization

Automatically enforces the `/humanize` skill rules:
- No "AI-powered", "AI-enhanced", "AI-driven"
- No "leverages", "utilizes", "facilitates"
- First person ("I"), not "we"
- Natural voice, specific over vague

## Routes To

- **Agent**: `geepers_readme`
- **References**: `~/.claude/skills/humanize/SKILL.md` for terminology rules

## Example Output

```markdown
# Wordblocks

Symbol-based communication for people who need it most.

![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)
![Python](https://img.shields.io/badge/python-3.10+-blue.svg)
![Live](https://img.shields.io/badge/live-dr.eamer.dev-cyan.svg)

## Features
- Builds sentences from pictographic symbols with text-to-speech
- ...

## Author
**Luke Steuber**
- Website: [dr.eamer.dev](https://dr.eamer.dev)
- Bluesky: [@lukesteuber.com](https://bsky.app/profile/lukesteuber.com)
```
