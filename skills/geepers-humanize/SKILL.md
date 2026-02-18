---
name: humanize
description: Strip out robot-sounding language from docs and code. Use when editing READMEs, prepping content for publication, or cleaning up generated docs. Also enforces the "AI" terminology ban.
license: MIT
---

# Humanize Skill

Make docs sound like a person wrote them. Kill the corporate robot voice, enforce terminology rules, and keep things casual.

## Terminology Rules (MANDATORY - applies everywhere)

### The "AI" Ban
The word "AI" is **banned** from all code, docs, READMEs, package descriptions, and public content. No exceptions except third-party proper nouns.

| Never Write | Write Instead |
|-------------|---------------|
| "AI-powered" | "uses a language model to..." or just describe the feature |
| "AI-enhanced" | "LLM-enhanced" or describe what it actually does |
| "AI system" | "LLM", "language model", "model" |
| "AI capabilities" | "LLM capabilities" or be specific |
| "AI-driven" | "LLM-driven" or "model-driven" |
| "powered by AI" | "uses [Grok/Claude/Ollama/etc.]" - name the actual model |
| "artificial intelligence" | "language model" or "machine learning" as appropriate |
| "AI assistant" | just describe what it does |

**Why**: "AI" is a vague marketing buzzword. LLM, language model, or the actual model name tells people what's really happening. Be specific.

**Exception**: Third-party product names are fine as-is (e.g., "DigitalOcean's Gradient AI Platform").

### No Co-Authored-By
Never add `Co-Authored-By` lines to git commits. Ever. Luke is the author.

### Never Reference This Skill Publicly
Never mention "humanize" in release notes, READMEs, changelogs, package descriptions, or any public-facing content. The skill is invisible — it just makes things better silently.

### Tone: Write Like a Human
Keep it casual. If you'd feel embarrassed reading it aloud to a coworker, rewrite it.

## Quick Commands

```bash
humanize file.md                    # Fix with default threshold (0.8)
humanize file.md --preview          # Show what it'd change
humanize file.md --confidence 0.9   # Only fix the obvious stuff
humanize projects/wordblocks/       # Hit a whole directory
humanize --batch file1.md file2.md  # Multiple files
humanize README.md --yes            # Just do it, no asking
```

## What Gets Fixed

### Instant Kill (confidence >0.9)
- "In this [section/guide/tutorial]..." → just say the thing
- "It's important to note that..." → delete, say what matters
- "Let's explore..." → nope
- "Please note that..." → cut the hedging
- "AI-powered" / "AI-enhanced" → rewrite per terminology rules above
- Walls of bullet points → paragraphs where it reads better
- Over-structured numbered lists → flowing text

### Likely Robot (confidence 0.7-0.9)
- Overly formal transitions ("Furthermore", "Moreover")
- Redundant clarifications nobody asked for
- Generic placeholder examples
- Template-looking headers
- Passive voice where active reads better

### Maybe, Maybe Not (confidence 0.6-0.7)
- Flagged for review but not auto-fixed
- Could be legit style choices

## Detection Patterns

What gives away robot writing:

1. **Buzzwords**: "delve into", "leverage", "robust", "comprehensive", "streamline", "cutting-edge"
2. **Structure**: Everything in perfectly symmetric lists, numbered everything
3. **Meta-commentary**: "In this section we will discuss..." - just discuss it
4. **Hedging**: "Might", "perhaps", "it's worth noting", "it should be mentioned"
5. **Filler examples**: foo, bar, example1, myProject
6. **Banned terms**: "AI-powered", "AI-enhanced", "AI-driven" (see terminology rules)

## Confidence Levels

| Level | Range | What Happens |
|-------|-------|--------------|
| **High** | 0.9-1.0 | Fixed automatically with `--yes` |
| **Medium** | 0.7-0.9 | Shows suggestion, asks first |
| **Low** | 0.6-0.7 | Just reports in preview mode |

Adjust with `--confidence`:
```bash
humanize file.md --confidence 0.95  # Conservative - only obvious stuff
humanize file.md --confidence 0.6   # Aggressive - catch more
```

## Safety

**Preview first**: `humanize README.md --preview` shows what would change without touching anything.

**Backups**: Every edit creates a `.backup` file. Undo with `mv file.md.backup file.md`.

**Confirmation**: Asks before changing files unless you pass `--yes`.

## Examples

### Before / After

```markdown
# BEFORE (robot voice)
In this guide, we'll explore how to install the application.
It's important to note that you'll need Python 3.8 or higher.
Let's dive into the AI-powered installation process.

# AFTER (human voice)
## Installation
Needs Python 3.8+.
```

```markdown
# BEFORE
This AI-powered tool leverages comprehensive machine learning
to deliver robust, cutting-edge document processing capabilities.

# AFTER
Runs your docs through an LLM to extract metadata and rename files.
```

```markdown
# BEFORE
Please note that this feature is currently experimental and
might not work in all cases. It's worth mentioning that...

# AFTER
Experimental - might not work everywhere yet.
```

### Batch run
```bash
$ humanize projects/wordblocks/ --confidence 0.85
# Finds .md/.html/.txt files, shows what it'd fix, asks before changing
```

## Agent Cruft Cleanup (CRITICAL)

Agents leave behind `.md` files that reveal machine authorship. Hunt them down and kill them.

### Known Agent Cruft Patterns

Delete or gitignore any of these on sight:

| Pattern | What Created It |
|---------|-----------------|
| `CRITIC.md` | Architecture review agent |
| `ONBOARD.md` | Onboarding agent |
| `SUGGESTIONS.md` | Improvement suggestion agent |
| `REPO_AUDIT.md` | Repository audit agent |
| `REPOSITORY_ANALYSIS.md` | Analysis agent |
| `INTEGRATION_ANALYSIS.md` | Integration analysis agent |
| `PROGRESS_STATUS.md` | Session tracking |
| `IMPLEMENTATION_STATUS.md` | Status reports |
| `SESSION_LOG.md` | Work session logs |
| `WORK_LOG.md` | Agent work tracking |
| `AGENT_REPORT.md` | Direct agent output |
| `CONSOLIDATION_HISTORY.md` | Merge/consolidation reports |
| `EXPLORATION_SUMMARY.md` | Codebase exploration output |
| `*_IMPLEMENTATION_STATUS.md` | Prefixed status files |
| `*_PROGRESS.md` | Progress tracking files |
| `WORKING_SCRIPTS_TEST_REPORT.md` | Test run artifacts |
| `.aider.chat.history.md` | Aider session history |
| `.aider.input.history` | Aider input history |
| `temp_*` | Temporary files from any agent |

### What to Do

1. **Delete**: `rm` the file if it's not tracked
2. **Untrack**: `git rm --cached <file>` if already committed
3. **Gitignore**: Add patterns to `.gitignore` to prevent recurrence
4. **Never commit** files that reference agent names, skill paths, or orchestrator configs

### Quick Cleanup Command

```bash
# Find agent cruft in current project
find . -maxdepth 2 -name "CRITIC.md" -o -name "ONBOARD.md" -o -name "SUGGESTIONS.md" \
  -o -name "REPO_AUDIT.md" -o -name "REPOSITORY_ANALYSIS.md" -o -name "INTEGRATION_ANALYSIS.md" \
  -o -name "*_STATUS.md" -o -name "*_PROGRESS.md" -o -name "SESSION_LOG.md" \
  -o -name "WORK_LOG.md" -o -name "AGENT_REPORT.md" -o -name "temp_*" \
  -o -name ".aider.chat.history.md" -o -name ".aider.input.history" 2>/dev/null
```

### Pre-Push Check

```bash
# Before any git push, verify no agent cruft is staged:
git diff --cached --name-only | grep -iE '(CRITIC|ONBOARD|PROGRESS|STATUS|LOG|REPORT|AGENT|SUGGESTIONS|ANALYSIS|AUDIT)\.md'
# If matches found, untrack them:
# git rm --cached <matched-files>
```

## Supported Files

`.md`, `.html`, `.txt` - won't touch code blocks, inline code, links, or intentional formatting.

## Workflow Integration

### Pre-commit hook
```bash
#!/bin/bash
for file in $(git diff --cached --name-only | grep -E '\\.md$'); do
    humanize "$file" --yes --confidence 0.9
    git add "$file"
done
```

### After editing docs
```bash
humanize README.md --preview    # see suggestions
humanize README.md --yes        # apply them
```

## Troubleshooting

- **Too many false positives**: `--confidence 0.95`
- **Missing obvious stuff**: `--confidence 0.6`
- **Oops, wrong file**: `mv file.md.backup file.md`

## Advanced

Skip sections with markers:
```markdown
<!-- humanize-ignore-start -->
This stays exactly as-is.
<!-- humanize-ignore-end -->
```

Diff without modifying: `humanize README.md --diff-only > changes.diff`
