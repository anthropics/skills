# Quick Start Guide

Get started with the Project Insights Skill in 5 minutes.

## Installation

### Option 1: Claude Code (Recommended)

```bash
# Register the skill
/plugin marketplace add ~/claude-skills/project-insights-skill
```

### Option 2: Claude.ai

1. Go to Skills → Upload Custom Skill
2. Upload the `project-insights-skill` folder
3. Done!

### Option 3: Direct Use (No Installation)

Just copy `SKILL.md` content into your Claude conversation and reference it.

## First Analysis

### 1. Basic Project Analysis

Navigate to your project and ask:

```
Use the project-insights skill to analyze this repository
```

Claude will:
- Run code analysis
- Parse git history
- Detect tech stack
- Generate visual report

### 2. Quick Overview

For a faster, condensed report:

```
Generate a minimal project insights report
```

### 3. Compare Two Projects

```
Use project-insights to compare projectA/ with projectB/
```

## What You'll Get

### Full Report Includes

📊 **Repository Statistics**
- Total lines of code
- Files count
- Project size

💻 **Language Distribution**
```
Python     ████████████░░░░░░░░  18.96%
Vue.js     ████████████░░░░░░░░  17.45%
```

🛠 **Tech Stack**
- Backend frameworks
- Frontend libraries
- Database systems
- DevOps tools

🔥 **Commit Activity**
- Timeline visualization
- Contributor statistics
- Development velocity

📈 **Progress Tracking**
```
Backend    ████████████████████  100%
Frontend   █████████████████░░░   85%
```

## Common Use Cases

### Understanding a New Codebase

```
I just cloned this project. Use project-insights to give me a comprehensive overview.
```

### Creating Documentation

```
Use project-insights to generate content for our README.md
```

### Status Report for Stakeholders

```
Generate a project insights report focusing on progress and features
```

### Before Code Review

```
Use project-insights with minimal style to quickly understand this PR's context
```

## Tips

1. **Run from project root** - Ensure you're in the directory with `.git`
2. **Install cloc** - For accurate code counting: `brew install cloc`
3. **Clean before analysis** - Remove `node_modules/`, `dist/` for accurate stats
4. **Update regularly** - Re-run after major milestones

## Troubleshooting

**Q: "No git repository found"**
A: Make sure you're in a directory with `.git`. The skill will skip git analysis if not found.

**Q: "cloc not found"**
A: Install with `brew install cloc` (macOS) or use package manager on Linux. Skill works without it but gives basic counts.

**Q: Analysis takes too long**
A: Large projects (>10K files) may take 30-60 seconds. This is normal.

**Q: Inaccurate language detection**
A: Add patterns to `.gitattributes` to help classify files correctly.

## Next Steps

1. ✅ Analyze your first project
2. 📖 Read through the full [README.md](README.md)
3. 🔍 Check [examples](reference/examples/) for real analyses
4. 🎨 Explore [templates](reference/templates/) for different styles
5. 🤝 Contribute improvements!

## Examples

### Web Application (Full Stack)
```
cd ~/my-web-app
# In Claude Code:
Use project-insights skill to analyze this FastAPI + React app
```

### Python Package
```
cd ~/my-library
Use project-insights with focus on dependencies and testing
```

### Monorepo
```
cd ~/monorepo
Use project-insights to analyze this workspace and compare packages
```

## Getting Help

- 📚 [Full Documentation](README.md)
- 💬 [Anthropic Skills Docs](https://docs.claude.com/skills)
- 🐛 [Report Issues](https://github.com/vinci7/project-insights-skill/issues)

---

**Happy analyzing!** 🚀

Built with Claude Code 🤖
