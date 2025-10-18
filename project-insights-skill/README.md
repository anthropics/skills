# Project Insights Skill

Generate comprehensive GitHub Insights-style project analysis reports with code metrics, language distribution, commit history, tech stack identification, and visual progress tracking.

## Overview

This skill analyzes software projects and generates detailed reports to help you:
- 🔍 **Understand codebases** quickly
- 📊 **Track development progress** over time
- 📝 **Auto-generate documentation**
- 🎯 **Present metrics** to stakeholders
- ⚖️ **Compare projects** side-by-side

## Features

### Comprehensive Analysis
- **Code Statistics** - Total lines, files, languages with cloc
- **Language Distribution** - Visual breakdown with progress bars
- **Tech Stack Detection** - Auto-detect frameworks and tools
- **Git History** - Commit activity, contributors, velocity
- **Project Structure** - Directory tree with annotations
- **Progress Tracking** - Phase completion assessment
- **Documentation Quality** - README, API docs, comments analysis

### Multiple Output Formats
- **GitHub Insights Style** - Full visual report (default)
- **Minimal Style** - Quick overview
- **Comparison Mode** - Side-by-side project analysis
- **JSON Export** - Machine-readable format

### Visual Elements
```
Progress bars:     ████████████████████  100%
Language charts:   Python ████████░░  45%
Timeline:          2025-10-14  █████████  9 commits
Status indicators: 🟢 Active 🟡 Maintenance 🔴 Deprecated
```

## Installation

### For Claude Code

```bash
# Register this repository as a plugin marketplace
/plugin marketplace add /path/to/project-insights-skill

# Or clone and register
git clone https://github.com/vinci7/project-insights-skill.git ~/claude-skills/
/plugin marketplace add ~/claude-skills/project-insights-skill
```

### For Claude.ai

1. Download or clone this repository
2. In Claude.ai, go to Skills → Upload Custom Skill
3. Upload the `project-insights-skill` folder
4. The skill will be available in your skill library

### For Claude API

```python
from anthropic import Anthropic

client = Anthropic(api_key="your-api-key")

# Upload skill
with open("SKILL.md", "r") as f:
    skill_content = f.read()

response = client.skills.create(
    name="project-insights",
    content=skill_content
)

# Use skill
message = client.messages.create(
    model="claude-sonnet-4",
    max_tokens=4096,
    skills=[response.id],
    messages=[{
        "role": "user",
        "content": "Analyze this project and generate insights"
    }]
)
```

## Usage

### Basic Analysis

```
Use the project-insights skill to analyze this repository
```

### Quick Overview

```
Generate a minimal project insights report
```

### Compare Projects

```
Use project-insights to compare project-a with project-b
```

### JSON Export

```
Generate project insights in JSON format
```

### Custom Focus

```
Use project-insights focusing on tech stack and dependencies only
```

## Requirements

### Required
- Git repository (for commit history)
- File system access

### Optional (Recommended)
- `cloc` - Accurate code line counting
- `tree` - Visual directory structure
- `jq` - JSON processing

Install on macOS:
```bash
brew install cloc tree jq
```

Install on Linux:
```bash
# Ubuntu/Debian
sudo apt install cloc tree jq

# Fedora/RHEL
sudo dnf install cloc tree jq
```

The skill will automatically fall back to alternative methods if these tools aren't available.

## Examples

See `reference/examples/` for real-world analyses:
- **hindsight-example.md** - Full-stack web application
- More examples coming soon!

## Templates

Available templates in `reference/templates/`:
- **github-style.md** - Full GitHub Insights style (default)
- **minimal-style.md** - Condensed single-page report
- **comparison.md** - Side-by-side project comparison

## Helper Scripts

### collect-metrics.sh

Standalone script to gather project data:

```bash
./scripts/collect-metrics.sh /path/to/project output.json
```

Generates structured data for analysis.

## Project Structure

```
project-insights-skill/
├── SKILL.md                 Core skill definition
├── README.md               This file
├── LICENSE                 Apache 2.0 license
├── reference/
│   ├── templates/          Report templates
│   │   ├── github-style.md
│   │   ├── minimal-style.md
│   │   └── comparison.md
│   └── examples/           Real-world examples
│       └── hindsight-example.md
└── scripts/                Helper scripts
    └── collect-metrics.sh
```

## How It Works

1. **Discovery Phase** - Identifies project type and reads documentation
2. **Code Analysis** - Runs cloc, counts files, measures sizes
3. **Git Analysis** - Parses commit history, contributors, activity
4. **Tech Stack Detection** - Reads dependency files, detects frameworks
5. **Progress Assessment** - Analyzes TODO/DONE items, test coverage
6. **Report Generation** - Formats data using selected template

## Supported Project Types

- ✅ **Web Applications** - Full-stack, frontend, backend
- ✅ **Libraries/Packages** - Python, Node.js, Rust, Go
- ✅ **Mobile Apps** - React Native, Flutter
- ✅ **CLI Tools** - Any language
- ✅ **Monorepos** - Multi-package repositories
- ✅ **Documentation Sites** - Static site generators

## Tech Stack Detection

Automatically detects:

**Backend:**
- Python (FastAPI, Django, Flask)
- Node.js (Express, NestJS)
- Go (Gin, Echo)
- Rust (Actix, Rocket)
- Ruby (Rails, Sinatra)
- Java (Spring Boot)

**Frontend:**
- React, Vue, Angular, Svelte, Solid

**Databases:**
- PostgreSQL, MySQL, MongoDB, Redis

**Tools:**
- Docker, Kubernetes
- GitHub Actions, GitLab CI
- Vite, Webpack, Rollup

## Performance

- **Small projects** (<1K files): ~5 seconds
- **Medium projects** (1K-10K files): ~15 seconds
- **Large projects** (>10K files): ~60 seconds

## Limitations

- Very large repositories (>100K files) may timeout
- Binary files are not analyzed
- Generated/vendor code is excluded
- Private submodules require credentials
- No git history = limited analysis

## Contributing

Contributions welcome! Areas to improve:
- [ ] Additional report templates
- [ ] More tech stack detection patterns
- [ ] Performance optimizations
- [ ] Additional language support
- [ ] Export formats (PDF, HTML)

To contribute:
1. Fork [this repository](https://github.com/vinci7/project-insights-skill)
2. Create a feature branch
3. Make your changes
4. Submit a pull request

## Related Skills

Pair with these skills for enhanced workflows:
- **documentation-generator** - Auto-generate API docs
- **code-reviewer** - Analyze code quality
- **dependency-auditor** - Security vulnerability checks
- **performance-analyzer** - Runtime profiling

## Changelog

### v1.0.0 (2025-10-18)
- Initial release
- Core analysis features
- GitHub Insights style reporting
- Multi-format output
- Tech stack auto-detection
- Comprehensive documentation

## License

Apache License 2.0 - See [LICENSE](LICENSE) file for details.

## Author

Created with ❤️ by the Claude Code community.

## Support

- **Issues**: [Report bugs or request features](https://github.com/vinci7/project-insights-skill/issues)
- **Discussions**: [Join community discussions](https://github.com/vinci7/project-insights-skill/discussions)
- **Documentation**: See [Anthropic Skills Documentation](https://docs.claude.com/skills)

## Acknowledgments

Inspired by:
- GitHub's Insights feature
- GitLab's project analytics
- The open source community

---

**Built with Claude Code** 🤖

*Part of the [Anthropic Skills](https://github.com/anthropics/skills) ecosystem*
