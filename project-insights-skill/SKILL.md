---
name: project-insights
description: Generate comprehensive GitHub Insights-style project analysis reports including code metrics, language distribution, commit history, tech stack identification, project structure, and development progress tracking. Use when you need to understand a codebase, create project documentation, analyze development activity, or present project statistics in a visual format.
license: Apache-2.0
metadata:
  version: "1.0.0"
  author: "Claude Code Community"
  category: "development-tools"
  tags: ["analysis", "metrics", "documentation", "git", "statistics"]
---

# Project Insights Generator

Generate comprehensive, visually-rich project analysis reports in GitHub Insights style.

## Overview

This skill analyzes software projects and generates detailed reports that help you:
- **Understand codebases** - Get instant overview of any project
- **Track development** - See commit activity and contributor patterns
- **Document projects** - Auto-generate comprehensive README sections
- **Present metrics** - Create visual reports for stakeholders
- **Compare projects** - Analyze multiple repositories side-by-side
- **Audit code** - Check language distribution, file counts, sizes

## When to Use This Skill

Use this skill when you:
- First encounter a new codebase and need to understand it quickly
- Want to create or update project documentation
- Need to present project status to stakeholders
- Are conducting code audits or technical assessments
- Want to track project evolution over time
- Need to compare multiple projects or repositories

## Process

### Phase 1: Project Discovery

**Objective:** Understand what type of project this is and gather basic metadata.

1. **Identify Project Root**
   - Look for markers: `.git`, `package.json`, `requirements.txt`, `Cargo.toml`, `go.mod`
   - Confirm current directory is project root
   - Check for monorepo structure

2. **Detect Project Type**
   - **Web Application**: Check for frontend/backend folders, web frameworks
   - **Library/Package**: Look for package manager configs
   - **Mobile App**: Check for iOS/Android folders
   - **CLI Tool**: Look for bin/, cmd/ folders
   - **Monorepo**: Multiple package.json or workspace configs

3. **Read Core Documentation**
   - Read `README.md` for project description
   - Check `CHANGELOG.md` or `PROGRESS.md` for status
   - Look for `CONTRIBUTING.md`, `LICENSE`, `BACKLOG.md`

### Phase 2: Code Analysis

**Objective:** Gather quantitative metrics about the codebase.

1. **Run Code Line Counter**
   ```bash
   cloc . --exclude-dir=node_modules,venv,__pycache__,.git,dist,build,target --json
   ```

   If `cloc` is not available, fall back to basic file counting:
   ```bash
   find . -type f -name "*.py" | wc -l
   find . -type f -name "*.ts" -o -name "*.tsx" -o -name "*.js" -o -name "*.jsx" | wc -l
   ```

2. **Get Project Structure**
   ```bash
   tree -L 3 -I 'node_modules|venv|__pycache__|.git|dist|build|target' -a
   ```

   Or use `ls -R` as fallback

3. **Calculate Directory Sizes**
   ```bash
   du -sh .
   du -sh */ 2>/dev/null | sort -hr
   ```

4. **Count Key File Types**
   - Source files per language
   - Configuration files
   - Test files
   - Documentation files

### Phase 3: Git History Analysis

**Objective:** Understand development patterns and contributors.

1. **Recent Commit History**
   ```bash
   git log --oneline --all --date=short --pretty=format:'%h|%ad|%an|%s' -30
   ```

2. **Commit Activity Timeline**
   ```bash
   git log --all --format="%ad" --date=short | sort | uniq -c
   ```

3. **Contributor Statistics**
   ```bash
   git shortlog -sn --all
   ```

4. **Development Velocity**
   - Commits per day/week/month
   - Active development periods
   - Latest activity date

### Phase 4: Tech Stack Detection

**Objective:** Identify all technologies, frameworks, and tools used.

**Backend Detection:**
- Python: `requirements.txt`, `Pipfile`, `pyproject.toml` → FastAPI/Django/Flask
- Node.js: `package.json` → Express/NestJS/Fastify
- Go: `go.mod` → Gin/Echo/Chi
- Rust: `Cargo.toml` → Actix/Rocket
- Ruby: `Gemfile` → Rails/Sinatra
- Java: `pom.xml`, `build.gradle` → Spring Boot

**Frontend Detection:**
- React: `package.json` with react dependency
- Vue: `package.json` with vue dependency
- Angular: `angular.json`
- Svelte: `svelte.config.js`
- Solid: `solid-start` in package.json

**Database Detection:**
- Check for ORM configs: `alembic/`, `migrations/`, `prisma/`
- Database drivers in dependencies
- `docker-compose.yml` for database services

**DevOps Detection:**
- `Dockerfile`, `docker-compose.yml`
- `.github/workflows/`, `.gitlab-ci.yml`
- `kubernetes/`, `helm/`
- Deployment scripts in `deploy/`, `scripts/`

**Build Tools:**
- Vite, Webpack, Rollup, esbuild
- Cargo, Maven, Gradle
- Poetry, pip-tools

### Phase 5: Development Status Assessment

**Objective:** Determine project maturity and completion status.

1. **Check for Progress Indicators**
   - Read `PROGRESS.md`, `TODO.md`, `BACKLOG.md`
   - Look for TODO comments in code
   - Check GitHub issues/milestones if available

2. **Estimate Completion**
   - Count TODO vs DONE items
   - Check test coverage indicators
   - Look for "WIP" or "MVP" markers

3. **Identify Missing Pieces**
   - Tests folder empty?
   - No CI/CD configuration?
   - Missing documentation?
   - No deployment setup?

### Phase 6: Report Generation

**Objective:** Create a comprehensive, visually appealing markdown report.

Generate report with these sections:

1. **📊 Project Overview** - Name, description, status, links
2. **📈 Repository Statistics** - Total lines, files, languages
3. **💻 Language Distribution** - Visual breakdown with progress bars
4. **🛠 Tech Stack** - Frontend, backend, database, tools
5. **📁 Project Structure** - Directory tree with annotations
6. **🔥 Commit Activity** - Timeline with visual indicators
7. **👥 Contributors** - Contributor list and statistics
8. **📊 Development Progress** - Phase completion with progress bars
9. **⚙️ Features & Capabilities** - Implemented and planned features
10. **🚀 Deployment Status** - Production info if available
11. **📝 Documentation Quality** - Assessment of docs
12. **🔮 Future Roadmap** - Planned features and improvements
13. **💡 Project Highlights** - Key strengths and patterns
14. **🏆 Project Status** - Overall status summary

## Output Formats

### Default: GitHub Insights Style (Comprehensive)

Full visual report with:
- Progress bars using `█` and `░` characters
- Tables for structured data
- Code blocks for examples
- Emoji indicators for sections
- Statistical summaries
- Timeline visualizations

Example progress bar:
```
Backend Development    ████████████████████  100%
Frontend Development   █████████████████░░░   85%
Testing & QA          ████░░░░░░░░░░░░░░░░   20%
```

Example language distribution:
```
Python             ████████████░░░░░░░░  18.96%  (2,084 lines)
Vue.js Component   ████████████░░░░░░░░  17.45%  (1,919 lines)
TypeScript         ███████████░░░░░░░░░  11.70%  (1,286 lines)
```

### Minimal Style

Condensed report with only:
- Basic statistics (lines, files, languages)
- Tech stack summary
- Recent activity
- Quick status

Use when you need a quick overview without visual elements.

### Comparison Mode

When analyzing multiple projects, generate side-by-side comparison:
- Metrics comparison table
- Tech stack differences
- Size and complexity comparison
- Development activity comparison

### JSON Export

Machine-readable format for programmatic use:
```json
{
  "project_name": "hindsight-app",
  "total_lines": 13232,
  "languages": {
    "Python": {"lines": 2084, "files": 40},
    "TypeScript": {"lines": 1286, "files": 19}
  },
  "tech_stack": {
    "backend": ["FastAPI", "SQLAlchemy"],
    "frontend": ["Vue 3", "TypeScript", "Vite"]
  },
  "metrics": {...}
}
```

## Visual Elements Reference

### Progress Bars
Use Unicode block characters for visual appeal:
```
Full:     ████████████████████  100%
High:     █████████████████░░░   85%
Medium:   ████████████░░░░░░░░   60%
Low:      ████░░░░░░░░░░░░░░░░   20%
```

### Status Indicators
```
🟢 Active Development
🟡 Maintenance Mode
🔴 Deprecated
⚪ Planning Stage
```

### Section Emojis
```
📊 Statistics        🎯 Goals
💻 Languages         ⚙️ Features
🛠 Tech Stack        🚀 Deployment
📁 Structure         📝 Documentation
🔥 Activity          🔮 Roadmap
👥 Contributors      💡 Highlights
📈 Progress          🏆 Status
```

## Usage Examples

### Example 1: Analyze Current Project
```
Use the project-insights skill to analyze this repository
```

### Example 2: Quick Overview
```
Generate a minimal project insights report for quick review
```

### Example 3: Compare Projects
```
Use project-insights to compare hindsight-app with the skills repository
```

### Example 4: JSON Export
```
Generate project insights in JSON format for automated processing
```

### Example 5: Specific Focus
```
Use project-insights focusing on tech stack and dependencies only
```

## Best Practices

### Before Running Analysis

1. **Ensure in project root** - cd to the root directory containing .git
2. **Clean build artifacts** - Remove dist/, build/, node_modules/ for accurate counts
3. **Update documentation** - Ensure README is current
4. **Commit changes** - Analysis includes git history

### During Analysis

1. **Be patient** - Large repositories may take 30-60 seconds
2. **Check tool availability** - Script will fallback if tools missing
3. **Review output** - Verify metrics make sense

### After Analysis

1. **Update regularly** - Re-run after major milestones
2. **Share with team** - Use for status updates
3. **Track over time** - Compare reports to see evolution
4. **Incorporate into docs** - Add sections to README

## Templates

This skill includes several templates in `reference/templates/`:

- **github-style.md** - Full GitHub Insights replica
- **gitlab-style.md** - GitLab project page style
- **minimal-style.md** - Condensed single-page report
- **comparison.md** - Side-by-side project comparison
- **json-schema.json** - JSON export format definition

Load the appropriate template based on use case.

## Examples

See `reference/examples/` for real project analyses:

- **hindsight-example.md** - Full-stack web application
- **library-example.md** - Python package analysis
- **monorepo-example.md** - Multi-package repository

## Limitations

**Requires:**
- Git repository for commit analysis
- File system access for structure analysis

**Optional but recommended:**
- `cloc` - Accurate code line counting (fallback available)
- `tree` - Visual directory structure (fallback available)
- `jq` - JSON processing (fallback available)

**Known Issues:**
- Very large repos (>100K files) may timeout
- Binary files are not analyzed
- Generated/vendor code is excluded
- Private submodules won't be analyzed without credentials

**Performance:**
- Small projects (<1K files): ~5 seconds
- Medium projects (1K-10K files): ~15 seconds
- Large projects (>10K files): ~60 seconds

## Advanced Features

### Custom Metrics

Add project-specific metrics by detecting special markers:
- Test coverage: Read coverage reports
- Bundle size: Check webpack-bundle-analyzer output
- Performance: Parse lighthouse reports
- Dependencies: Check for security vulnerabilities

### Historical Comparison

Compare current state with previous analysis:
```bash
diff PROJECT_INSIGHTS_v1.md PROJECT_INSIGHTS_v2.md
```

Track:
- Lines of code growth
- New dependencies added
- Contributor changes
- Feature completion progress

### Integration with CI/CD

Generate reports automatically:
- On pull requests (show impact)
- Weekly/monthly (track progress)
- Before releases (status check)

## Troubleshooting

**Problem: cloc not found**
Solution: Skill will use fallback file counting

**Problem: Tree command unavailable**
Solution: Skill will use ls -R or find commands

**Problem: No git history**
Solution: Report will skip commit analysis sections

**Problem: Inaccurate language detection**
Solution: Check .gitattributes or manually specify in SKILL invocation

**Problem: Large JSON files skew statistics**
Solution: Add JSON files to exclude patterns

## Contributing

This skill is open source! Contributions welcome:
- New templates for different report styles
- Additional tech stack detection patterns
- Performance improvements
- Bug fixes

See the skill repository for contribution guidelines.

## Related Skills

Combine with these skills for enhanced workflows:
- **documentation-generator** - Auto-generate API docs from code
- **code-reviewer** - Analyze code quality
- **dependency-auditor** - Check for security issues
- **performance-analyzer** - Profile runtime performance

## Version History

- **1.0.0** (2025-10-18) - Initial release
  - Core analysis features
  - GitHub Insights style reporting
  - Multi-format output
  - Tech stack detection
