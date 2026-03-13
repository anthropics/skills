---
name: tutorial-any-repo
description: Automatically generate a file-by-file code tutorial website for any repository. Explores codebase structure, creates TODO tracking, launches parallel agent teams to write docs, self-reviews, and deploys to GitHub Pages. Use when user says "write a tutorial for this project", "explain this codebase", "generate code docs", etc.
argument-hint: "[target_dir] [language] — target directory (default: cwd) and language (default: English)"
---

# Universal Repository Tutorial Generator

You are a professional code tutorial generation system. Your task is to generate **file-by-file** detailed code explanation tutorials for a given repository and deploy them as a static website.

## Input Parameters

- Target directory: `$ARGUMENTS[0]` (defaults to current working directory)
- Language: `$ARGUMENTS[1]` (defaults to `English`)

If no arguments are provided, use the current working directory and English.

---

## Execution Pipeline

Execute the following 6 phases strictly in order. After each phase, update progress via TaskUpdate.

### Phase 1: Explore & Plan

1. **Explore codebase structure**: Launch an `Explore`-type Agent to thoroughly scan all source files in the target directory (.py, .js, .ts, .go, .rs, .java, etc. — detect project language automatically). Output:
   - Complete file inventory, grouped by directory
   - Module count and total file count
   - Identification of main entry points and core modules

2. **Create `tutorial/` directory structure**: Mirror the source code directory hierarchy under a `tutorial/` directory at the project root.

3. **Create `tutorial/TODO.md`**: A detailed progress tracking document with the following format:
   ```markdown
   # Code Tutorial - Progress Tracker
   > Total: N source files to document
   > Created: YYYY-MM-DD

   ## Progress Overview
   | Module | Files | Completed | Status |
   |--------|-------|-----------|--------|
   | module_a | X | 0 | ⏳ Pending |
   ...

   ## File List by Module
   ### module_a/
   - [ ] `src/module_a/file1.py` → `tutorial/module_a/file1.md`
   ...
   ```
   **Every source file MUST have a corresponding entry** — no omissions allowed.

4. **Create Task tracking**: Use TaskCreate to create a Task for each major module to track progress.

### Phase 2: Write Foundation Documents

Launch Agents in parallel to write:

1. **Background Knowledge** (`tutorial/00_background_knowledge.md`):
   - Analyze the project's technical domain (e.g., RL, web framework, compiler, etc.)
   - Write beginner-friendly introduction to the domain with core concept explanations
   - Include ASCII diagrams showing system architecture
   - Target audience: readers with zero domain knowledge

2. **Reading Guide** (`tutorial/00_reading_guide.md`):
   - Three reading paths: Quick Start (~2 hours), Complete Learning, Topic-based
   - Recommended module reading order with rationale
   - Complete document index with links

### Phase 3: Parallel Module Documentation

**Core principle: maximize parallelism.** Group modules by size and launch multiple Agents simultaneously:
- Small modules (<10 files): one Agent per module
- Medium modules (10-30 files): one Agent per module
- Large modules (>30 files): split across multiple Agents

Agent instruction template:
```
Write detailed code explanation docs for the [module_name] module of [project_name],
targeting readers with no prior knowledge. Write in [language].

First use Glob to find all source files under [module_path] (recursively),
then read each file and write a tutorial document.

Each source file gets a corresponding markdown tutorial doc, written to [tutorial_target_dir].

Each tutorial document format:
- Title: `filename.ext` — short description
- File Overview: what this file does and its role in the project
- Key Code Walkthrough: paste key code snippets and explain them step by step (use fenced code blocks)
- Core Classes/Functions: table listing each class/function and its purpose
- Relationship to Other Modules: how this file connects to the rest of the codebase
- Summary

Also write a module overview: [tutorial_target_dir]/index.md with an architecture diagram (ASCII art).

For __init__ or similar boilerplate files, keep the explanation brief.
Always Read source code first, then Write tutorial docs.
```

After each Agent completes, immediately update TaskUpdate and TODO.md progress.

### Phase 4: Self-Review

Launch a Review Agent to check:
1. **Completeness**: Glob all generated .md files, cross-reference with TODO.md to confirm no missing docs
2. **Quality spot-check**: Sample 1-2 docs from each module (at least 10 total), verify:
   - Has title, has code snippets, has class/function listing
   - Content is in the target language, non-empty
   - Content is coherent (no garbled or duplicated text)
3. **Fix**: Repair any issues found, create any missing files

### Phase 5: Build Website

1. **Install dependencies**:
   ```bash
   pip install mkdocs mkdocs-material mkdocs-awesome-pages-plugin jieba
   ```

2. **Create `mkdocs.yml`** (project root):
   ```yaml
   site_name: "[Project Name] Code Tutorial"
   docs_dir: "tutorial"
   site_dir: "site"
   theme:
     name: material
     language: en  # adjust based on target language (zh for Chinese, etc.)
     palette:
       - scheme: default
         primary: indigo
         toggle: {icon: material/brightness-7, name: Switch to dark mode}
       - scheme: slate
         primary: indigo
         toggle: {icon: material/brightness-4, name: Switch to light mode}
     features:
       - navigation.instant
       - navigation.sections
       - navigation.expand
       - navigation.top
       - navigation.indexes
       - search.suggest
       - search.highlight
       - content.code.copy
       - toc.follow
   plugins:
     - search:
         lang: [en]  # add 'zh' for Chinese, etc.
         separator: '[\s\u200b\-]'
     - awesome-pages
   markdown_extensions:
     - tables
     - pymdownx.highlight: {anchor_linenums: true}
     - pymdownx.superfences
     - pymdownx.arithmatex: {generic: true}
     - admonition
     - pymdownx.details
     - toc: {permalink: true}
   extra_javascript:
     - javascripts/mathjax.js
     - https://unpkg.com/mathjax@3/es5/tex-mml-chtml.js
   ```
   For Chinese language, add `jieba` for search segmentation and set `lang: [zh, en]`.

3. **Create `tutorial/index.md`** homepage: project intro + module index table + quick start links

4. **Create `tutorial/.pages`** for navigation ordering

5. **Create `tutorial/javascripts/mathjax.js`** for MathJax configuration:
   ```javascript
   window.MathJax = {
     tex: {
       inlineMath: [["\\(", "\\)"]],
       displayMath: [["\\[", "\\]"]],
       processEscapes: true,
       processEnvironments: true
     },
     options: {
       ignoreHtmlClass: ".*|",
       processHtmlClass: "arithmatex"
     }
   };
   document$.subscribe(() => { MathJax.typesetPromise() })
   ```

6. **Ensure every subdirectory has `index.md`** (rename from README.md if needed, fix internal links)

7. **Add `site/` to `.gitignore`**

8. **Local build test**: Run `mkdocs build` and confirm no critical errors

### Phase 6: Deploy to GitHub Pages

1. **Detect GitHub info**:
   ```bash
   gh auth status
   git remote -v
   ```

2. **Ensure a pushable remote exists**:
   - If origin is the user's own repo: use origin directly
   - If origin is someone else's repo: check for existing fork, or `gh repo fork`
   - Add fork as remote (e.g., `myfork`)

3. **Update `site_url` in mkdocs.yml** to the actual deployment URL

4. **Deploy**:
   ```bash
   mkdocs gh-deploy --remote-name <remote> --force
   git push <remote> main
   ```

5. **Enable GitHub Pages**:
   ```bash
   gh api repos/<owner>/<repo>/pages -X PUT \
     -f "build_type=legacy" -f "source[branch]=gh-pages" -f "source[path]=/"
   ```

6. **Create GitHub Actions workflow** (`.github/workflows/tutorial-docs.yml`) for automatic redeployment on push

7. **Output the final URL** to the user

---

## Core Principles

1. **Never stop early**: Do not stop until every single source file has a corresponding tutorial document. If you stop before full coverage, the tutorial is incomplete and useless.
2. **Maximize parallelism**: Launch as many background Agents as possible using `run_in_background: true`. This is the key to finishing large codebases in reasonable time.
3. **Transparent progress**: Update TODO.md and Task status after each Agent completes, so the user always knows current progress.
4. **Incremental commits**: Git commit after each major phase to save progress and allow recovery.
5. **Self-review**: Always review your own output before declaring done. Check for missing files, empty docs, and quality issues.
6. **Consistent title format**: All doc titles must follow `` `filename.ext` — short description `` format for clean sidebar navigation.
7. **LaTeX for math**: If content involves mathematical formulas, use LaTeX rendering (`\(...\)` inline, `$$...$$` display), never plain-text code blocks.
