# Command Reference: 15 Modern CLI Tools

This reference provides detailed command syntax, options, and examples for all 15 tools included in the shell-tools-osx skill.

## Core Search & File Tools

### fd - Fast File Finder

**Basic Syntax:** `fd [options] [pattern] [path]`

**Common Options:**
- `-e, --extension <ext>` - Filter by file extension
- `-E, --exclude <pattern>` - Exclude paths matching pattern
- `-t, --type <type>` - Filter by type (f=file, d=directory, l=symlink)
- `-H` - Search hidden files
- `-I` - Don't respect .gitignore

**Examples:**
```bash
# Find all TypeScript files
fd -e ts

# Find in src, excluding dist
fd -e ts -E dist src

# Find directories only
fd -t d config

# Find hidden files
fd -H .env
```

### ripgrep (rg) - Fast Text Search

**Basic Syntax:** `rg [options] <pattern> [path]`

**Common Options:**
- `-n, --line-number` - Show line numbers
- `-i, --ignore-case` - Case insensitive search
- `--glob <pattern>` - Include/exclude files
- `-l, --files-with-matches` - Only show filenames
- `-C, --context <num>` - Show context lines
- `-A, --after-context <num>` - Show lines after
- `-B, --before-context <num>` - Show lines before

**Examples:**
```bash
# Basic search with line numbers
rg -n "TODO"

# Exclude dist directory
rg "TODO" --glob '!dist'

# Case insensitive with context
rg -i -C 3 "error"

# Search specific file types
rg "import" -g "*.ts"
```

### ast-grep (sg) - AST-Aware Code Search

**Basic Syntax:** `sg [options] -p <pattern> [-r <replacement>]`

**Common Options:**
- `-l, --lang <lang>` - Language (ts, js, py, etc.)
- `-p, --pattern <pattern>` - Search pattern (AST-aware)
- `-r, --rewrite <replacement>` - Replacement pattern
- `--update` - Apply changes to files
- `--dry-run` - Preview changes without applying

**Pattern Variables:**
- `$VAR` - Match any expression
- `$$$` - Match multiple statements

**Examples:**
```bash
# Find console.log statements
sg -l ts -p 'console.log($X)'

# Preview refactor (dry run)
sg -l ts -p 'console.log($X)' -r 'logger.debug($X)' --update --dry-run

# Apply refactor
sg -l ts -p 'console.log($X)' -r 'logger.debug($X)' --update

# Find function calls with any arguments
sg -l ts -p 'fetchData($$$)'
```

## Data Processing

### jq - JSON Processor

**Basic Syntax:** `jq [options] '<filter>' [file]`

**Common Options:**
- `-r, --raw-output` - Output raw strings, not JSON
- `-c, --compact-output` - Compact output
- `-S, --sort-keys` - Sort object keys
- `-e, --exit-status` - Exit with error if output is false/null

**Common Filters:**
- `.field` - Access field
- `.[]` - Array iterator
- `.[n]` - Array index
- `select()` - Filter items
- `map()` - Transform array
- `sort_by()` - Sort array

**Examples:**
```bash
# Extract field from all items
jq -r '.items[].id' data.json

# Top N by score
jq -r 'sort_by(-.score)[:20] | .[].user_id' data.json

# Filter items
jq '.items[] | select(.active == true)' data.json

# Transform structure
jq '{id: .id, name: .user.name}' data.json

# Multiple operations
cat data.json | jq '.items[] | select(.score > 50) | {id, score}'
```

## Interactive Tools

### fzf - Fuzzy Finder

**Basic Syntax:** `command | fzf [options]`

**Common Options:**
- `-m, --multi` - Enable multi-select
- `--preview <command>` - Preview window command
- `--preview-window <options>` - Preview window position/size
- `-q, --query <query>` - Start with query

**Examples:**
```bash
# Pick file to view
fd -t f | fzf | xargs bat

# Multi-select files to delete
fd -t f | fzf -m | xargs rm

# With preview
fd -t f | fzf --preview 'bat --color=always {}'

# Pick file and open in editor
vim $(fd -t f | fzf)

# Search git commits
git log --oneline | fzf --preview 'git show {1}'
```

## Display & Navigation

### bat - Cat with Syntax Highlighting

**Basic Syntax:** `bat [options] [file]`

**Common Options:**
- `-n, --number` - Show line numbers
- `-p, --plain` - Plain output (no decorations)
- `-l, --language <lang>` - Force language
- `--paging <when>` - When to use pager (always, never, auto)

**Examples:**
```bash
# View with line numbers
bat -n README.md

# Plain output (no decorations)
bat -p config.json

# Force language
bat -l json data.txt

# No pager
bat --paging=never script.sh
```

### eza - Modern ls

**Basic Syntax:** `eza [options] [path]`

**Common Options:**
- `-l, --long` - Long format
- `-a, --all` - Show hidden files
- `-T, --tree` - Tree view
- `--git` - Show git status
- `--level <depth>` - Tree depth
- `-s, --sort <field>` - Sort by field

**Examples:**
```bash
# Long format with git status
eza -l --git

# Tree view of src, depth 2
eza -T --level=2 src

# All files, sorted by modified time
eza -la -s modified

# Tree with git info
eza -T --git src | less -R
```

### zoxide - Smart Directory Jump

**Basic Syntax:** `z [query]` or `zi` (interactive)

**Common Commands:**
- `z <query>` - Jump to matching directory
- `zi <query>` - Interactive selection
- `zoxide query <query>` - Query without jumping
- `zoxide add <path>` - Add path to database
- `zoxide remove <path>` - Remove path from database

**Examples:**
```bash
# Jump to frequently used directory
z projects

# Interactive selection
zi doc

# Query matches
zoxide query proj
```

## Network & Git

### httpie (http) - HTTP Client

**Basic Syntax:** `http [method] <url> [items]`

**Request Items:**
- `Header:Value` - Custom header
- `param==value` - Query parameter
- `field=value` - JSON field (POST)
- `field:=json` - Raw JSON field

**Common Options:**
- `-v, --verbose` - Verbose output
- `-h, --headers` - Only show headers
- `-b, --body` - Only show body
- `-d, --download` - Download file
- `-o, --output <file>` - Output to file

**Examples:**
```bash
# Simple GET
http GET api.example.com/items

# With query parameters
http GET :3000/items limit==50 offset==0

# With auth header
http GET :3000/items "Authorization:Bearer $TOKEN"

# POST with JSON body
http POST :3000/items name="test" active:=true

# Custom headers
http GET api.example.com "User-Agent:MyApp/1.0"

# Download file
http -d https://example.com/file.zip
```

### git-delta (delta) - Better Git Diffs

**Basic Syntax:** Use as git pager via config or `-c` flag

**Configuration:**
```bash
# In ~/.gitconfig
[core]
    pager = delta

[delta]
    features = side-by-side line-numbers decorations
    syntax-theme = Dracula
```

**Ad-hoc Usage:**
```bash
# View last commit
git -c core.pager=delta show

# Diff branches
git -c core.pager=delta diff main..feature

# Diff specific file
git -c core.pager=delta diff HEAD~1 -- src/app.ts

# Staged changes
git -c core.pager=delta diff --staged
```

## High-Leverage Add-ons

### mise - Runtime & Task Manager

**Basic Syntax:** `mise [command] [options]`

**Common Commands:**
- `mise use [runtime][@version]` - Install and use runtime
- `mise install` - Install all runtimes from config
- `mise run <task>` - Run task from config
- `mise ls` - List installed runtimes
- `mise current` - Show current runtime versions

**Config File:** `.mise.toml`
```toml
[tools]
node = "lts"
python = "3.12"

[env]
APP_ENV = "dev"
DATABASE_URL = "postgres://localhost/mydb"

[tasks.dev]
run = "node server.js"

[tasks.test]
run = "npm test"
```

**Examples:**
```bash
# Install Node LTS globally
mise use -g node@lts

# Install Python 3.12 for project
mise use python@3.12

# Install all from .mise.toml
mise install

# Run task
mise run dev

# List installed
mise ls
```

### direnv - Auto Environment Loader

**Basic Syntax:** `direnv [command]`

**Common Commands:**
- `direnv allow [path]` - Allow .envrc in directory
- `direnv deny [path]` - Deny .envrc
- `direnv reload` - Reload current .envrc

**Config File:** `.envrc`
```bash
# Load .env file
dotenv_if_exists .env

# Set variables
export APP_ENV=dev
export DEBUG=true

# Add to PATH
PATH_add bin

# Load mise/asdf
use mise
```

**Setup (one-time):**
```bash
# Add to ~/.zshrc or ~/.bashrc
eval "$(direnv hook zsh)"  # or bash
```

**Usage:**
```bash
# Create .envrc
echo 'export FOO=bar' > .envrc

# Allow it
direnv allow

# Now cd into directory auto-loads env
# cd away auto-unloads
```

### just - Task Runner

**Basic Syntax:** `just [task] [args]`

**Common Commands:**
- `just` - Run default task
- `just <task>` - Run specific task
- `just --list` - List available tasks
- `just --show <task>` - Show task recipe

**Config File:** `justfile`
```make
# Variables
build_dir := "dist"

# Default task (runs when 'just' called with no args)
default:
  @just --list

# Build project
build:
  npm ci && npm run build

# Run tests
test:
  npm test -- --watch=false

# Task with parameters
crawl ENV="dev":
  node scripts/crawl.js --env {{ENV}}

# Task dependencies
deploy: build test
  ./deploy.sh {{build_dir}}

# Multi-line with error handling
release VERSION:
  #!/usr/bin/env bash
  set -euo pipefail
  git tag v{{VERSION}}
  git push origin v{{VERSION}}
  echo "Released v{{VERSION}}"
```

**Examples:**
```bash
# List tasks
just --list

# Run task
just build

# With arguments
just crawl prod

# Run dependent tasks
just deploy
```

### pre-commit - Git Hook Framework

**Basic Syntax:** `pre-commit [command]`

**Common Commands:**
- `pre-commit install` - Install git hooks
- `pre-commit run` - Run on staged files
- `pre-commit run --all-files` - Run on all files
- `pre-commit autoupdate` - Update hook versions
- `pre-commit uninstall` - Remove hooks

**Config File:** `.pre-commit-config.yaml`
```yaml
repos:
  # Standard hooks
  - repo: https://github.com/pre-commit/pre-commit-hooks
    rev: v4.6.0
    hooks:
      - id: check-yaml
      - id: end-of-file-fixer
      - id: trailing-whitespace
      - id: check-json
      - id: check-merge-conflict
      - id: detect-private-key

  # Python formatting
  - repo: https://github.com/psf/black
    rev: 24.4.2
    hooks:
      - id: black

  # JavaScript/TypeScript
  - repo: https://github.com/pre-commit/mirrors-eslint
    rev: v8.56.0
    hooks:
      - id: eslint
        files: \.(js|ts|tsx)$
        args: [--fix]
```

**Examples:**
```bash
# Install hooks (one-time per repo)
pre-commit install

# Run manually on staged files
pre-commit run

# Run on all files
pre-commit run --all-files

# Update to latest versions
pre-commit autoupdate
```

### sops + age - Encrypted Secrets

**Basic Syntax:** `sops [options] <file>`

**Common Commands:**
- `sops -e <file>` - Encrypt file
- `sops -d <file>` - Decrypt file
- `sops <file>` - Edit encrypted file
- `age-keygen` - Generate age key pair

**Setup:**
```bash
# Generate age key pair
mkdir -p ~/.config/age
age-keygen -o ~/.config/age/keys.txt

# Export public key for encryption
export SOPS_AGE_RECIPIENTS=$(age-keygen -y ~/.config/age/keys.txt)

# Save to profile for persistence
echo "export SOPS_AGE_RECIPIENTS=$(age-keygen -y ~/.config/age/keys.txt)" >> ~/.zshrc
```

**Encrypt/Decrypt:**
```bash
# Encrypt file
sops --encrypt --age "$SOPS_AGE_RECIPIENTS" secrets.yaml > secrets.enc.yaml

# Decrypt to stdout (read-only)
sops -d secrets.enc.yaml

# Decrypt to file
sops -d secrets.enc.yaml > /tmp/secrets.yaml

# Edit encrypted file (decrypts, opens editor, re-encrypts)
sops secrets.enc.yaml
```

**Config File:** `.sops.yaml` (project root)
```yaml
creation_rules:
  - path_regex: \.enc\.yaml$
    age: age1ql3z7hjy54pw3hyww5ayyfg7zqgvc7w3j2elw8zmrj2kg5sfn9aqmcac8p
```

**Integration Examples:**
```bash
# Use in scripts
eval $(sops -d secrets.enc.yaml | yq eval '.env' -)

# Decrypt for app runtime
sops -d secrets.enc.yaml > /tmp/config.yaml && ./app --config /tmp/config.yaml

# Git pre-commit hook to prevent plaintext secrets
# (Add to .pre-commit-config.yaml)
- repo: local
  hooks:
    - id: forbid-secrets
      name: Forbid plaintext secrets
      entry: 'secrets\.yaml$'
      language: pygrep
      files: ''
```

## Common Workflows

### Search & Replace Workflow
```bash
# 1. Find files
fd -e ts src

# 2. Search for pattern
rg "oldFunction" src

# 3. Preview AST-aware replacement
sg -l ts -p 'oldFunction($X)' -r 'newFunction($X)' --update --dry-run

# 4. Apply if satisfied
sg -l ts -p 'oldFunction($X)' -r 'newFunction($X)' --update
```

### Code Review Workflow
```bash
# 1. See changed files
git -c core.pager=delta diff --name-only

# 2. Review diff
git -c core.pager=delta diff main..feature

# 3. Check specific file
git -c core.pager=delta show HEAD:src/app.ts

# 4. Interactive file selection
git diff --name-only | fzf | xargs -I{} git -c core.pager=delta diff {}
```

### API Development Workflow
```bash
# 1. Start server with mise
mise run dev

# 2. Test endpoints
http GET :3000/health
http GET :3000/api/users limit==10

# 3. With auth
export TOKEN=$(http POST :3000/auth/login email=user@example.com password=pass | jq -r '.token')
http GET :3000/api/protected "Authorization:Bearer $TOKEN"

# 4. Format response
http GET :3000/api/users | jq -r '.users[] | "\(.id) - \(.name)"'
```

### Project Setup Workflow
```bash
# 1. Set up runtime versions
mise use node@lts python@3.12

# 2. Configure environment
cat > .envrc <<EOF
dotenv_if_exists .env
export APP_ENV=dev
use mise
EOF
direnv allow

# 3. Create task runner
cat > justfile <<EOF
install:
  npm install

dev:
  npm run dev

test:
  npm test
EOF

# 4. Set up git hooks
cat > .pre-commit-config.yaml <<EOF
repos:
  - repo: https://github.com/pre-commit/pre-commit-hooks
    rev: v4.6.0
    hooks:
      - id: trailing-whitespace
      - id: check-yaml
EOF
pre-commit install
```

## New Essential Tools

### yq - YAML Processor

**Basic Syntax:** `yq eval [options] '<expression>' [file]`

**Common Options:**
- `-i, --inplace` - Edit file in place
- `-o, --output-format <format>` - Output format (yaml, json, xml, props)
- `-P, --prettyPrint` - Pretty print output
- `-I, --indent <num>` - Indentation size

**Common Expressions:**
- `.field` - Access field
- `.field.nested` - Nested access
- `.array[]` - Array iterator  
- `.array[0]` - Array index
- `select()` - Filter items

**Examples:**
```bash
# Read field
yq eval '.services.app.image' docker-compose.yml

# Update field in place
yq eval '.services.app.image = "node:20"' -i docker-compose.yml

# Add new field
yq eval '.services.app.ports = ["3000:3000"]' -i docker-compose.yml

# Delete field
yq eval 'del(.services.old)' -i docker-compose.yml

# Convert YAML to JSON
yq eval -o=json config.yaml

# Convert JSON to YAML
yq eval -P input.json

# Merge YAML files
yq eval-all 'select(fileIndex == 0) * select(fileIndex == 1)' base.yaml override.yaml

# Filter array
yq eval '.items[] | select(.active == true)' data.yaml

# Get array length
yq eval '.items | length' data.yaml

# Extract specific fields
yq eval '.services.*.image' docker-compose.yml
```

### gh - GitHub CLI

**Basic Syntax:** `gh <command> <subcommand> [options]`

**Authentication:**
```bash
# Login interactively
gh auth login

# Login with token
gh auth login --with-token < token.txt

# Check status
gh auth status

# Logout
gh auth logout
```

**Pull Requests:**
```bash
# Create PR
gh pr create --title "feat: add feature" --body "Description"

# Create PR using template
gh pr create --fill

# Create draft PR
gh pr create --draft --title "WIP: feature"

# List PRs
gh pr list

# List PRs by state
gh pr list --state closed
gh pr list --state merged

# View PR
gh pr view 123

# View PR in browser
gh pr view 123 --web

# Check PR status
gh pr status

# Checkout PR locally
gh pr checkout 123

# Review PR
gh pr review 123 --approve
gh pr review 123 --comment --body "LGTM"
gh pr review 123 --request-changes --body "Needs work"

# Merge PR
gh pr merge 123 --squash
gh pr merge 123 --merge
gh pr merge 123 --rebase

# Close PR
gh pr close 123

# Reopen PR
gh pr reopen 123

# View PR diff
gh pr diff 123

# View PR checks
gh pr checks 123
```

**Issues:**
```bash
# Create issue
gh issue create --title "Bug: app crashes" --body "Steps to reproduce..."

# Create with labels
gh issue create --title "Feature request" --label "enhancement"

# List issues
gh issue list

# List open issues assigned to me
gh issue list --assignee @me --state open

# View issue
gh issue view 456

# View in browser
gh issue view 456 --web

# Comment on issue
gh issue comment 456 --body "Working on this"

# Close issue
gh issue close 456

# Reopen issue
gh issue reopen 456
```

**Repositories:**
```bash
# Clone repo
gh repo clone owner/repo

# Create repo
gh repo create my-project --public
gh repo create my-project --private

# Fork repo
gh repo fork owner/repo

# View repo
gh repo view
gh repo view owner/repo

# View in browser
gh repo view --web
```

**Workflows (GitHub Actions):**
```bash
# List workflows
gh workflow list

# View workflow runs
gh run list

# View specific run
gh run view 12345

# Watch run
gh run watch 12345

# Re-run workflow
gh run rerun 12345
```

### shellcheck - Shell Script Linter

**Basic Syntax:** `shellcheck [options] <script>`

**Common Options:**
- `-S, --severity <level>` - Minimum severity (error, warning, info, style)
- `-f, --format <format>` - Output format (tty, gcc, json, checkstyle)
- `-e, --exclude <code>` - Exclude specific check codes
- `-s, --shell <shell>` - Specify shell dialect (bash, sh, dash, ksh)
- `-x, --external-sources` - Follow source statements

**Examples:**
```bash
# Basic linting
shellcheck script.sh

# Lint all scripts in directory
fd -e sh -x shellcheck

# Specific severity level
shellcheck -S warning script.sh
shellcheck -S error script.sh

# Output as JSON
shellcheck -f json script.sh

# Exclude specific checks
shellcheck -e SC2086 -e SC2034 script.sh

# Check specific shell dialect
shellcheck -s bash script.sh

# Follow sourced files
shellcheck -x main.sh

# List all check codes
shellcheck --list-optional

# Show specific check documentation
shellcheck --wiki-link-count=3 SC2086
```

**Common Check Codes:**
- `SC2086` - Quote variables to prevent word splitting
- `SC2034` - Variable appears unused
- `SC2154` - Variable referenced but not assigned
- `SC2164` - Use `cd ... || exit` for safety
- `SC2046` - Quote to prevent word splitting
- `SC2006` - Use `$(...)` instead of backticks

**Disable Checks in Script:**
```bash
# Disable specific check for whole file
# shellcheck disable=SC2086
echo $var

# Disable for one line
# shellcheck disable=SC2086
echo $var  # This line only

# Disable multiple checks
# shellcheck disable=SC2086,SC2034
echo $var
```

### tokei - Code Statistics

**Basic Syntax:** `tokei [options] [path]`

**Common Options:**
- `-s, --sort <column>` - Sort by column (files, lines, code, comments, blanks)
- `-t, --type <types>` - Filter by language types
- `-e, --exclude <path>` - Exclude paths
- `-o, --output <format>` - Output format (json, yaml)
- `-f, --files` - Show individual files

**Examples:**
```bash
# Basic statistics
tokei .

# Sort by lines of code
tokei . --sort lines
tokei . --sort code

# Specific languages
tokei . -t TypeScript,JavaScript
tokei . -t Python,Rust

# Exclude directories
tokei . -e dist -e node_modules

# Show individual files
tokei . --files

# JSON output
tokei . -o json

# JSON output with jq processing
tokei . -o json | jq '.TypeScript.code'

# Compare two directories
diff <(tokei project1 -o json) <(tokei project2 -o json)

# Track code growth over time
git log --reverse --format=%H | while read hash; do
  git checkout -q $hash
  tokei . -o json | jq -r ".Total.code"
done
```

### sd - Find & Replace

**Basic Syntax:** `sd [options] <find> <replacement> [files]`

**Common Options:**
- `-p, --preview` - Preview changes without applying
- `-s, --string-mode` - Treat expressions as strings (not regex)
- `-f, --flags <flags>` - Regex flags (i for case-insensitive)

**Examples:**
```bash
# Simple replacement in file
sd 'old_function' 'new_function' src/app.ts

# Preview changes (dry run)
sd 'console.log' 'logger.debug' src/app.ts -p

# Replace in multiple files
sd 'old' 'new' src/*.ts

# Use with fd for recursive replacement
fd -e ts -x sd 'old' 'new'

# Case-insensitive
sd -f i 'ERROR' 'Error' log.txt

# String mode (no regex)
sd -s '.' '-' filenames.txt

# Regex replacement
sd '(\w+)@example.com' '$1@newdomain.com' contacts.txt

# Multiple replacements
sd 'foo' 'bar' file.txt && sd 'baz' 'qux' file.txt

# Replace in stdin
echo "hello world" | sd 'world' 'universe'
```

### watchexec - File Watcher

**Basic Syntax:** `watchexec [options] -- <command>`

**Common Options:**
- `-w, --watch <path>` - Watch specific path
- `-e, --exts <extensions>` - Filter by extensions
- `-i, --ignore <pattern>` - Ignore pattern
- `-c, --clear` - Clear screen before command
- `-r, --restart` - Restart long-running process
- `--poll <interval>` - Use polling instead of native events

**Examples:**
```bash
# Run tests on TypeScript file changes
watchexec -e ts,tsx -- npm test

# Clear screen before running
watchexec -c -e js -- node script.js

# Watch specific directory
watchexec -w src -e ts -- npm test

# Ignore directories
watchexec -i "dist/*" -i "node_modules/*" -e ts -- npm run build

# Restart server on change
watchexec -r -e ts -- npm run dev

# Run multiple commands
watchexec -e ts -- "npm run lint && npm test"

# Custom debounce (wait 2s after last change)
watchexec -e ts --debounce 2000 -- npm test

# Use polling (for network drives)
watchexec --poll 1000 -e ts -- npm test

# Watch and use changed file path
watchexec -e ts -- echo "Changed: {}"
```

**Use Cases:**
```bash
# Development: rebuild on change
watchexec -w src -e ts -- npm run build

# Testing: run tests on save
watchexec -e ts,tsx -- npm test

# Linting: check on save
watchexec -e ts -- npm run lint

# Documentation: rebuild docs
watchexec -w docs -e md -- mkdocs build

# Docker: rebuild container
watchexec -w Dockerfile -- docker build -t myapp .
```

### hyperfine - Benchmarking

**Basic Syntax:** `hyperfine [options] '<command>' [more commands...]`

**Common Options:**
- `-w, --warmup <num>` - Warmup runs before measurement
- `-m, --min-runs <num>` - Minimum number of runs
- `-M, --max-runs <num>` - Maximum number of runs
- `--export-json <file>` - Export results to JSON
- `--export-markdown <file>` - Export results to Markdown
- `-p, --parameter-scan <name> <min> <max>` - Parameter sweep

**Examples:**
```bash
# Simple benchmark
hyperfine "npm test"

# Compare two commands
hyperfine "npm test" "jest --coverage"

# Warmup runs
hyperfine --warmup 3 "node script.js"

# Control number of runs
hyperfine --min-runs 10 --max-runs 100 "command"

# Export to JSON
hyperfine --export-json results.json "npm test"

# Export to Markdown table
hyperfine --export-markdown table.md "cmd1" "cmd2"

# Parameter sweeps
hyperfine --parameter-scan threads 1 8 "node --max-old-space-size={threads}00 script.js"

# Prepare commands (run before each benchmark)
hyperfine --prepare "rm -rf cache" "build-with-cache"

# Shell-less execution (faster)
hyperfine --shell=none "./binary"

# Compare algorithms
hyperfine "sort file.txt" "sort -n file.txt"

# Compare build tools
hyperfine --warmup 1 "npm run build" "pnpm run build" "yarn build"
```

**Use Cases:**
```bash
# Compare test runners
hyperfine --warmup 2 "jest" "vitest" "mocha"

# Optimize script
hyperfine "python script.py" "pypy script.py"

# Compare compression
hyperfine "gzip file.txt" "bzip2 file.txt" "xz file.txt"

# Database query optimization
hyperfine --warmup 1 "psql -f query1.sql" "psql -f query2.sql"
```

### difftastic - Structural Diff

**Basic Syntax:** `difft [options] <file1> <file2>`

**Common Options:**
- `--color <when>` - Colorize output (always, auto, never)
- `--display <mode>` - Display mode (side-by-side, inline)
- `--width <num>` - Terminal width
- `--language <lang>` - Override language detection

**Examples:**
```bash
# Compare two files
difft file1.ts file2.ts

# Use with git
GIT_EXTERNAL_DIFF=difft git diff

# Configure as git difftool
git config diff.external difft

# Or use as difftool
git config difftool.difftastic.cmd 'difft "$LOCAL" "$REMOTE"'
git difftool --tool=difftastic

# Compare branches
GIT_EXTERNAL_DIFF=difft git diff main..feature

# Side-by-side display
difft --display side-by-side file1.ts file2.ts

# Inline display
difft --display inline file1.ts file2.ts

# Override language
difft --language rust file1.txt file2.txt

# Specific width
difft --width 120 file1.ts file2.ts

# No color
difft --color never file1.ts file2.ts
```

**Configuration in ~/.gitconfig:**
```toml
[diff]
    tool = difftastic
    external = difft

[difftool]
    prompt = false

[difftool "difftastic"]
    cmd = difft "$LOCAL" "$REMOTE"

[pager]
    difftool = true
```

**Advantages over git-delta:**
- AST-aware (understands code structure)
- Better for refactoring reviews
- Shows moved code blocks
- Language-specific parsing

## Updated Common Workflows

### YAML Configuration Management
```bash
# Update docker-compose service
yq eval '.services.app.image = "node:20"' -i docker-compose.yml

# Add environment variable
yq eval '.services.app.environment.NODE_ENV = "production"' -i docker-compose.yml

# Update GitHub Actions
yq eval '.jobs.test.runs-on = "ubuntu-22.04"' -i .github/workflows/ci.yml

# Merge configs
yq eval-all 'select(fileIndex == 0) * select(fileIndex == 1)' base.yaml env.yaml > config.yaml
```

### Code Quality Workflow
```bash
# 1. Analyze codebase
tokei . --sort lines

# 2. Find issues
rg "TODO" -n
rg "FIXME" -n

# 3. Validate shell scripts
fd -e sh -x shellcheck

# 4. Run tests with benchmarking
hyperfine --warmup 1 "npm test"

# 5. Set up file watching for development
watchexec -e ts,tsx -- npm test
```

### GitHub PR Workflow
```bash
# 1. Create feature branch
git checkout -b feature/new-feature

# 2. Make changes and commit
sd 'old_function' 'new_function' src/*.ts
git add .
git commit -m "refactor: rename function"

# 3. Review diff
GIT_EXTERNAL_DIFF=difft git diff main..feature

# 4. Push and create PR
git push -u origin feature/new-feature
gh pr create --fill

# 5. Check PR status
gh pr status

# 6. Merge when ready
gh pr merge --squash
```

### Performance Optimization Workflow
```bash
# 1. Baseline benchmark
hyperfine --warmup 3 "npm test" --export-json baseline.json

# 2. Make optimization
sd 'slow_function' 'fast_function' src/*.ts

# 3. Compare performance
hyperfine --warmup 3 "npm test" --export-json optimized.json

# 4. Analyze results
jq -s '.[0].results[0].mean - .[1].results[0].mean' baseline.json optimized.json
```
