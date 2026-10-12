#!/bin/bash
# scan-project.sh - Analyzes project structure for init-roadmap skill
# Usage: ./scan-project.sh [project-root]
#
# Outputs a structured summary of the project for roadmap planning.

PROJECT_ROOT="${1:-.}"

if [ ! -d "$PROJECT_ROOT" ]; then
  echo "ERROR: Directory '$PROJECT_ROOT' not found"
  exit 1
fi

cd "$PROJECT_ROOT" || exit 1

# Colors (disabled if not a terminal)
if [ -t 1 ]; then
  BOLD='\033[1m'
  BLUE='\033[0;34m'
  YELLOW='\033[1;33m'
  GREEN='\033[0;32m'
  NC='\033[0m'
else
  BOLD='' BLUE='' YELLOW='' GREEN='' NC=''
fi

echo -e "${BOLD}=== PROJECT SCAN ===${NC}"
echo ""

# 1. Basic info
echo -e "${BLUE}[PROJECT]${NC}"
echo "ROOT=$(pwd)"
echo "NAME=$(basename "$(pwd)")"
echo ""

# 2. Detect language/framework
echo -e "${BLUE}[FRAMEWORK]${NC}"
[ -f "package.json" ] && echo "NODEJS=true" && (grep -q '"next"' package.json 2>/dev/null && echo "FRAMEWORK=nextjs")
[ -f "package.json" ] && (grep -q '"react"' package.json 2>/dev/null && echo "REACT=true")
[ -f "package.json" ] && (grep -q '"vue"' package.json 2>/dev/null && echo "VUE=true")
[ -f "package.json" ] && (grep -q '"svelte"' package.json 2>/dev/null && echo "SVELTE=true")
[ -f "package.json" ] && (grep -q '"express"' package.json 2>/dev/null && echo "EXPRESS=true")
[ -f "tsconfig.json" ] && echo "TYPESCRIPT=true"
[ -f "requirements.txt" ] || [ -f "pyproject.toml" ] || [ -f "setup.py" ] && echo "PYTHON=true"
[ -f "go.mod" ] && echo "GO=true"
[ -f "Cargo.toml" ] && echo "RUST=true"
[ -f "pom.xml" ] || [ -f "build.gradle" ] && echo "JAVA=true"
[ -f "Gemfile" ] && echo "RUBY=true"
[ -f "composer.json" ] && echo "PHP=true"
echo ""

# 3. File count by extension
echo -e "${BLUE}[FILES]${NC}"
echo "TOTAL=$(find . -type f -not -path './.git/*' -not -path './node_modules/*' -not -path './.next/*' -not -path './dist/*' -not -path './build/*' -not -path './__pycache__/*' -not -path './venv/*' -not -path './.venv/*' | wc -l | tr -d ' ')"

# Count by extension (top 10)
find . -type f -not -path './.git/*' -not -path './node_modules/*' -not -path './.next/*' -not -path './dist/*' -not -path './build/*' -not -path './__pycache__/*' -not -path './venv/*' -not -path './.venv/*' \
  | sed 's/.*\.//' | sort | uniq -c | sort -rn | head -10 | while read -r count ext; do
    echo "  .${ext}=${count}"
  done
echo ""

# 4. Directory structure (depth 2)
echo -e "${BLUE}[STRUCTURE]${NC}"
find . -maxdepth 2 -type d \
  -not -path './.git*' \
  -not -path './node_modules*' \
  -not -path './.next*' \
  -not -path './dist*' \
  -not -path './build*' \
  -not -path './__pycache__*' \
  -not -path './venv*' \
  -not -path './.venv*' \
  | sort | head -40
echo ""

# 5. Config files
echo -e "${BLUE}[CONFIG]${NC}"
[ -f ".eslintrc" ] || [ -f ".eslintrc.js" ] || [ -f ".eslintrc.json" ] || [ -f "eslint.config.js" ] || [ -f "eslint.config.mjs" ] && echo "ESLINT=true"
[ -f ".prettierrc" ] || [ -f ".prettierrc.js" ] || [ -f "prettier.config.js" ] && echo "PRETTIER=true"
[ -f "jest.config.js" ] || [ -f "jest.config.ts" ] || [ -f "jest.config.mjs" ] && echo "JEST=true"
[ -f "vitest.config.ts" ] || [ -f "vitest.config.js" ] && echo "VITEST=true"
[ -f "cypress.config.ts" ] || [ -f "cypress.config.js" ] && echo "CYPRESS=true"
[ -f "playwright.config.ts" ] && echo "PLAYWRIGHT=true"
[ -f ".env" ] && echo "DOTENV=true"
[ -f ".env.example" ] && echo "DOTENV_EXAMPLE=true"
[ -f "docker-compose.yml" ] || [ -f "docker-compose.yaml" ] && echo "DOCKER_COMPOSE=true"
[ -f "Dockerfile" ] && echo "DOCKERFILE=true"
echo ""

# 6. CLAUDE.md status
echo -e "${BLUE}[CLAUDE_MD]${NC}"
if [ -f "CLAUDE.md" ]; then
  echo "EXISTS=true"
  grep -c '^\- \[ \]' CLAUDE.md 2>/dev/null && echo "UNCHECKED_TASKS=$(grep -c '^\- \[ \]' CLAUDE.md)"
  grep -c '^\- \[x\]' CLAUDE.md 2>/dev/null && echo "CHECKED_TASKS=$(grep -c '^\- \[x\]' CLAUDE.md)"
  grep -q '## Roadmap' CLAUDE.md && echo "HAS_ROADMAP=true" || echo "HAS_ROADMAP=false"
else
  echo "EXISTS=false"
fi
echo ""

# 7. Git status
echo -e "${BLUE}[GIT]${NC}"
if [ -d ".git" ]; then
  echo "GIT=true"
  echo "BRANCH=$(git branch --show-current 2>/dev/null)"
  echo "CLEAN=$(git status --porcelain 2>/dev/null | wc -l | tr -d ' ')"
  echo "RECENT_COMMITS=$(git log --oneline -5 2>/dev/null)"
else
  echo "GIT=false"
fi
echo ""

# 8. TypeScript-specific: count `any` types (if TS project)
if [ -f "tsconfig.json" ]; then
  echo -e "${BLUE}[TYPESCRIPT_ANALYSIS]${NC}"
  ANY_COUNT=$(grep -r --include="*.ts" --include="*.tsx" -l ': any' . \
    --exclude-dir=node_modules --exclude-dir=dist --exclude-dir=build --exclude-dir=.next 2>/dev/null | wc -l | tr -d ' ')
  echo "FILES_WITH_ANY=${ANY_COUNT}"

  if [ "$ANY_COUNT" -gt 0 ]; then
    echo "TOP_FILES_WITH_ANY:"
    grep -r --include="*.ts" --include="*.tsx" -c ': any' . \
      --exclude-dir=node_modules --exclude-dir=dist --exclude-dir=build --exclude-dir=.next 2>/dev/null \
      | grep -v ':0$' | sort -t: -k2 -rn | head -10 | while IFS=: read -r file count; do
        echo "  ${file}=${count}"
      done
  fi
  echo ""
fi

# 9. Python-specific: check for type hints
if [ -f "requirements.txt" ] || [ -f "pyproject.toml" ]; then
  echo -e "${BLUE}[PYTHON_ANALYSIS]${NC}"
  PY_COUNT=$(find . -name "*.py" -not -path './venv/*' -not -path './.venv/*' -not -path './__pycache__/*' 2>/dev/null | wc -l | tr -d ' ')
  echo "PYTHON_FILES=${PY_COUNT}"

  # Files without type hints (rough heuristic: no -> in function defs)
  NO_HINTS=$(grep -rL --include="*.py" '\->' . --exclude-dir=venv --exclude-dir=.venv --exclude-dir=__pycache__ 2>/dev/null | wc -l | tr -d ' ')
  echo "FILES_WITHOUT_TYPE_HINTS=${NO_HINTS}"
  echo ""
fi

echo -e "${GREEN}=== SCAN COMPLETE ===${NC}"
