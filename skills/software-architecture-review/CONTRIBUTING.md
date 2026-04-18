# Contributing: software-architecture-review Skill

## Files in This PR

```
skills/software-architecture-review/
├── SKILL.md                          ← Main skill definition
└── evals/
    ├── evals.json                    ← 3 test cases with 11 assertions
    └── trigger-evals.json            ← 16 description trigger eval queries
```

## Step-by-Step Contribution Workflow

### 1. Fork and clone the repo
```bash
git clone https://github.com/YOUR_USERNAME/skills.git
cd skills
git checkout -b add-software-architecture-review
```

### 2. Copy skill files
```bash
mkdir skills/software-architecture-review
cp SKILL.md skills/software-architecture-review/SKILL.md
mkdir skills/software-architecture-review/evals
cp evals/evals.json skills/software-architecture-review/evals/evals.json
cp evals/trigger-evals.json skills/software-architecture-review/evals/trigger-evals.json
```

### 3. Register in marketplace.json
Open `.claude-plugin/marketplace.json` and add to the `example-skills` plugin's `skills` array:
```json
"./skills/software-architecture-review"
```

### 4. Run description optimizer (optional but recommended)
```bash
# Inside Claude Code with the skills repo open:
python -m scripts.run_loop \
  --eval-set skills/software-architecture-review/evals/trigger-evals.json \
  --skill-path skills/software-architecture-review \
  --model claude-sonnet-4-5 \
  --max-iterations 5 \
  --verbose
```

### 5. Commit and push
```bash
git add skills/software-architecture-review/
git add .claude-plugin/marketplace.json
git commit -m "feat: add software-architecture-review skill

Adds a new Technical category skill for structured architecture reviews.
Covers: design pattern analysis, quality attribute scoring (6 dimensions),
anti-pattern detection (7 structural + 7 Gen AI/RAG specific), ADR generation,
and a dedicated Gen AI/RAG pipeline review module.

Evals: 3 test cases, 11 assertions, 16 description trigger queries."
git push origin add-software-architecture-review
```

### 6. Open Pull Request
- **Title**: `feat: add software-architecture-review skill`
- **Category**: Technical (alongside `mcp-builder`, `webapp-testing`, `frontend-design`)
- **Tag**: `@klazuka` (repo owner: klazuka@anthropic.com)

## PR Description Template
```
## Summary
Adds a new `software-architecture-review` skill to the Technical category.

## What It Does
Performs structured, expert-level software architecture reviews covering:
- 6 architecture styles (Microservices, Event-Driven, Layered, Hexagonal, RAG/GenAI, CQRS)
- Quality attribute scoring across 6 dimensions (Scalability, Security, Observability, Maintainability, Resilience, Cost)
- Anti-pattern detection: 7 structural + 7 Gen AI/RAG-specific patterns
- ADR (Architecture Decision Record) generation with alternatives comparison
- Dedicated Gen AI / RAG pipeline review module (chunking, embeddings, retrieval, Responsible AI)
- LangGraph / multi-agent architecture review checklist

## Gap Filled
None of the existing 12 example skills covers architecture review, design evaluation, or ADR generation.

## Evals
- 3 realistic test cases (REST microservices, healthcare RAG pipeline, event bus ADR)
- 11 assertions (format checks, concept checks, scope checks)
- 16 description trigger queries (8 should-trigger, 8 near-miss should-not-trigger)

## Checklist
- [ ] SKILL.md follows naming convention (lowercase-with-hyphens)
- [ ] Skill registered in `.claude-plugin/marketplace.json`
- [ ] SKILL.md under 500 lines
- [ ] Includes examples section
- [ ] No malware or exploits
- [ ] Description uses "pushy" triggering language per skill-creator guidelines
```
