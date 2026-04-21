# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Overview

This repository contains the **SEAL Security Knowledge Graph** - a collection of 27 security domain skills for AI agents based on the [Security Alliance Frameworks](https://github.com/security-alliance/frameworks).

**Focused exclusively on Web3/blockchain security domains:** incident response, wallet security, opsec, infrastructure hardening, threat modeling, and more.

## Architecture

### Two Skill Collections

1. **`advisors/`** - SEAL security advisor skills (concise, chat-oriented):
   - Core advisor skills: `wallet-security-advisor`, `incident-response-advisor`, `infrastructure-security-advisor`, `opsec-advisor`, etc.
   - Special utilities: `seal-coach` (security coaching and assessments), `skill-sync` (track upstream changes)

2. **Root-level security domains** - Comprehensive framework skills (detailed, certification-oriented):
   - `incident-management/`, `wallet-security/`, `multisig-for-protocols/`, `devsecops/`, `certs/`, etc.
   - 27 domains total, each with extensive reference materials

3. **Cross-domain navigation**: `INDEX.md` contains the trigger table that routes security questions to appropriate domain skills

### Skill Structure

Every skill follows the Agent Skills Spec (see `spec/agent-skills-spec.md` and `spec/skill-authoring.md`):

```
skill-name/
├── SKILL.md              # Required: YAML frontmatter + instructions
├── scripts/              # Optional: executable Python/Bash tools
├── references/           # Optional: docs loaded into context as needed
└── assets/               # Optional: templates, fonts, images used in output
```

**Key files:**
- `SKILL.md` - Only file required. YAML frontmatter (name, description) determines when skill triggers. Body contains instructions (loaded after triggering).
- Progressive disclosure: Keep SKILL.md < 500 lines. Split detailed content into `references/` files.
- Scripts in `scripts/` provide deterministic tools (validated by executing them).

## Common Commands

### SEAL Security Skill Synchronization

Check which skills need updating based on upstream framework changes (requires frameworks repo):
```bash
# From frameworks repository
git log --oneline --since="30 days ago" -- docs/pages/
git diff --name-only <last-sync-commit>..HEAD -- docs/pages/ | cut -d'/' -f3 | sort -u
```

See `advisors/skill-sync/SKILL.md` for complete sync workflow and skill-to-source mapping.

### Optional: Add Anthropic Document Skills

If you need document generation (Excel, PowerPoint, PDF), install Anthropic's skills separately:

```bash
# Install SEAL security skills (this repo)
git clone https://github.com/yourusername/seal-skills ~/.claude/skills/seal

# Optional: Add Anthropic document skills
git clone https://github.com/anthropics/skills ~/.claude/skills/anthropic
```

SEAL skills focus purely on security knowledge. Document generation is available from Anthropic's upstream repository.

## Skill Development Guidelines

When creating or editing skills, follow these principles from `skills/skill-creator/SKILL.md`:

### 1. Concise is Key
- Default assumption: Claude is already smart. Only add context Claude doesn't have.
- Keep SKILL.md body under 500 lines. Split larger content into `references/` files.
- Prefer concise examples over verbose explanations.

### 2. Progressive Disclosure
Three-level loading system:
1. **Metadata (name + description)** - Always in context (~100 words)
2. **SKILL.md body** - Loaded when skill triggers (<5k words)
3. **Bundled resources** - Loaded as needed by Claude

**Important:** Description in YAML frontmatter is the primary triggering mechanism. Include both what the skill does AND specific triggers/contexts for when to use it.

### 3. Set Appropriate Degrees of Freedom
- **High freedom** (text instructions): Multiple valid approaches, context-dependent decisions
- **Medium freedom** (pseudocode/parameterized scripts): Preferred pattern exists, some variation acceptable
- **Low freedom** (specific scripts): Fragile operations, consistency critical, specific sequence required

### 4. Resource Organization
- **`scripts/`**: Executable code for tasks that are repeatedly rewritten or need deterministic reliability. Must be tested by running them.
- **`references/`**: Documentation loaded into context as needed (schemas, APIs, workflows, policies). Avoid duplication with SKILL.md.
- **`assets/`**: Files used in output (templates, fonts, images), not loaded into context.

### 5. Do NOT Create
- README.md, INSTALLATION_GUIDE.md, CHANGELOG.md, or other auxiliary documentation
- Skills should only contain information needed for AI agent execution

## Security and Privacy Considerations

SEAL skills handle **sensitive security data** (security gaps, failed controls, incident details). See `SECURITY.md` for full details.

**Key principle:** Before deploying for any organization, ask: "Are we comfortable with our inference provider seeing this data?"

**Provider trust levels:**
- Local LLM (Ollama, vLLM): No data leaves machine - highest security
- Venice.ai: No retention policy - low risk
- Self-hosted: You control infra - low-medium risk
- Anthropic/Claude/OpenAI: Queries retained - high risk for sensitive data

## Repository-Specific Patterns

### SEAL Coach Pattern
The `seal-coach` skill provides Duolingo-style security training:
- Daily tips rotated across domains
- Readiness assessments (not certifications)
- Hardening plans prioritized by impact/effort
- State tracking in `state-log.json`
- **Important:** Always get explicit approval before creating cron jobs or automations

### Marketplace Configuration
`.claude-plugin/marketplace.json` defines SEAL security skill collections for skill marketplaces and discovery platforms.

### Cross-Domain Navigation
Security skills are interconnected via the trigger table in `INDEX.md`. When working with SEAL skills:
- Load related skills via skill references in YAML frontmatter
- Common cross-cuts: opsec touches everything, governance connects to all operational domains
- Use trigger keywords to route questions to correct domain

## File Naming Conventions
- Skill names: lowercase with hyphens (e.g., `skill-creator`, `wallet-security-advisor`)
- SKILL.md: Always capitalized
- References: kebab-case markdown (e.g., `mcp-best-practices.md`, `testing-patterns.md`)
- Scripts: snake_case Python (e.g., `init_skill.py`, `package_skill.py`)

## Testing Scripts Before Including
Any scripts added to `scripts/` directories must be tested by actually running them. For many similar scripts, test a representative sample to balance thoroughness with efficiency.
