---
name: "find-skills"
description: "Discovers, searches, and installs skills from multiple AI agent skill marketplaces (400K+ skills) using the SkillKit CLI. Supports browsing official partner collections (Anthropic, Vercel, Supabase, Stripe, and more) and community repositories, searching by domain or technology, and installing specific skills from GitHub. Use when the user wants to find, browse, or install new agent skills, plugins, extensions, or add-ons; asks 'is there a skill for X' or 'find a skill for X'; wants to explore a skill store or marketplace; needs to extend agent capabilities in areas like React, testing, DevOps, security, or APIs; or says 'browse skills', 'search skill marketplace', 'install a skill', or 'what skills are available'."
version: "1.0.0"
tags: ["meta", "discovery", "marketplace", "skills"]
---

# Find Skills

Universal skill discovery across all AI agent skill marketplaces.

## When to Use

Use this skill when the user:
- Asks "how do I do X" where X might have an existing skill
- Says "find a skill for X" or "is there a skill that can..."
- Wants to extend agent capabilities with specialized knowledge
- Mentions a domain (testing, deployment, design, security, etc.)

## SkillKit CLI Commands

```bash
# Search skills
npx skillkit@latest find <query>

# Install from GitHub
npx skillkit@latest install <owner/repo>

# Browse TUI marketplace
npx skillkit@latest marketplace

# List installed skills
npx skillkit@latest list

# Get recommendations based on your project
npx skillkit@latest recommend
```

## Skill Sources (400K+ skills)

### Official Partners
| Source | Install |
|--------|---------|
| Anthropic | `npx skillkit@latest install anthropics/skills` |
| Vercel | `npx skillkit@latest install vercel-labs/agent-skills` |
| Expo | `npx skillkit@latest install expo/skills` |
| Remotion | `npx skillkit@latest install remotion-dev/skills` |
| Supabase | `npx skillkit@latest install supabase/agent-skills` |
| Stripe | `npx skillkit@latest install stripe/ai` |

### Community Collections
| Source | Focus |
|--------|-------|
| `trailofbits/skills` | Security, auditing |
| `obra/superpowers` | TDD, workflow |
| `wshobson/agents` | Dev patterns |
| `ComposioHQ/awesome-claude-skills` | Curated collection |
| `langgenius/dify` | AI platform |
| `better-auth/skills` | Authentication |
| `elysiajs/skills` | Bun/ElysiaJS |
| `rohitg00/kubectl-mcp-server` | Kubernetes MCP |

## How to Help Users

### Step 1: Understand the Need
Identify:
1. Domain (React, testing, DevOps, security, etc.)
2. Specific task (writing tests, deployment, code review)
3. Technology stack

### Step 2: Search for Skills

Run search with relevant keywords:
```bash
npx skillkit@latest find "react testing"
npx skillkit@latest find "kubernetes"
npx skillkit@latest find "security audit"
```

### Step 3: Present Results

When you find skills, show:
1. Skill name and description
2. The install command
3. Source repository

Example response:
```
Found: "React Best Practices" from Vercel Labs
- React and Next.js patterns from Vercel Engineering

Install:
npx skillkit@latest install vercel-labs/agent-skills
```

### Step 4: Install

Install for the user:
```bash
npx skillkit@latest install <owner/repo>
```

Or install specific skill (non-interactive):
```bash
npx skillkit@latest install owner/repo --skills skill-name
npx skillkit@latest install anthropics/skills --skills frontend-design
npx skillkit@latest install vercel-labs/agent-skills -s react-best-practices
```

## Common Searches

| Need | Search Query |
|------|--------------|
| React patterns | `npx skillkit@latest find react` |
| Testing | `npx skillkit@latest find testing jest` |
| TypeScript | `npx skillkit@latest find typescript` |
| DevOps | `npx skillkit@latest find docker kubernetes` |
| Security | `npx skillkit@latest find security` |
| API design | `npx skillkit@latest find api rest graphql` |
| Mobile | `npx skillkit@latest find react-native expo` |
| Database | `npx skillkit@latest find postgres prisma` |

## When No Skills Found

If no matching skill exists:
1. Offer to help directly with your capabilities
2. Suggest creating a custom skill:
   ```bash
   npx skillkit@latest init my-skill
   ```
3. Recommend publishing to share with others:
   ```bash
   npx skillkit@latest publish
   ```

## Browse Online

- Website: https://agentskills.com
- GitHub: https://github.com/rohitg00/skillkit

## Important Notes

- Use `owner/repo` format, NOT full URLs
- Use `--skills` (plural) or `-s` flag for specific skills
- Add `@latest` to npx for latest version: `npx skillkit@latest`
