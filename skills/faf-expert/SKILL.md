---
name: faf-expert
description: Expert in .faf (Foundational AI-context Format) files for persistent project context. Use when working with .faf files, project DNA, CLAUDE.md bi-sync, faf-cli commands, MCP server configuration, or AI-readiness scoring (0-100%). Updated for v3.3.7.
license: Complete terms in LICENSE.txt
---

# FAF Expert - Project DNA Specialist

## What is .faf?

`.faf` is the universal format for persistent AI project context - "Project DNA ✨ for ANY AI".

**Core Concepts:**
- **Foundational AI-context Format** - YAML-based project context file
- **Persistent Context** - Survives across sessions, tools, and AI assistants
- **Universal** - Works with Claude, ChatGPT, Gemini, Cursor, any AI
- **Measurable** - Championship scoring system (0-100% AI-readiness)
- **Official Anthropic MCP Steward** - PR #2759 MERGED

## When to Use This Skill

Activate this skill when:
- Creating or updating `.faf` files
- Working with `CLAUDE.md` files
- Running `faf` CLI commands (init, auto, score, formats, bi-sync)
- Scoring project AI-readiness
- Setting up MCP server (claude-faf-mcp)
- Configuring tool visibility (v2.8.0+)
- Discussing project context or documentation

## Key Files

- **`.faf`** - YAML format, machine-readable project context
- **`CLAUDE.md`** - Markdown format, human-readable project guide
- **Bi-Sync** - `.faf ↔ CLAUDE.md` kept in sync automatically
- **`project.faf`** - v1.2.0 standard naming

## Common Commands

### faf-cli Commands
```bash
faf init              # Create .faf from project
faf auto              # Auto-detect stack and create .faf
faf score             # Rate AI-readiness (0-100%)
faf formats           # List 153+ supported formats
faf bi-sync           # Sync .faf ↔ CLAUDE.md
faf status            # Check project AI-readiness
faf validate          # Validate .faf structure
faf doctor            # Diagnose and fix issues
faf migrate           # Migrate to latest format
```

### MCP Tools (claude-faf-mcp v2.8.0+)

**v2.8.0 introduces Tool Visibility System:**
- **21 Core Tools** (default) - Essential workflow
- **51 Total Tools** (opt-in) - All features

**Configuration:**
```json
{
  "mcpServers": {
    "faf": {
      "command": "npx",
      "args": ["-y", "claude-faf-mcp@latest"],
      "env": {
        "FAF_MCP_SHOW_ADVANCED": "false"
      }
    }
  }
}
```

**Core Tools (21):**
- Essential Workflow: `faf`, `faf_auto`, `faf_init`, `faf_innit`, `faf_status`
- Quality: `faf_score`, `faf_validate`, `faf_doctor`, `faf_audit`
- Intelligence: `faf_formats`, `faf_stacks`, `faf_skills`, `faf_install_skill`
- Sync: `faf_sync`, `faf_bi_sync`, `faf_update`, `faf_migrate`
- AI: `faf_chat`, `faf_enhance`
- Help: `faf_index`, `faf_faq`, `faf_about`

**Advanced Tools (30+):**
Set `FAF_MCP_SHOW_ADVANCED: "true"` to enable:
- Display variants: `faf_display`, `faf_show`, `faf_check`
- Trust system: `faf_trust`, `faf_trust_confidence`, `faf_trust_garage`
- File operations: `faf_read`, `faf_write`, `faf_list`, `faf_exists`, etc.
- DNA tracking: `faf_dna`, `faf_log`, `faf_auth`, `faf_recover`
- Utilities: `faf_choose`, `faf_clear`, `faf_share`, `faf_credit`

## AI-Readiness Scoring

**Championship Tiers:**
- 🏆 **95-100%** - Championship (Gold)
- 🥇 **85-94%** - Podium (Silver)
- 🥈 **70-84%** - Points (Bronze)
- 🥉 **55-69%** - Midfield
- 🟢 **40-54%** - Backmarker
- 🟡 **25-39%** - Struggling
- 🔴 **10-24%** - Critical
- 🤍 **0-9%** - DNF (Did Not Finish)

**Target:** 85%+ for production projects

## .faf File Structure

```yaml
# Basic .faf structure
format: typescript-nextjs
language: typescript
framework: nextjs
version: "14.0.0"

structure:
  - src/
  - components/
  - pages/

dependencies:
  react: "^18.0.0"
  next: "^14.0.0"

testing: jest
deployment: vercel

# v1.2.0+ additions
project_name: "My Project"
ai_readiness_score: 87
```

## Best Practices

1. **Start with `faf auto`** - Let it detect your stack
2. **Review and refine** - Auto-detection is 85% accurate, tweak as needed
3. **Run `faf score`** - Target 85%+ for championship context
4. **Use `faf bi-sync`** - Keep .faf and CLAUDE.md in sync
5. **Update regularly** - As project evolves, update context
6. **Use core tools first** - Advanced tools are opt-in for specific needs

## The FAF Family

**6 Championship Integrations:**
- React (20M/week npm downloads) 🏆
- TypeScript (40M/week) 🏆
- Next.js (5M/week) 🏆
- Vite (9M/week) 🥇
- Svelte (400K/week) 🥇
- n8n (401K/week - TURBO only) 🥇

## Installation

### faf-cli (npm)
```bash
npm install -g faf-cli
```

### faf-cli (Homebrew)
```bash
brew install faf-cli
```

### claude-faf-mcp (MCP Server)
Add to `~/Library/Application Support/Claude/claude_desktop_config.json`:
```json
{
  "mcpServers": {
    "faf": {
      "command": "npx",
      "args": ["-y", "claude-faf-mcp@latest"]
    }
  }
}
```

**For advanced tools:**
```json
{
  "mcpServers": {
    "faf": {
      "command": "npx",
      "args": ["-y", "claude-faf-mcp@latest"],
      "env": {
        "FAF_MCP_SHOW_ADVANCED": "true"
      }
    }
  }
}
```

## v2.8.0 Tool Visibility System

**Problem Solved:** Reduced cognitive load from 51 tools to 21 core tools.

**How It Works:**
- **Default:** Shows 21 essential tools
- **Opt-in:** Enable all 51 tools via environment variable
- **Smart Filtering:** Tools categorized by purpose
- **Backward Compatible:** Existing setups continue working

**Categories:**
- `workflow` - Essential commands
- `quality` - Scoring and validation
- `intelligence` - Format/stack detection
- `sync` - Context synchronization
- `ai` - AI enhancement features
- `help` - Documentation
- `trust` - Trust validation
- `file` - File operations
- `utility` - Misc tools

**Configuration Priority:**
1. Environment variable (`FAF_MCP_SHOW_ADVANCED`)
2. Config file (`~/.fafrc`)
3. Default (core only)

## Philosophy

**The Noodle Philosophy 🍜**
- YAML noodles for AI (machine-readable)
- Converts to markdown/TXT for humans (human-readable)
- Interconnected context, not flat data

**Format-First**
- The format is the foundation
- Without .faf, there is no universal context
- Format-driven architecture

**Official Stewardship**
- Anthropic-approved MCP server (PR #2759 MERGED)
- Account Managers for all things .FAF in Anthropic ecosystem
- Governance responsibility for format specification

## Brand Values

- **NO BS ZONE** - Only real stats, verified claims
- **Championship Standards** - <50ms performance, 1,000+ tests
- **Free Forever** - MIT license, open source
- **Trust is Everything** - Built on credibility
- **Professional, Boring, Trusted** - F1-grade engineering

## Stats (Real, Verified - December 2025)

- **18,000+ total downloads** (CLI + MCP combined)
- **6,700+ MCP downloads** (weekly: 800+)
- **6,500+ CLI downloads**
- **79 tests passing** (57 MCP + 22 visibility)
- **153+ formats validated** (TURBO-CAT engine)
- **<10ms tool filtering** (5x better than 50ms target)
- **Zero regressions** in v2.8.0 release
- **WJTTC Gold Certified** - F1-inspired testing standards
- **Anthropic-approved** MCP server (Official steward)

## Version History

- **v3.2.6** - faf-cli latest
- **v3.3.7** - claude-faf-mcp latest (TYPE_DEFINITIONS parity)
- **v1.2.0** - faf-mcp universal

## Resources

- **Website:** https://faf.one
- **CLI npm:** https://npmjs.com/package/faf-cli
- **MCP npm:** https://npmjs.com/package/claude-faf-mcp
- **GitHub:** https://github.com/Wolfe-Jam/faf-cli
- **Homebrew:** `brew install faf-cli`
- **Chrome Extension:** Chrome Web Store (Google approved)

## Testing Standards

**WJTTC (WolfeJam Technical & Testing Center)**
- F1-Inspired testing methodology
- 3 Tiers: Brake Systems, Engine Systems, Aerodynamics
- Philosophy: "We break things so others never have to know they were broken"
- All tests reported and documented
- Gold certification for production releases

## Troubleshooting

### MCP Server Not Loading
```bash
# Check logs
tail -f ~/Library/Logs/Claude/mcp-server-claude-faf-mcp.log

# Verify config
cat ~/Library/Application\ Support/Claude/claude_desktop_config.json

# Test locally
node /path/to/claude-faf-mcp/dist/src/index.js
```

### Tool Count Verification
```bash
# Should show 21 core tools (default)
# Or 51 tools (advanced mode)
# Check console output when MCP loads
```

### CLI Not Found
```bash
# Install globally
npm install -g faf-cli

# Or via Homebrew
brew install faf-cli

# Verify installation
faf --version
```

## Advanced Usage

### Custom Config File
Create `~/.fafrc`:
```json
{
  "showAdvanced": true
}
```

Or key=value format:
```
FAF_SHOW_ADVANCED=true
```

### Local Development
```bash
# Use local build
{
  "mcpServers": {
    "faf": {
      "command": "node",
      "args": ["/path/to/claude-faf-mcp/dist/src/index.js"],
      "env": {
        "FAF_MCP_SHOW_ADVANCED": "false"
      }
    }
  }
}
```

---

## Skill Control

**To disable this skill temporarily:**
```bash
# Rename directory to disable
mv ~/.claude/skills/faf-expert ~/.claude/skills/faf-expert.disabled
```

**To re-enable:**
```bash
# Rename back to enable
mv ~/.claude/skills/faf-expert.disabled ~/.claude/skills/faf-expert
```

**Or just delete the directory to remove completely.**

---

## How to Get This Skill

**Option 1: Manual Installation**
1. Copy this SKILL.md file
2. Create directory: `~/.claude/skills/faf-expert/`
3. Save as: `~/.claude/skills/faf-expert/SKILL.md`
4. Restart Claude Code

**Option 2: Git Clone (if published)**
```bash
# Coming soon - published skills repository
git clone [skills-repo] ~/.claude/skills/faf-expert
```

**Option 3: From FAF CLI (future)**
```bash
# Planned feature
faf skill install faf-expert
```

---

*Made with 🧡 by wolfejam.dev*
*Official Anthropic MCP Steward*
*Championship Edition v3.3.7* 🏎️✨
*IANA-Registered Format: application/vnd.faf+yaml (Oct 30, 2025)*
