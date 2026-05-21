# Mainframe Super Power (`/mf`)

> AI-powered IBM z/OS mainframe assistant for Claude Code, Cursor, Codex, and 30+ AI agents

[![Agent Skills](https://img.shields.io/badge/Agent%20Skills-Compatible-blue)](https://github.com/anthropics/skills)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## What It Does

Five super powers for anyone working with IBM z/OS mainframes:

| Power | Example | Description |
|-------|---------|-------------|
| **JCL Forge** | `/mf jcl compile cobol` | Generate JCL from natural language |
| **ABEND Doctor** | `/mf abend S0C7` | Decode abend codes with fixes |
| **Message Decoder** | `/mf msg IKJ56703I` | Explain z/OS messages |
| **Screen Whisperer** | `/mf screen` | Explain 3270 terminal screens |
| **Dataset Navigator** | `/mf what is a PDS?` | Understand dataset concepts |

Or just ask: `/mf how do I submit a batch job?`

## Installation

### Claude Code / Cursor / Codex CLI

```bash
# Clone to your personal skills directory
git clone https://github.com/YOUR_USERNAME/mainframe-ai.git
cp -r mainframe-ai/.claude/skills/mf ~/.claude/skills/

# Or for project-specific use
cp -r mainframe-ai/.claude/skills/mf .claude/skills/
```

### Manual Installation

1. Create `~/.claude/skills/mf/` directory
2. Copy `SKILL.md` into it
3. Restart your AI agent

## Usage Examples

### Generate JCL
```
/mf jcl copy dataset MY.INPUT to MY.OUTPUT

/mf jcl compile COBOL program PAYROLL in MY.SOURCE

/mf jcl run program HELLO with input from MY.DATA

/mf jcl delete dataset MY.OLD.FILE
```

### Decode ABENDs
```
/mf abend S0C7
> Data Exception - invalid packed decimal. Check COMP-3 fields...

/mf abend S913
> RACF Not Authorized. Request access via security admin...

/mf my job failed with S0C4, what happened?
```

### Explain Messages
```
/mf msg IKJ56703I
> TSO error - INVALID KEYWORD. The command syntax is wrong...

/mf what does IEF285I mean?
```

### Learn Mainframe Concepts
```
/mf what is JCL?
/mf how do I view job output?
/mf difference between PDS and sequential dataset
/mf what is RACF?
```

## Capabilities

### ABEND Codes Covered

**System Abends:**
- S0C1 (Operation), S0C4 (Protection), S0C7 (Data), S0CB (Division)
- S106, S213, S322, S522, S622, S722
- S806 (Module Not Found), S913 (RACF)
- SB37, SD37, SE37 (Space)

**User Abends:**
- U0001-U4095 with context

### JCL Generation

- Compile jobs (COBOL, PL/I, Assembler, C)
- Dataset operations (copy, delete, rename, allocate)
- Utility programs (IEBGENER, IEBCOPY, IDCAMS, SORT)
- Batch execution with proper JOB/EXEC/DD

### Message Prefixes Decoded

IKJ (TSO), IEF (Allocation), ICH/IRR (RACF), IGD (SMS), IEC (I/O), IST (VTAM), DFH (CICS), DSN (DB2), HASP/IAT (JES), CEE/IGZ (Language Environment), and 50+ more.

## For Mainframe Beginners

This skill assumes **no prior mainframe knowledge**. Ask anything:

- "What is JCL?"
- "How do I log into TSO?"
- "What's the difference between a PDS and a sequential dataset?"
- "Why did my job fail?"
- "How do I see my job output?"

## Compatibility

Works with any AI agent supporting the [Agent Skills](https://github.com/anthropics/skills) specification:

- Claude Code
- Claude.ai
- OpenAI Codex CLI
- Cursor
- Windsurf
- Gemini CLI
- And 30+ more

## File Structure

```
mf/
├── SKILL.md           # Main skill definition
├── README.md          # This file
└── examples/
    ├── jcl-templates.md      # Ready-to-use JCL
    ├── abend-reference.md    # ABEND code guide
    └── message-prefixes.md   # Message prefix reference
```

## Contributing

PRs welcome! Areas for improvement:

- [ ] More JCL templates
- [ ] Additional ABEND codes
- [ ] CICS transaction support
- [ ] DB2 SQL assistance
- [ ] IMS database help

## License

MIT License - Use freely, contribute back!

## Credits

- Mainframe AI project
- Agent Skills spec by Anthropic

---

**Made for the masses** - Because everyone deserves mainframe super powers.
