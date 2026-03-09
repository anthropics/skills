# Generate Claude Files - Complete Skill Package

**Skill ID**: `w3-generate-claude-files`
**Approach**: Prompt-based (not code generation)
**Duration**: 15-60 minutes
**Languages**: Node.js • Python • Go • Java • C# • Ruby • And more!
**Result**: CLAUDE.md + CODEMAP.md + MEMORY.md

---

## 🎯 What Is This Skill?

This skill helps you generate three essential documentation files for **any backend project** (Node.js, Python, Go, Java, C#, etc.):

1. **CLAUDE.md** - Project Constitution
   - Tech stack, coding rules, how to add features

2. **CODEMAP.md** - Codebase Architecture Map
   - Directory structure, request flow, navigation guides

3. **MEMORY.md** - Project Context & Knowledge Base
   - Quick facts, code patterns, gotchas, performance notes

**Key Point**: Uses **prompts and analysis** (minimal code), not automated code generation. **Language-agnostic approach** works for any backend stack.

---

## 📁 Skill Structure

```
w3-generate-claude-files/
├── SKILL.md                          ← Main skill description
├── README.md                         ← This file
└── references/
    ├── HOW_TO_USE_THIS_SKILL.md     ← START HERE (Overview)
    ├── PROMPT_BASED_WORKFLOW.md     ← 4-phase detailed guide
    ├── QUICK_START_PROMPTS.md       ← Copy-paste prompts for Claude
    ├── USAGE.md                     ← Examples & best practices
    ├── CLAUDE.md.template           ← Template reference
    ├── CODEMAP.md.template          ← Template reference
    └── MEMORY.md.template           ← Template reference
```

---

## 🚀 Quick Start

### Option 1: Super Quick (15 min) 🏃

```
1. Open: references/QUICK_START_PROMPTS.md
2. Copy Phase 1 prompt → Paste into Claude
3. Answer questions about your project
4. Copy Phase 2-4 prompts → Generate files
5. Done!
```

### Option 2: Thorough (45-60 min) 📖

```
1. Open: references/PROMPT_BASED_WORKFLOW.md
2. Follow detailed 4-phase guide with templates
3. Answer all questions, fill in examples
4. Generate professional documentation
5. Done!
```

### Option 3: Hybrid (30 min) 🤖

```
1. Do Phase 1 analysis manually (15 min)
2. Use QUICK_START_PROMPTS with Claude (10 min)
3. Review & customize (5 min)
4. Done!
```

### Option 4: Optimized with CLI Tools (20-25 min) ⚡ **Fastest + Token Efficient**

```
Prerequisites: Install codemap, repomix, and mgrep CLI tools

1. Generate project structure with codemap (~3 min)
   codemap --output project-structure.md

2. Generate context with repomix (~5 min)
   repomix --output context.md

3. Extract patterns with mgrep (~3 min)
   mgrep "pattern" src/ > patterns.txt

4. Feed all outputs into Phase 1 analysis (5 min)
5. Generate docs (5-10 min)
6. Done!
```

**Result**: 50% faster + 30% fewer tokens

---

## 📖 Which File Should I Read?

| File | Purpose | When to Use |
|------|---------|------------|
| **HOW_TO_USE_THIS_SKILL.md** | Complete overview & getting started | First - understand all options |
| **QUICK_START_PROMPTS.md** | Ready-to-use prompts for Claude | Want fastest results (15 min) |
| **PROMPT_BASED_WORKFLOW.md** | Detailed phase-by-phase guide | Want professional quality (60 min) |
| **USAGE.md** | Examples and best practices | Need inspiration or examples |
| **SKILL.md** | Skill definition and capabilities | Need technical details |
| **Templates** | Reference templates | Check format examples |

---

## 🎯 The 4 Phases Explained

### Phase 1: Repository Analysis (15-20 min)
**What**: Explore your project and answer questions
**Input**: Your project files + questions
**Output**: Structured analysis

### Phase 2: Generate CLAUDE.md (5-10 min)
**What**: Project constitution
**Input**: Analysis from Phase 1 + prompt
**Output**: CLAUDE.md file

### Phase 3: Generate CODEMAP.md (10-15 min)
**What**: Codebase architecture map
**Input**: Analysis from Phase 1 + prompt
**Output**: CODEMAP.md file

### Phase 4: Generate MEMORY.md (10-15 min)
**What**: Context and knowledge base
**Input**: Analysis from Phase 1 + prompt
**Output**: MEMORY.md file

---

## 💡 Key Features

✨ **Prompt-Based** - Not automated code generation
✨ **Interactive** - Claude asks clarifying questions
✨ **Personalized** - Based on YOUR actual project
✨ **Flexible** - 3 different approaches (Quick/Thorough/Hybrid)
✨ **Professional** - Enterprise-quality documentation

---

## 📊 What You Get

### CLAUDE.md (Project Constitution)
- ✅ Tech stack overview
- ✅ Critical coding rules
- ✅ Input validation patterns
- ✅ Error handling standards
- ✅ Testing requirements
- ✅ Security rules
- ✅ How to add features
- ✅ Pre-commit checklist

### CODEMAP.md (Architecture Map)
- ✅ Directory structure with purposes
- ✅ Service layer patterns
- ✅ Middleware overview
- ✅ Request flow diagrams
- ✅ File quick reference
- ✅ Navigation guides

### MEMORY.md (Context Knowledge)
- ✅ Quick facts table
- ✅ Architecture overview
- ✅ Code conventions with examples
- ✅ Known gotchas and solutions
- ✅ Performance notes
- ✅ Security checklist
- ✅ Testing patterns

---

## 🔄 Complete Workflow

```
START
  ↓
Choose approach (Quick/Thorough/Hybrid)
  ↓
PHASE 1: Analyze Repository (15-20 min)
├─ Answer project questions
├─ Examine code patterns
└─ Document gotchas
  ↓
PHASE 2: Generate CLAUDE.md (5-10 min)
├─ Use prompt from QUICK_START_PROMPTS.md
├─ Paste analysis into Claude
└─ Get CLAUDE.md
  ↓
PHASE 3: Generate CODEMAP.md (10-15 min)
├─ Use prompt from QUICK_START_PROMPTS.md
├─ Paste analysis into Claude
└─ Get CODEMAP.md
  ↓
PHASE 4: Generate MEMORY.md (10-15 min)
├─ Use prompt from QUICK_START_PROMPTS.md
├─ Paste analysis into Claude
└─ Get MEMORY.md
  ↓
REVIEW & CUSTOMIZE (10 min)
├─ Check for accuracy
├─ Remove placeholders
└─ Add context
  ↓
USE YOUR DOCUMENTATION (5 min)
├─ Place files in project root
└─ Reference in future Claude requests
  ↓
SUCCESS! 🎉
```

---

## 📋 Supported Tech Stack

### Frameworks
- ✅ Express
- ✅ Fastify
- ✅ NestJS
- ✅ Others (adaptable)

### Databases
- ✅ PostgreSQL
- ✅ MongoDB
- ✅ MySQL
- ✅ SQLite

### Testing
- ✅ Jest
- ✅ Vitest
- ✅ Mocha
- ✅ Others

### Validation
- ✅ Zod
- ✅ class-validator
- ✅ Custom patterns

### Auth
- ✅ JWT
- ✅ Session
- ✅ OAuth

### Logging
- ✅ Winston
- ✅ Pino
- ✅ Bunyan

---

## 🎓 Examples

### Simple Express API (15 min)
```
Project: User API with Express + PostgreSQL + Jest
Result:
- CLAUDE.md      ~500 lines
- CODEMAP.md     ~400 lines
- MEMORY.md      ~300 lines
Time: 15 minutes
```

### Medium NestJS Service (45 min)
```
Project: Multi-feature NestJS + MongoDB + Vitest
Result:
- CLAUDE.md      ~800 lines
- CODEMAP.md     ~600 lines
- MEMORY.md      ~500 lines
Time: 45 minutes
```

### Large Platform (60 min)
```
Project: Complex Express + PostgreSQL + Jest + E2E
Result:
- CLAUDE.md      ~1000+ lines
- CODEMAP.md     ~800+ lines
- MEMORY.md      ~700+ lines
Time: 60 minutes
```

---

## ✅ Success Criteria

Your generated files are successful when:

**CLAUDE.md**
- [ ] No placeholder values like [XX]
- [ ] Real code examples from your project
- [ ] Specific rules, not generic
- [ ] File paths match your structure

**CODEMAP.md**
- [ ] Actual file locations documented
- [ ] Real function names listed
- [ ] Request flow based on your middleware
- [ ] Navigation paths work

**MEMORY.md**
- [ ] Gotchas specific to your project
- [ ] Code examples show actual patterns
- [ ] Performance issues documented
- [ ] Security measures listed

---

## 🚀 After Generation

### Step 1: Review (10 min)
- Check for accuracy
- Verify all paths are correct
- Ensure code examples match your project

### Step 2: Customize (10 min)
- Add company-specific rules
- Include team conventions
- Update with latest context

### Step 3: Use in Claude Requests
```
"Add new API endpoint

See CLAUDE.md, CODEMAP.md, MEMORY.md for context"
```

Result: 10x faster, more accurate AI assistance!

---

## 💬 FAQ

**Q: How long does it take?**
A: 15 min (quick) to 60 min (thorough)

**Q: Do I need to write code?**
A: No! Just analysis and prompts

**Q: Works with all languages?**
A: Yes! Node.js, Python, Go, Java, C#, Ruby, PHP - any backend stack

**Q: Will files stay updated?**
A: Update manually as project evolves

**Q: Multi-language teams?**
A: Perfect! Creates shared documentation for any tech stack

---

## 🎬 Get Started Now!

### Next Step:
1. **Open**: `references/HOW_TO_USE_THIS_SKILL.md`
2. **Choose**: Quick/Thorough/Hybrid approach
3. **Follow**: The workflow
4. **Generate**: Your documentation
5. **Use**: In future Claude requests

---

## 📚 Related Resources

**Documentation Files**:

- **[SKILL.md](./SKILL.md)** - Skill definition & overview
- **[HOW_TO_USE_THIS_SKILL.md](./references/HOW_TO_USE_THIS_SKILL.md)** - Complete guide
- **[QUICK_START_PROMPTS.md](./references/QUICK_START_PROMPTS.md)** - Copy-paste prompts
- **[PROMPT_BASED_WORKFLOW.md](./references/PROMPT_BASED_WORKFLOW.md)** - Detailed phases

**Complementary Tools**:

- `codemap` - Project structure visualization and architecture maps
- `repomix` - Token-lean context generation
- `mgrep` - Code pattern extraction

---

**Version**: 1.0
**Last Updated**: February 2026
**Status**: Ready to use ✅

Good luck! Your documentation starts now! 🚀
