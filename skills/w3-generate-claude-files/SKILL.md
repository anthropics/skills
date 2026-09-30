---
name: w3-generate-claude-files
description: Generate CLAUDE.md, CODEMAP.md, and MEMORY.md for any backend project (Node.js, Python, Go, etc.) using prompts and manual analysis. Uses Claude AI to help you document your project constitution, codebase architecture, and context knowledge. Language-agnostic, prompt-based approach - focused on accurate, personalized documentation through interactive analysis.
---

# 📝 Generate Claude Files - Multi-Language Documentation

Generate **CLAUDE.md**, **CODEMAP.md**, and **MEMORY.md** for your backend project using **prompts and analysis** (not automated code generation).

**Supported Languages**: Node.js/JavaScript • Python • Go • Java • C# • Ruby • PHP • And more!

---

## 🎯 What This Skill Does

This skill helps you create three essential AI collaboration files for **ANY** backend project:

1. **CLAUDE.md** - Project Constitution
   - Project rules, conventions, tech stack
   - Critical coding standards
   - How to add features
   - Language-specific best practices

2. **CODEMAP.md** - Codebase Architecture Map
   - Directory structure with purposes
   - Request/response flow diagrams
   - Navigation guides
   - Framework-specific patterns

3. **MEMORY.md** - Project Context & Knowledge Base
   - Quick facts and architecture overview
   - Code patterns and conventions
   - Known gotchas and solutions
   - Performance and security notes
   - Language-specific tips

**Approach**: Interactive prompts + manual analysis → personalized, accurate documentation for YOUR tech stack

---

## ⚡ Quick Start (15 minutes)

### Step 1: Get the Quick Start Prompts
```
Open: references/QUICK_START_PROMPTS.md
```

### Step 2: Answer Phase 1 Questions
```
Copy the Phase 1 prompt → Paste into Claude
Answer questions about your project
Get structured analysis
```

### Step 3: Generate Documentation
```
Use Phase 2 prompt → Get CLAUDE.md
Use Phase 3 prompt → Get CODEMAP.md
Use Phase 4 prompt → Get MEMORY.md
```

### Step 4: Use Your Documentation
Review and customize the generated files, then use them in your Claude requests.

---

## ⚡ Optimization: Faster Generation with External Tools

**Save time and tokens by using these CLI tools if available:**

### Option A: Use Existing Codemap
If you already have a `CODEMAP.md`:
- Skip Phase 3 (CODEMAP generation)
- Use existing codemap in Phase 2 analysis
- **Saves**: 10-15 minutes + 20% tokens

### Option B: Generate Codemap with CLI (CLI Tool)
Generate project structure map with `codemap` CLI:
```bash
codemap --output project-structure.md
```
Then use output in Phase 1 to inform CODEMAP generation
- **Saves**: 10-15 minutes + simplifies Phase 3 (CODEMAP)
- **Best for**: Understanding complex project layouts

### Option C: Use repomix (CLI Tool)
Generate token-lean context with `repomix` CLI:
```bash
repomix --output context.md
```
Then paste the output into Phase 1 for comprehensive analysis
- **Saves**: 15-20 minutes + 30% tokens

### Option D: Use mgrep (CLI Tool)
Before Phase 1, run `mgrep` to extract code patterns:
```bash
mgrep "error handling" src/
mgrep "validation" src/
mgrep "interface\|type" src/
```
Collect key patterns and feed into Phase 1
- **Saves**: 10 minutes + gives Phase 1 better answers

### Option E: Combined Optimization (Recommended) ⚡
1. Generate codemap structure: `codemap --output project-structure.md`
2. Generate repomix context: `repomix --output context.md`
3. Run mgrep for patterns: `mgrep "pattern" src/`
4. Feed all outputs into Phase 1 for comprehensive analysis
5. **Result**: 20-25 min instead of 45-60 min + 50% token savings

---

## 📚 How to Use This Skill

### Option 1: Super Quick (15 min) 🏃
Use **QUICK_START_PROMPTS.md**
- Copy Phase 1 prompt → analyze your repo
- Copy Phase 2-4 prompts → generate files
- Done!

### Option 2: Thorough (45-60 min) 📖
Use **PROMPT_BASED_WORKFLOW.md**
- 4 detailed phases with templates
- Complete section-by-section
- Professional quality output

### Option 3: AI-Assisted (30 min) 🤖
Hybrid approach
- Do Phase 1 analysis manually (15 min)
- Use prompts with Claude (10 min)
- Review & customize (5 min)

---

## 📖 Documentation Files

### Main Guides

| File | Purpose | When to Use |
|------|---------|------------|
| **HOW_TO_USE_THIS_SKILL.md** | Overview & quick start | Start here first |
| **PROMPT_BASED_WORKFLOW.md** | Detailed 4-phase guide | Want detailed guidance |
| **QUICK_START_PROMPTS.md** | Ready-to-use prompts | Want fastest approach |

### Templates & References

| File | Purpose |
|------|---------|
| CLAUDE.md.template | Template for project constitution |
| CODEMAP.md.template | Template for architecture map |
| MEMORY.md.template | Template for context knowledge |

---

## 🚀 The 4 Phases

### Phase 1: Repository Analysis (15-20 min)
**You do**: Explore your project, answer questions about:
- Project identity (name, purpose, type)
- Technology stack
- Directory structure
- Code patterns
- Known pain points

**Output**: Structured analysis answers

### Phase 2: Generate CLAUDE.md (5-10 min)
**Claude generates**: Project constitution containing:
- Tech stack overview
- Critical coding rules
- Code quality standards
- How to add features
- Pre-commit checklist

### Phase 3: Generate CODEMAP.md (10-15 min)
**Claude generates**: Architecture map showing:
- Directory structure & purposes
- Request flow diagram
- File quick reference
- Navigation guides

### Phase 4: Generate MEMORY.md (10-15 min)
**Claude generates**: Context knowledge including:
- Quick facts table
- Code patterns & conventions
- Known gotchas & solutions
- Performance notes
- Security checklist

---

## 📋 What You Get

### CLAUDE.md - Project Constitution
✅ Tech stack details specific to your project
✅ Critical coding rules (validation, error handling, testing, language-specific standards)
✅ Project structure documentation
✅ Step-by-step feature addition guide
✅ Pre-commit verification checklist
✅ Decision matrix (when to ask vs. when to decide)

### CODEMAP.md - Architecture Map
✅ Directory structure with clear purposes
✅ Service layer and pattern documentation
✅ Middleware and utility overview
✅ Request flow diagrams
✅ File location quick reference
✅ How to navigate and find code

### MEMORY.md - Context Knowledge
✅ Quick facts table (tech, deployment, auth)
✅ Architecture diagrams
✅ Code conventions with real examples
✅ Known gotchas and their solutions
✅ Performance issues and fixes
✅ Security measures checklist
✅ Testing patterns

---

## 💡 Why This Approach?

### Advantages of Prompts vs. Code Generation

✨ **Accurate** - Based on YOUR actual code, not generic templates
✨ **Personalized** - Reflects your project's specific patterns & gotchas
✨ **Conversational** - Interactive with Claude to clarify details
✨ **Understandable** - Claude asks for clarification when needed
✨ **Flexible** - Easy to customize generated output

---

## 🎯 When to Use This Skill

✅ **Perfect for:**
- Starting a new backend project (any language)
- Onboarding to an existing codebase
- Creating AI-collaboration documentation
- Documenting microservices, APIs, or services
- Documenting team projects consistently
- Multi-language/polyglot teams

✅ **Supported Languages & Frameworks:**

**Node.js/JavaScript**
- Frameworks: Express, Fastify, NestJS, Koa
- Testing: Jest, Vitest, Mocha
- Databases: PostgreSQL, MongoDB, MySQL, SQLite

**Python**
- Frameworks: Django, FastAPI, Flask, Starlette
- Testing: pytest, unittest
- ORMs: SQLAlchemy, Django ORM, Tortoise-ORM
- Databases: PostgreSQL, MySQL, SQLite

**Go**
- Frameworks: Gin, Echo, Chi, Fiber
- Testing: testing package, Testify, GoConvey
- Databases: PostgreSQL, MySQL, SQLite

**Other Languages** (with adaptation):
- Java (Spring Boot, Quarkus)
- C# (.NET, ASP.NET Core)
- Ruby (Rails, Sinatra)
- PHP (Laravel, Symfony)

✅ **Supported Infrastructure:**
- REST APIs
- GraphQL Services
- Microservices
- Event-driven systems
- Message queues (RabbitMQ, Kafka, Redis)
- Background jobs
- Monoliths & distributed systems

---

## 📁 Skill Structure

```
w3-generate-claude-files/
├── SKILL.md                              ← You are here
└── references/
    ├── HOW_TO_USE_THIS_SKILL.md         ← Start here
    ├── PROMPT_BASED_WORKFLOW.md         ← Detailed guide
    ├── QUICK_START_PROMPTS.md           ← Copy-paste prompts
    ├── CLAUDE.md.template               ← Template reference
    ├── CODEMAP.md.template              ← Template reference
    └── MEMORY.md.template               ← Template reference
```

---

## 🔍 Before You Start

You'll need:

✅ A backend project (Node.js, Python, Go, Java, C#, etc.)
✅ Basic knowledge of your project structure
✅ ~15-60 minutes depending on project size
✅ Claude AI access for prompt-based generation
✅ Know your tech stack (framework, database, testing tools)

---

## 📝 Example: What Gets Generated

### For a Simple Express API (15 min)
```
CLAUDE.md      ~500 lines (rules + patterns)
CODEMAP.md     ~400 lines (structure + flow)
MEMORY.md      ~300 lines (context + gotchas)
```

### For a Medium NestJS Service (45 min)
```
CLAUDE.md      ~800 lines (detailed rules)
CODEMAP.md     ~600 lines (complex architecture)
MEMORY.md      ~500 lines (comprehensive context)
```

### For a Large Microservices Platform (60 min)
```
CLAUDE.md      ~1000+ lines (extensive standards)
CODEMAP.md     ~800+ lines (detailed maps)
MEMORY.md      ~700+ lines (complete knowledge)
```

---

## 🚀 Getting Started Right Now

### Step 1: Choose Your Approach
- **Quick?** → Use QUICK_START_PROMPTS.md
- **Thorough?** → Use PROMPT_BASED_WORKFLOW.md
- **Hybrid?** → Do Phase 1, then use prompts

### Step 2: Open the Guide
```
references/HOW_TO_USE_THIS_SKILL.md
```

### Step 3: Follow the Workflow
- Answer analysis questions
- Use copy-paste prompts
- Review generated files
- Customize as needed

### Step 4: Use Your Documentation
In future Claude requests, reference your generated files:
```
"See CLAUDE.md, CODEMAP.md, MEMORY.md for context"
```

---

## 💬 Using Generated Files in Claude Requests

### Before: Generic Explanations Needed
```
"Add user authentication"
→ Claude: "What framework? JWT or session? Where's your auth middleware?"
→ Back and forth for 20+ minutes
```

### After: Instant Understanding
```
"Add user authentication

See CLAUDE.md, CODEMAP.md, MEMORY.md"
→ Claude: Already knows your tech stack, patterns, and conventions
→ Generates code in 5 minutes matching YOUR project style
```

---

## ❓ Quick FAQ

**Q: How long does it take?**
A: 15 min (quick) to 60 min (thorough) depending on project size

**Q: Do I need to write code?**
A: No! This is purely prompts and analysis

**Q: Works with all languages?**
A: Yes! Node.js, Python, Go, Java, C#, Ruby, PHP - any backend stack

**Q: Will files stay updated?**
A: You update manually as project evolves

**Q: Multi-language teams?**
A: Perfect! Creates shared documentation for any tech stack

---

## 🎓 Next Steps

1. Open **HOW_TO_USE_THIS_SKILL.md**
2. Choose your approach (Quick/Thorough/Hybrid)
3. Follow the workflow
4. Generate your documentation files
5. Use in all future Claude requests

---

## 📚 Related Tools & Resources

**Complementary CLI Tools** (for optimization):
- `codemap` - Generate project structure visualization and architecture maps
- `repomix` - Generate token-lean repository context
- `mgrep` - Extract code patterns and conventions

**Using Generated Files**:
- Paste CLAUDE.md, CODEMAP.md, MEMORY.md into future Claude requests
- Reference them with: "See CLAUDE.md, CODEMAP.md, MEMORY.md for context"

---

**Last Updated**: February 2026
**Approach**: Prompt-based (not code generation)
**Status**: Ready to use ✅
