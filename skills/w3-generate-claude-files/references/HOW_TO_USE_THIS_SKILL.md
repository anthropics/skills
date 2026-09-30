# How to Use This Skill: Complete Guide

This skill helps you generate **CLAUDE.md**, **CODEMAP.md**, and **MEMORY.md** for **any backend project** (Node.js, Python, Go, Java, C#, etc.) using **prompts and analysis** instead of code generation.

---

## 🎯 What You'll Get

After using this skill, your project will have three professional documentation files:

### 1️⃣ **CLAUDE.md** - Project Constitution
A rulebook for working with your project containing:
- Tech stack overview
- Critical coding rules (validation, error handling, testing, language-specific standards)
- Project structure and how to add features
- Pre-commit checklist
- Decision matrix (when to ask first vs. when to decide)

**Benefits**: Claude AI understands your project's rules and conventions immediately.

### 2️⃣ **CODEMAP.md** - Codebase Architecture Map
A navigation guide showing:
- Directory structure with purposes
- Request flow diagram
- Key files and their functions
- How to find and modify code
- Architecture overview

**Benefits**: Anyone (human or AI) can quickly understand your codebase structure.

### 3️⃣ **MEMORY.md** - Project Context & Knowledge Base
Institutional knowledge documenting:
- Quick facts and tech stack
- Important code conventions
- Known gotchas and their solutions
- Performance issues and fixes
- Security checklist
- Testing patterns

**Benefits**: Avoids repeating mistakes; speeds up onboarding and debugging.

---

## 📚 How This Skill Works

### Approach: Prompts + Analysis (Not Code)

Instead of running scripts that generate files automatically, this skill:

1. **Guides you through analyzing your repository** (15-20 min)
   - Answer questions about your project
   - Examine actual code to understand patterns
   - Document gotchas and conventions

2. **Provides structured prompts** to use with Claude
   - Copy-paste prompts from this skill
   - Paste into Claude with your project analysis
   - Claude generates the documentation files

3. **You customize the output**
   - Review generated files
   - Remove placeholders
   - Add context specific to your project

**Advantage**: Your documentation is accurate, specific, and reflects your actual project—not a generic template.

---

## 🚀 Quick Start (5 Minutes)

### Step 1: Gather Project Info (2 min)

Answer these quick questions:

```
- Project name? ___
- Framework? (Express/NestJS/Fastify) ___
- Database? (PostgreSQL/MongoDB) ___
- Testing? (Jest/Vitest) ___
```

### Step 2: Get the Prompts (1 min)

Go to: **`/references/QUICK_START_PROMPTS.md`**

Find the **Phase 1: Repository Analysis Prompt**

### Step 3: Run with Claude (2 min)

1. Copy the Phase 1 prompt
2. Paste into Claude Chat
3. Include your answers from Step 1
4. Run the prompt

**Claude will ask for more details** → Provide them from your actual codebase

---

## 📖 Detailed Workflow (45-60 minutes)

For the complete experience with all details:

### Follow This Path:

1. **Read**: [`PROMPT_BASED_WORKFLOW.md`](./PROMPT_BASED_WORKFLOW.md)
   - Complete 4-phase guide with templates
   - Detailed instructions for each phase
   - Section-by-section breakdown

2. **Use**: [`QUICK_START_PROMPTS.md`](./QUICK_START_PROMPTS.md)
   - Copy-paste prompts for Claude
   - One prompt per file (CLAUDE.md, CODEMAP.md, MEMORY.md)
   - Validation checklist at the end

3. **Customize**: Review and adjust generated files
   - Remove placeholder values
   - Add project-specific context
   - Update Last Modified dates

---

## 📋 The 4 Phases Explained

### Phase 1: Repository Analysis (15-20 min)
**What you do**: Explore your project and answer questions

**Questions cover**:
- Project identity (name, purpose, type)
- Technology stack (all dependencies)
- Directory structure (what's in each folder)
- Code patterns (validation, error handling, logging)
- Pain points (known issues, gotchas)

**Deliverable**: Answers to all questions

**Prompt to use**: `QUICK_START_PROMPTS.md` → Phase 1

---

### Phase 2: Generate CLAUDE.md (5-10 min)
**What Claude does**: Generates project constitution based on your analysis

**File includes**:
- Tech stack
- Critical coding rules
- Project structure
- How to add features
- Pre-commit checklist

**Your role**: Review and customize for your project

**Prompt to use**: `QUICK_START_PROMPTS.md` → Phase 2

---

### Phase 3: Generate CODEMAP.md (10-15 min)
**What Claude does**: Maps your codebase architecture

**File includes**:
- Directory structure with purposes
- Request flow diagram
- Key files and their functions
- Navigation guides

**Your role**: Review and add missing context

**Prompt to use**: `QUICK_START_PROMPTS.md` → Phase 3

---

### Phase 4: Generate MEMORY.md (10-15 min)
**What Claude does**: Documentinstitutional knowledge

**File includes**:
- Quick facts about your project
- Code patterns and conventions
- Known gotchas and solutions
- Performance and security notes

**Your role**: Review and add project-specific details

**Prompt to use**: `QUICK_START_PROMPTS.md` → Phase 4

---

## 🗂️ Files in This Skill

```
w3-generate-claude-files/
├── SKILL.md                          ← What this skill does
└── references/
    ├── HOW_TO_USE_THIS_SKILL.md     ← You are here
    ├── PROMPT_BASED_WORKFLOW.md     ← Detailed 4-phase guide
    ├── QUICK_START_PROMPTS.md       ← Copy-paste prompts for Claude
    ├── USAGE.md                     ← Additional usage examples
    ├── CLAUDE.md.template           ← Template reference
    ├── CODEMAP.md.template          ← Template reference
    └── MEMORY.md.template           ← Template reference
```

---

## 💡 Which File Should I Use?

### I want the fastest start
→ Use **QUICK_START_PROMPTS.md**
- Copy Phase 1 prompt
- Answer questions
- Use Phase 2-4 prompts to generate files
- ~45 minutes total

### I want detailed guidance
→ Use **PROMPT_BASED_WORKFLOW.md**
- Walks through each phase step-by-step
- Provides templates for each section
- Explains what to document in detail
- ~60 minutes with high quality output

### I want both
→ Start with QUICK_START_PROMPTS.md, then reference PROMPT_BASED_WORKFLOW.md for details on specific sections.

---

## ✅ Step-by-Step Instructions

### Option A: Super Quick (15 min - Simple Project)

1. Open **QUICK_START_PROMPTS.md**
2. Copy **Phase 1 prompt**
3. Paste into Claude with your project brief
4. Copy Claude's analysis + **Phase 2 prompt** → Get CLAUDE.md
5. Copy Claude's analysis + **Phase 3 prompt** → Get CODEMAP.md
6. Copy Claude's analysis + **Phase 4 prompt** → Get MEMORY.md
7. Paste all three files into your project root
8. Done! 🎉

### Option B: Thorough (45-60 min - Professional Quality)

1. Open **PROMPT_BASED_WORKFLOW.md**
2. Follow **Phase 1** → Explore your repository, answer all questions
3. Follow **Phase 2** → Fill in CLAUDE.md template with your answers
4. Follow **Phase 3** → Fill in CODEMAP.md template with your code examples
5. Follow **Phase 4** → Fill in MEMORY.md template with your gotchas
6. Review all three files for accuracy
7. Paste into your project root
8. Done! 🎉

### Option C: AI-Assisted (30 min - Best of Both)

1. Open **PROMPT_BASED_WORKFLOW.md**
2. Complete **Phase 1 Analysis** manually (15 min)
3. Use **QUICK_START_PROMPTS.md** → Phase 2, 3, 4 with Claude (10 min)
4. Review and customize generated files (5 min)
5. Done! 🎉

---

## 📝 What You Need to Provide

### Required Information

✅ **Project basics**:
- Name
- Framework (Express/NestJS/Fastify)
- Database (PostgreSQL/MongoDB)
- Main purpose

✅ **Directory structure**:
- Show your folder organization
- List important files

✅ **Code examples**:
- 1 example of validation
- 1 example of error handling
- 1 example of API response
- 1 example of service pattern

✅ **Known issues**:
- Performance problems
- Common bugs
- Auth/CORS issues
- Database issues

### What Claude Will Generate

🤖 **CLAUDE.md**:
- Tech stack details
- Coding rules specific to your stack
- Project structure
- How to add features

🤖 **CODEMAP.md**:
- Directory purpose mapping
- Request flow diagram
- File quick reference
- Navigation guide

🤖 **MEMORY.md**:
- Quick facts table
- Architecture diagram
- Code conventions with examples
- Known gotchas and solutions

---

## 🎓 Examples of Generated Files

### Minimal Project (15 min)
```
Project: Simple Express API
- Express + PostgreSQL + Jest
- 5 main endpoints
- ~2000 lines of code

Result:
- CLAUDE.md: 500 lines
- CODEMAP.md: 400 lines
- MEMORY.md: 300 lines
```

### Medium Project (45 min)
```
Project: NestJS Microservice
- NestJS + MongoDB + Vitest
- 15+ endpoints
- Service, middleware, guard layers
- ~5000 lines of code

Result:
- CLAUDE.md: 800 lines
- CODEMAP.md: 600 lines
- MEMORY.md: 500 lines
```

### Complex Project (60 min)
```
Project: Multi-service Platform
- Express + PostgreSQL + Jest + E2E tests
- 50+ endpoints
- Complex auth, caching, queuing
- ~10,000 lines of code

Result:
- CLAUDE.md: 1000+ lines
- CODEMAP.md: 800+ lines
- MEMORY.md: 700+ lines
```

---

## 🚀 After Generation: Next Steps

### 1. Review Generated Files (10 min)
- [ ] Check for accurate file paths
- [ ] Verify code examples are from your project
- [ ] Ensure no placeholder values remain
- [ ] Confirm architecture diagrams are correct

### 2. Customize (10 min)
- [ ] Update project name/description
- [ ] Add company-specific rules
- [ ] Add performance notes
- [ ] Document team-specific gotchas

### 3. Use in Claude Requests (Ongoing)
```
"See CLAUDE.md, CODEMAP.md, and MEMORY.md for context"
```

This tells Claude:
- Your project structure (CODEMAP.md)
- Your rules and patterns (CLAUDE.md)
- Your gotchas and context (MEMORY.md)

Result: 10x faster, more accurate assistance! 🎯

---

## 💬 Using Generated Docs in Claude Requests

### Without Documentation
```
"Add user authentication to my Node.js API"
→ Claude asks many clarifying questions
→ Takes 30 minutes
```

### With Documentation
```
"Add user authentication to my Node.js API

See CLAUDE.md, CODEMAP.md, MEMORY.md for context"
→ Claude already knows your stack, patterns, gotchas
→ Takes 5 minutes
```

---

## ❓ Frequently Asked Questions

### Q: How long does it take?
**A**: 15-60 minutes depending on project size and approach
- Quick: 15 min (simple projects)
- Thorough: 45-60 min (professional quality)

### Q: Do I need to write code?
**A**: No! This is prompt + analysis based, not code generation

### Q: Works with all backend languages?
**A**: Yes! Node.js, Python, Go, Java, C#, Ruby, PHP - any backend project. Skill is language-agnostic

### Q: Will the files stay in sync?
**A**: You need to update them manually as your project evolves. Update the "Last Modified" date when you make changes

### Q: Can I use with an existing project?
**A**: Absolutely! Works great for projects of any age

### Q: What if my project structure is unusual?
**A**: The prompts are flexible. Adapt them to match your actual structure

### Q: Should I commit these files to git?
**A**: Yes! They're valuable documentation for your team and for AI assistance

---

## 🎯 Success Criteria

Your generated files are successful when:

✅ **CLAUDE.md**
- [ ] No placeholder values like [XX]
- [ ] Real code examples from your project
- [ ] Specific rules, not generic
- [ ] File paths match your actual structure

✅ **CODEMAP.md**
- [ ] Actual file locations documented
- [ ] Real function names listed
- [ ] Request flow based on your actual middleware
- [ ] Navigation paths work

✅ **MEMORY.md**
- [ ] Gotchas specific to your project
- [ ] Code examples show actual patterns
- [ ] Performance issues documented
- [ ] Security measures listed

---

## 🔄 Workflow Diagram

```
START
  ↓
[Option: Quick/Thorough/AI-Assisted]
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
USE (5 min)
  ├─ Place files in project root
  └─ Reference in future Claude requests
  ↓
SUCCESS! 🎉
```

---

## 📚 Related Resources

- **[PROMPT_BASED_WORKFLOW.md](./PROMPT_BASED_WORKFLOW.md)** - Detailed phase-by-phase guide
- **[QUICK_START_PROMPTS.md](./QUICK_START_PROMPTS.md)** - Copy-paste prompts for Claude
- **[CLAUDE.md.template](./CLAUDE.md.template)** - Template reference
- **[CODEMAP.md.template](./CODEMAP.md.template)** - Template reference
- **[MEMORY.md.template](./MEMORY.md.template)** - Template reference

---

## 🎬 Ready to Start?

### Choose your path:

**🏃 I'm in a hurry** (15 min)
→ Go to QUICK_START_PROMPTS.md

**📚 I want detailed guidance** (45-60 min)
→ Go to PROMPT_BASED_WORKFLOW.md

**🤖 I want AI help** (30 min)
→ Follow Option C from "Step-by-Step Instructions" above

---

**Last Updated**: February 2026
**Skill Version**: 1.0
**Status**: Ready to use ✅

Good luck! Your project documentation starts now! 🚀
