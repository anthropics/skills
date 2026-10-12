# Contributing to LAME-AI

First — thank you. Every contribution makes this better for every aviation student worldwide.

---

## What We Need Most

| Priority | Contribution | Difficulty |
|----------|-------------|------------|
| 🔴 High | Module 11A (B1 mechanical systems) | Medium |
| 🔴 High | Module 16 (Piston Engine) | Medium |
| 🔴 High | More MCQ questions (aim for 500+) | Easy |
| 🟡 Medium | Module 12 (Helicopter) | Medium |
| 🟡 Medium | Module 17 (Propeller) | Easy |
| 🟡 Medium | French translation `/lang/fr/` | Easy |
| 🟡 Medium | Arabic translation `/lang/ar/` | Easy |
| 🟢 Low | Fix typos / errors in existing files | Easy |
| 🟢 Low | Add worked calculation examples | Easy |

---

## How to Contribute

### 1. Fork the Repository
Click **Fork** at the top right of the GitHub page.

### 2. Clone Your Fork
```bash
git clone https://github.com/YOUR-USERNAME/lame-ai.git
cd lame-ai
```

### 3. Create a Branch
```bash
git checkout -b feature/add-module-11A
# or
git checkout -b fix/module5-arinc-error
# or
git checkout -b add/french-translation
```

### 4. Make Your Changes
Follow the file format below.

### 5. Commit and Push
```bash
git add .
git commit -m "Add Module 11A — B1 Turbine Aeroplane mechanical systems"
git push origin feature/add-module-11A
```

### 6. Open a Pull Request
Go to your fork on GitHub → Click **"Compare & pull request"** → Describe what you added.

---

## File Format Standards

### New Module Reference File
Name it: `moduleXX-topic.md`

Required sections:
```markdown
# Module XX — [Title] (B1/B2)
## Sources: [List your sources]

---

## XX.1 [First Topic]
[Content]

---

## Key Exam Traps — Module XX
1. [Trap 1]
2. [Trap 2]
```

### New MCQ Questions
Add to `mcq-question-bank.md` following this exact format:
```markdown
**Q[number].** [Question text]
A) [Option A]  B) [Option B]  C) [Option C]  D) [Option D]
**Answer: [Letter]** — [Brief explanation]
```

### Error Corrections
If you find a factual error:
- Open an **Issue** first describing the error and correct information
- Include your source (AMM chapter, EASA document, FAA handbook reference)
- Then submit a PR with the fix

---

## Content Quality Rules

✅ **Do:**
- Base content on verifiable sources (EASA syllabus, FAA handbooks, official AMMs)
- Cite your source at the top of each file
- Use exact EASA/aviation terminology
- Flag if content differs between EASA and FAA — always note which applies
- Test your MCQs against the EASA question bank if possible

❌ **Don't:**
- Add content from memory without a source
- Copy proprietary training material verbatim (summarise/paraphrase instead)
- Add content that contradicts current EASA regulations without flagging
- Submit content in languages other than English to main branch (use `/lang/` subfolder)

---

## Reporting Issues

Found an error? Missing topic? Broken format?

Open an **Issue** and use one of these labels:
- `bug` — factual error in content
- `enhancement` — new module or feature request
- `question` — unsure about content accuracy
- `translation` — language-related

---

## Code of Conduct

This is a technical community. Be professional, be precise, cite your sources.

Aviation is safety-critical. Wrong information in this skill could affect real exam performance. Quality over quantity — always.

---

## Recognition

All contributors are listed in the README under **Contributors**.
Significant contributions get a shoutout in the release notes.

---

**Built by engineers. For engineers.**

*7HAMZAA*
