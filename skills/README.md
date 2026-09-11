<div align="center">

# ✈️ LAME-AI

### The First AI Skill for EASA Part-66 Aircraft Maintenance Engineers

*Not lame. Licensed.*

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Claude Skill](https://img.shields.io/badge/Claude-Skill-orange.svg)](https://claude.ai)
[![EASA Part-66](https://img.shields.io/badge/EASA-Part--66-blue.svg)](https://www.easa.europa.eu)
[![GitHub Stars](https://img.shields.io/github/stars/7HAMZAA/lame-ai?style=social)](https://github.com/7HAMZAA/lame-ai)
[![Contributions Welcome](https://img.shields.io/badge/Contributions-Welcome-brightgreen.svg)](CONTRIBUTING.md)

**Built by [7HAMZAA](https://github.com/7HAMZAA) — Aviation Engineer & AI Builder**

[🚀 Quick Install](#-quick-install) • [📚 What's Inside](#-whats-inside) • [🎯 How to Use](#-how-to-use) • [🤝 Contribute](#-contribute)

</div>

---

## 🔥 What is LAME-AI?

**LAME** = **L**icensed **A**ircraft **M**aintenance **E**ngineer

**LAME-AI** is an open-source AI skill that transforms Claude (and other AI tools) into a full EASA Part-66 exam preparation coach. Built from official **Aviotrace Swiss** training manuals + **FAA handbooks** — by an engineer who actually studied for the licence.

> 💡 **No generic AI content.** Every reference file is built from real aviation training material used in Part-147 approved training organisations.

---

## ⚡ Quick Install

### Claude.ai (Desktop or Web)
```
1. Download lame-ai.skill (see Releases)
2. Open Claude.ai → Settings → Skills
3. Click "Upload Skill" → select lame-ai.skill
4. Done. Start any conversation with "test me on Module 5"
```

### Claude Code / Copilot / Cursor
```bash
# Clone the repo
git clone https://github.com/7HAMZAA/lame-ai.git

# Point your AI tool to the skill
# Add to your .claude/settings or equivalent:
# skills: ["./lame-ai/SKILL.md"]
```

---

## 📚 What's Inside

### 18 Reference Files Covering All B1/B2 Modules

| File | Module | Source |
|------|--------|--------|
| `module1-2-maths-physics.md` | M1 Mathematics + M2 Physics | EASA Syllabus |
| `module3-aviotrace.md` | M3 Electrical Fundamentals | Aviotrace Swiss |
| `module4-aviotrace.md` | M4 Electronic Fundamentals | Aviotrace Swiss |
| `module5-aviotrace.md` | M5 Digital Techniques & Instruments | Aviotrace Swiss |
| `module6-materials-hardware.md` | M6 Materials & Hardware | FAA AMT + AC 43.13 |
| `module7-aviotrace.md` | M7 Maintenance Practices (Full) | Aviotrace Swiss |
| `module7-04-aviotrace.md` | M7.04 Avionic Test Equipment | Aviotrace Swiss |
| `module8-aerodynamics-m15-gasturbine.md` | M8 Aerodynamics + M15 Gas Turbine | FAA PHAK + AMT |
| `module9-human-factors.md` | M9 Human Factors | EASA + CAA CAP 716 |
| `module10-aviotrace.md` | M10 Aviation Legislation | Aviotrace Swiss |
| `module11B-turbine-systems.md` | M11B Turbine Aeroplane Systems | FAA AMT Airframe |
| `module13-aircraft-systems.md` | M13 Aircraft Systems | FAA AMT + EASA |

### 🛠️ Exam Tools

| File | Contents |
|------|---------|
| `formula-reference.md` | Every formula with worked numerical examples |
| `mcq-question-bank.md` | 110+ exam-style MCQs with answers & explanations |
| `common-mistakes.md` | Most common exam errors by module — study this last |
| `exam-strategy-b1-b2-comparison.md` | Time management, question techniques, B1/B2 depth map |
| `exam-stats.md` | Question counts & pass marks per module |
| `modules-syllabus.md` | Full M1–17 syllabus overview |

---

## 🎯 How to Use

Once installed, just talk to Claude naturally:

```
"Test me on Module 5 — ARINC buses"
→ Generates 5 EASA-format MCQs, grades your answers, explains mistakes

"Explain how TCAS works"
→ Technical explanation at LAME level with aircraft examples

"Calculate: 12-bit ADC, how many levels?"
→ Shows formula: 2^12 = 4096, with explanation

"What's the difference between B1 and B2?"
→ Full comparison table with module depth per licence

"Give me the 5 most common exam traps in Module 3"
→ Pulls from common-mistakes.md, module-specific

"I have my M7 exam in 3 days, what do I focus on?"
→ Priority revision plan based on question counts
```

---

## 📊 Coverage Stats

```
Total Modules Covered:     12 / 17 (B2 complete)
Total MCQ Questions:       110+
Total Reference Pages:     ~500 equivalent
Pass Mark Target:          75% (EASA standard)
Compatible AI Tools:       Claude · GitHub Copilot · Cursor · Gemini CLI
Language:                  English
Licence Categories:        B1 · B2
```

---

## 🏗️ Repository Structure

```
lame-ai/
├── SKILL.md                          # Main skill file (AI reads this)
├── references/
│   ├── module1-2-maths-physics.md
│   ├── module3-aviotrace.md
│   ├── module4-aviotrace.md
│   ├── module5-aviotrace.md
│   ├── module6-materials-hardware.md
│   ├── module7-aviotrace.md
│   ├── module7-04-aviotrace.md
│   ├── module8-aerodynamics-m15-gasturbine.md
│   ├── module9-human-factors.md
│   ├── module10-aviotrace.md
│   ├── module11B-turbine-systems.md
│   ├── module13-aircraft-systems.md
│   ├── formula-reference.md
│   ├── mcq-question-bank.md
│   ├── common-mistakes.md
│   ├── exam-strategy-b1-b2-comparison.md
│   ├── exam-stats.md
│   └── modules-syllabus.md
├── README.md
├── LICENSE
└── .gitignore
```

---

## 🤝 Contribute

Missing a module? Found an error? Want to add your language?

```bash
# Fork the repo
# Create your branch
git checkout -b feature/add-module-11A

# Make your changes
# Submit a Pull Request
```

### What we need most:
- [ ] Module 11A (B1 Turbine Aeroplane — mechanical systems)
- [ ] Module 12 (Helicopter Aerodynamics)
- [ ] Module 16 (Piston Engine)
- [ ] Module 17 (Propeller)
- [ ] French translation (`/lang/fr/`)
- [ ] Arabic translation (`/lang/ar/`)
- [ ] More MCQ questions per module
- [ ] Worked calculation exercises

Read [CONTRIBUTING.md](CONTRIBUTING.md) before submitting.

---

## ⚠️ Disclaimer

This skill is a **study aid only**. Content is derived from:
- EASA Part-66 official syllabus (public domain)
- FAA AMT Handbooks (public domain — US Government works)
- CAA CAP 716 Human Factors (public domain)

Always refer to the current approved **AMM, SRM**, and applicable **EASA regulations** for actual maintenance. Never maintain aircraft from memory or AI output alone.

**EASA standard applies** where it differs from FAA.

---

## 📬 Contact

Built by **7HAMZAA** — Aviation Engineer & AI Builder

[![GitHub](https://img.shields.io/badge/GitHub-7HAMZAA-black?logo=github)](https://github.com/7HAMZAA)

---

## ⭐ Star History

If LAME-AI helped you pass your exam — give it a star. It helps other engineers find it.

---

<div align="center">

**LAME-AI** — *Not lame. Licensed.*

`#EASA #Part66 #Aviation #AircraftMaintenance #LAME #Avionics #B1 #B2 #MRO #AviationEngineering #Claude #AI #OpenSource #ExamPrep #7HAMZAA`

</div>
