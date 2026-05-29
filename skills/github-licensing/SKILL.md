---
name: github-licensing
description: Choose, customize, and apply a software license for a GitHub project. Use this skill whenever the user is starting a new repo or project and needs to pick a LICENSE, asks "which license should I use", wants to open-source or protect/monetize their code, wants to prevent competitors from reselling their work as a SaaS, wants to dual-license or sell a commercial edition, needs a CLA/DCO or contributor agreement, wants to add trademark/attribution protection, needs to customize or add terms to a license, or wants to audit/validate the license already in a repository. Trigger even if the user only mentions "MIT", "Apache", "GPL", "AGPL", "BSL", "open source", "source available", "fair source", "copyleft", or "license header" without saying the word "license" explicitly.
---

# GitHub Licensing

Help a developer **choose the right software license, harden it for their goals, and implement it correctly** in a GitHub repository — or **audit** the license a repo already has.

> **Not legal advice.** This skill gives engineering-grade defaults and explains how licenses work in practice. It is not a substitute for a lawyer. For dual-licensing, trademark enforcement, patent strategy, or anything with real money attached, tell the user to have an IP attorney review it. Surface this caveat once, early, then move on — don't repeat it at every step.

## How to use this skill

There are three jobs this skill does. Figure out which one the user wants, then follow that path.

| Job | Trigger | Path |
|---|---|---|
| **Choose** a license for a new/unlicensed project | "which license", "starting a project", "open source this" | Run the **Interview** → **Recommend** → **Implement** |
| **Audit** an existing repo's license | "is my license right", "check my license", "is this compatible" | Jump to **Auditing an existing repo** |
| **Protect / customize** (often after choosing) | "stop competitors", "dual license", "sell commercial", "add trademark", "customize the license" | Read `references/protection.md` and apply |

Default to the **interactive interview** — the user explicitly wants Claude to interview them and give baseline direction at project start. Don't dump the whole decision tree on them; ask, listen, then recommend.

## Step 1 — The interview (interactive)

Ask these questions **conversationally, a few at a time** (not as one giant wall). Adapt — skip questions already answered, drill into whatever the user flags. The goal is to learn enough to route confidently.

1. **What is the project?** Library/SDK, application, CLI tool, web service/SaaS backend, framework, dataset/docs, or something embedded in other people's products?
2. **Who do you want to use it, and how?** Anyone freely (max adoption)? Other open-source projects? Companies internally? Or are you planning to sell/commercialize it?
3. **Commercial intent.** Do you plan to make money from this directly (paid editions, hosted version, support), or is it a community/portfolio/infra project?
4. **The competitor/SaaS question.** Would you be upset if a cloud provider or competitor took your code, ran it as a paid hosted service, and contributed nothing back? (This single answer drives the biggest fork in the tree — see below.)
5. **Contributions.** Do you expect outside contributors? Do you want to keep the option to relicense or sell a commercial version later? (If yes → you'll need a CLA; see `references/protection.md`.)
6. **Patents.** Does the project involve patentable techniques, or are you contributing in a patent-sensitive industry? (Pushes toward Apache-2.0 / GPLv3 / AGPL, which have express patent grants.)
7. **Brand.** Do you have a project/product name, logo, or brand you want to protect even while the code is open? (→ trademark policy, separate from the code license.)
8. **Dependencies.** Is the project a derivative of, or does it statically link, GPL/LGPL/other copyleft code? (Existing dependencies can constrain or force your choice — check `references/compatibility.md`.)
9. **Non-code assets in the repo?** Docs, data, media, fonts? (These often want a separate license; note it but the skill focuses on code.)

## Step 2 — Route to a recommendation

Use the answers to land in one of these buckets. Read the matching reference file before giving final advice — don't recommend from memory.

```
START: Do you want to keep others from offering your work as a closed/hosted service
       without giving back, OR do you plan to monetize it directly?
│
├─ NO, maximize adoption / it's a library / I don't mind reuse
│   │
│   ├─ Want an express PATENT grant or corporate-friendly defaults?  → Apache-2.0
│   ├─ Want the shortest, most universal, most familiar?             → MIT
│   ├─ Want MIT-like but with an explicit non-endorsement clause?    → BSD-3-Clause
│   └─ (ISC = MIT-equivalent, terser; BSD-2 = MIT-equivalent)
│        → references/permissive.md
│
├─ YES, keep it OPEN but force improvements to stay open (share-alike)
│   │
│   ├─ It's a network service / could be run as SaaS  → AGPL-3.0   ★ key anti-SaaS-freeloader, still OSI open source
│   ├─ It's an application, want strong copyleft       → GPL-3.0
│   ├─ It's a library, want adoption but file-level share-alike → MPL-2.0  (or LGPL for linking-based)
│   └─ Eclipse/Java ecosystem                          → EPL-2.0
│        → references/copyleft.md   (AGPL §13 is the critical section)
│
└─ YES, and AGPL isn't enough — I want to explicitly forbid commercial resale /
   hosted competition, and I'm OK NOT being "open source" in the OSI sense
    │
    ├─ Want it to AUTO-CONVERT to open source after N years  → BSL 1.1 or FSL-1.1 (Fair Source)
    ├─ Want to block managed services + license-key circumvention → Elastic License 2.0
    ├─ "Run as a service → open-source your whole stack"     → SSPL (heavy, controversial)
    ├─ A simple "no selling" rider on top of an existing license → Commons Clause
    └─ Modular non-commercial / internal-use / small-business grants → PolyForm
         → references/source-available.md
```

**The most important fork** (your stated priority): "stop a competitor running it as a SaaS." There is a real ladder of strength and trade-offs here — AGPL-3.0 (still open source, share-alike on the network) → FSL/BSL (source-available, time-delayed open) → Elastic-2.0/SSPL (source-available, hard restrictions) → fully proprietary/dual-licensed. Walk the user up the ladder only as far as their goal requires, and be explicit about what each rung *costs* (loss of OSI "open source" label, contributor friction, ecosystem packaging issues). Details and the comparison table are in `references/source-available.md`.

## Step 3 — Protect & customize (optional layer)

If the user wants to monetize, dual-license, or protect their brand, read **`references/protection.md`** and apply the relevant mechanism:

- **Dual-licensing / open-core** (open community edition + paid commercial license) — requires you own all the rights, which means a **CLA**.
- **CLA vs. DCO** — set up contributor agreements so you *can* relicense/sell later. DCO (`git commit -s`) is lightweight; a CLA is needed if you ever want to dual-license or relicense.
- **Trademark / attribution** — your code license does **not** protect your name/logo. Add a separate trademark policy.
- **Customizing a license correctly** — ⚠️ do **not** edit the canonical text of MIT/Apache/GPL. Use the *sanctioned* mechanisms (additional terms, exceptions, riders, NOTICE files, BSL's "Additional Use Grant"). See `references/protection.md`.

## Step 4 — Implement (write the files)

Once the license is chosen, **write the files into the repo** (the user wants this, not just advice):

1. **`LICENSE`** (or `LICENSE.txt`/`LICENSE.md`) at repo root — use the canonical text from `assets/templates/`, fill in copyright year + holder. GitHub's `licensee` detector recognizes `LICENSE`, `LICENSE.txt`, `LICENSE.md`, `COPYING`.
2. **`NOTICE`** if Apache-2.0 and there are attributions to carry.
3. **Source file headers** — add `SPDX-License-Identifier:` headers (modern standard; see `references/protection.md` for the REUSE spec and per-license header text).
4. **Parameter blocks** for BSL/FSL — fill in Change Date, Change License, Additional Use Grant. Templates in `assets/templates/`.
5. **Contributor setup** if dual-licensing — add DCO/CLA docs and `CONTRIBUTING.md` notes.
6. **`README` license section + badge** — add a short license statement and SPDX badge.

Always confirm the **copyright holder name** and **year** with the user before writing, and confirm SPDX identifier. After writing, summarize what each file does and any follow-ups (e.g., "enable the DCO bot", "have a lawyer review the commercial license").

## Auditing an existing repo

When the user wants to check a repo's current license:

1. Locate the license file(s) and any `SPDX-License-Identifier` headers; identify the SPDX ID. Note if the text was modified from canonical (→ tooling won't recognize it; should be `LicenseRef-`).
2. Check **dependency compatibility** — does the repo pull in copyleft (GPL/AGPL/LGPL) deps that conflict with its declared license? See `references/compatibility.md`.
3. Check **hygiene** — is there a copyright holder? Are source headers consistent? Is there a `NOTICE` if Apache? Multi-license repos: is it REUSE-compliant?
4. Check **goal fit** — ask what they're trying to achieve and whether the current license actually delivers it (common gap: shipped MIT but wants to prevent SaaS resale).
5. Report findings + recommended changes. Offer to apply fixes.

## Reference files

Read the relevant one(s) before giving final recommendations — they carry the authoritative, current detail:

- `references/permissive.md` — MIT, Apache-2.0, BSD-2/3-Clause, ISC
- `references/copyleft.md` — GPL-2.0/3.0, AGPL-3.0, LGPL, MPL-2.0, EPL-2.0 (AGPL §13 focus)
- `references/source-available.md` — BSL, FSL/Fair Source, Elastic-2.0, SSPL, PolyForm, Commons Clause
- `references/protection.md` — dual-licensing, CLA/DCO, trademark, correct customization, SPDX/REUSE hygiene
- `references/compatibility.md` — license compatibility matrix and how to combine licenses

Canonical license texts and fill-in templates live in `assets/templates/`.
