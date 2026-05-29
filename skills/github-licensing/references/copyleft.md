# Copyleft Licenses: GPL, AGPL, LGPL, MPL, EPL

A practical reference for choosing a copyleft license at project setup. Copyleft licenses use copyright to *guarantee* downstream freedom: anyone who receives the software (and, for AGPL, anyone who uses it over a network) must be able to get the source and the same rights. The opposite of permissive (MIT/Apache), which let recipients re-close the code.

**Strong copyleft** = the share-alike obligation reaches the *whole combined work* (anything linked/integrated). **Weak copyleft** = the obligation is bounded to a smaller unit (the licensed files, or the library itself), so you can combine it with proprietary code under certain rules.

> Engineering guidance, not legal advice. For relicensing an existing project, dual-licensing, or commercial-dispute exposure, consult a lawyer.

## Contents
- **Strong:** [GPL-2.0](#gpl-20) · [GPL-3.0](#gpl-30) · [AGPL-3.0](#agpl-30) — **[AGPL §13 network clause](#agpl-section-13--the-networksaas-clause-the-important-part)**
- **Weak:** [LGPL-2.1](#lgpl-21) · [LGPL-3.0](#lgpl-30) · [MPL-2.0](#mpl-20) · [EPL-2.0](#epl-20)
- [Compatibility matrix](#compatibility-matrix)
- [Decision sub-tree: prevent closed SaaS forks](#decision-sub-tree-i-want-it-open-but-no-competitor-running-it-as-a-closed-hosted-service)
- [GPL linking exceptions (customizing correctly)](#gpl-linking-exceptions--granting-extra-permissions-without-editing-the-gpl)
- [Real-world projects](#real-world-projects-on-each-license)

---

# STRONG COPYLEFT

## GPL-2.0

- **SPDX:** `GPL-2.0-only` or `GPL-2.0-or-later`. Bare `GPL-2.0` is **deprecated** — always use the `-only` / `-or-later` suffix to make the "this version only" vs. "any later version" choice explicit.
- **OSI-approved:** Yes. **FSF free/libre:** Yes.
- **Plain English:** The most widely used copyleft license — if you distribute the program or a derivative, you must ship it under GPL-2.0 with complete source.
- **Permissions:** commercial use, modification, distribution, private use.
- **Conditions:** include-copyright, document-changes, disclose-source, same-license.
- **Limitations:** no liability, no warranty. **No explicit patent grant** — a key gap vs. v3.
- **Scope of copyleft:** Strong / whole-work. Trigger = **distribution** (conveying a copy outside your org). Boundary = the entire "work based on the Program," including statically or dynamically linked code. Pure aggregation on one medium is not covered.
- **"Or later" clause:** Section 9 lets *you the licensor* offer "version 2 or any later version." `GPL-2.0-only` deliberately locks the project to v2 — this is what makes the Linux kernel GPLv2-only and unable to absorb GPLv3 code.
- **Compatibility:** GPL-2.0-only is **incompatible with GPLv3** and **incompatible with Apache-2.0** (Apache's patent-termination clause is an "additional restriction").
- **How to apply:** Full license in `COPYING` (GNU convention) or `LICENSE` at root + per-file boilerplate header. **Do not edit the license text** — to grant extra permissions, add a separate exception.
- **Pick this when:** You need to interoperate with the GPLv2-only ecosystem (notably the Linux kernel) and explicitly don't want v3's anti-tivoization/patent terms. Most new projects should prefer GPL-3.0.

## GPL-3.0

- **SPDX:** `GPL-3.0-only` or `GPL-3.0-or-later` (bare `GPL-3.0` deprecated).
- **OSI-approved:** Yes. **FSF free/libre:** Yes.
- **Plain English:** The modern strong copyleft license — distribute the program or any larger work using it under GPL-3.0 with complete source, preserve notices, and you receive an express patent grant from contributors.
- **Permissions:** commercial use, modification, distribution, **patent use**, private use.
- **Conditions:** include-copyright, document-changes, disclose-source, same-license.
- **Limitations:** no liability, no warranty.
- **Scope of copyleft:** Strong / whole-work. Triggered by **conveying** (distribution).
- **How to apply:** Full text in `COPYING`/`LICENSE` + per-file boilerplate header. Don't edit the text; add exceptions separately.
- **Pick this when:** You want maximum assurance that improvements stay open for *distributed* software (desktop apps, CLI tools, firmware, strongly-copylefted libraries), want explicit patent protection, and don't need the network/SaaS clause (if you do, use AGPL).

### GPLv2 vs GPLv3 — the differences that actually matter

1. **Anti-tivoization.** GPLv3 adds "Installation Information" requirements: ship GPLv3 software inside a consumer device and you must provide the signing keys/info needed to install *modified* versions and have them run. Blocks "tivoization" (hardware that runs the code but cryptographically refuses user-modified builds). GPLv2 has no such clause.
2. **Explicit patent grant.** GPLv3 gives an express patent license + anti-retaliation. GPLv2 has only an implied grant at best — which is why Apache-2.0 is compatible with v3 but not v2.
3. **DRM clause.** GPLv3 declares the software is not a "technological protection measure," so anti-circumvention laws can't be used against modifiers.
4. **"Or later" clause.** `-only` freezes the version; `-or-later` lets downstream upgrade.
5. **Compatibility.** GPLv3's Section 7 "additional terms" is the machinery that makes Apache-2.0 and others compatible with it.

## AGPL-3.0

- **SPDX:** `AGPL-3.0-only` or `AGPL-3.0-or-later`.
- **OSI-approved:** Yes. **FSF free/libre:** Yes (FSF's recommended choice for server-side software).
- **Plain English:** GPL-3.0 plus a "network copyleft" clause — if users interact with your modified version *over a network*, you must offer them the complete corresponding source, even though you never "distributed" a binary.
- **Permissions:** commercial use, modification, distribution, patent use, private use.
- **Conditions:** include-copyright, document-changes, disclose-source, **network-use disclosure**, same-license.
- **Limitations:** no liability, no warranty.
- **Scope:** Strong / whole-work, **plus the network trigger**. Identical to GPLv3 except for Section 13.

### AGPL Section 13 — the network/SaaS clause (the important part)

**What it requires, precisely:** If you *modify* the program and run that modified version so users **interact with it remotely through a computer network** (and your version supports such interaction), you must **prominently offer those network users the opportunity to receive the Corresponding Source** of your version — for free, from a network server, by some standard download means. The Corresponding Source is the complete source for *your* running version, including your modifications.

**Why it exists — the "SaaS loophole."** Plain GPL's copyleft fires only on *distribution*. A company can take GPL software, modify it heavily, and run it as a hosted web service — users never receive a binary, so the source-sharing obligation never fires. AGPL §13 closes this: *remote network interaction* counts as the trigger.

**Important limits — what AGPL does *not* do:**
- It only fires if the operator **modifies** the code. Running stock, unmodified AGPL software as a service creates no obligation beyond making the (already public) source available.
- It only covers the **AGPL work and its corresponding source**, not your separate proprietary services that talk to it over a clean network/API boundary. It is *not* a viral grab on your entire infrastructure.
- It does **not** prohibit commercial or SaaS use, and does **not** require patches *back to you* — only that source is offered to *the service's own users*. A competitor can comply by publishing their fork's source; AGPL's deterrent is that they must give away their modifications, not that they're forbidden from competing.
- Purely internal use with no external network users doesn't trigger §13.

**Real-world enforcement reputation.** Little direct litigation; its power is largely *deterrent* — many corporate legal departments simply ban AGPL dependencies rather than risk source disclosure, which is itself the effect many adopters want. The closest major case, **Neo4j v. PureThink/Suhy**, is really about AGPLv3 **Section 7** (added restrictions): Neo4j stapled the non-free "Commons Clause" onto verbatim AGPLv3; a downstream party stripped it, citing AGPL §7's "you may remove added restrictions." The district court sided with Neo4j; the **Ninth Circuit appeal (Case No. 24-5538) was still pending as of early-mid 2026**, with the **FSF** and **Software Freedom Conservancy** both filing amicus briefs arguing the lower court misread the license.

- **How to apply:** Full `LICENSE` at root + per-file boilerplate header. Crucially, the source-availability *offer* must be wired into the running app (e.g., a visible "Source" link in the UI/footer). Don't edit the text.
- **Pick this when:** You're building **server-side / SaaS software** and want to prevent competitors from running a closed, modified hosted version. The strongest open-source defense against the SaaS-fork business model while remaining genuinely OSI-approved. *(If even this isn't enough — you want to forbid hosted competition outright — you must leave open source: see `source-available.md`.)*

---

# WEAK COPYLEFT

## LGPL-2.1

- **SPDX:** `LGPL-2.1-only` or `LGPL-2.1-or-later`. **OSI:** Yes. **FSF:** Yes.
- **Plain English:** A library license — modifications to the library itself stay LGPL, but programs that merely *link to* the library can remain under any license, including proprietary.
- **Permissions:** commercial use, modification, distribution, private use.
- **Conditions:** include-copyright, disclose-source, document-changes, **same-license (library)**.
- **Scope:** Weak / library-bounded. Changes to the LGPL library's own files must be released under LGPL; an application that *uses* the library is not forced open, provided the user can swap in a modified library.
- **Pick this when:** Publishing a **library** that you want broadly adoptable (including by proprietary software) while keeping the library itself open, and you need compatibility with the older v2.x ecosystem. New libraries usually prefer LGPL-3.0.

## LGPL-3.0

- **SPDX:** `LGPL-3.0-only` or `LGPL-3.0-or-later`. **OSI:** Yes. **FSF:** Yes.
- **Plain English:** Structured as a *set of additional permissions on top of GPL-3.0* — same library/proprietary-linking deal as LGPL-2.1, with GPLv3's patent grant and anti-tivoization baked in.
- **Permissions:** + **patent use**.
- **How to apply:** Because it's "GPL-3.0 + extra permissions," ship **both**: the GPL-3.0 text (`COPYING`) *and* a `COPYING.LESSER` with the LGPL-3.0 text. In per-file headers, insert "Lesser" before "General" in the three places. **Never edit either body** — the LGPL is itself the exception document layered on the GPL.
- **Pick this when:** Publishing a new library usable by proprietary software, keeping library improvements open, with GPLv3 patent/anti-lockdown protections.

### LGPL dynamic vs static linking — the nuance

The LGPL's goal is that the **end user can replace the LGPL library with their own modified version and relink** the application:
- **Dynamic linking** (shared `.so`/`.dll`): Easiest. The user can already drop in a modified library, so keep your app closed and just ship the LGPL library's source/notices.
- **Static linking** (library baked into your binary): You must enable relinking — ship **either your app's source, or its object files / a relinkable form**, plus build info, so the user can rebuild against a modified library. Your own source can stay proprietary if you provide the object files.

Practical takeaway: **dynamic-link LGPL libraries** and obligations are trivial; static linking is allowed but adds the object-file/relink burden.

## MPL-2.0

- **SPDX:** `MPL-2.0` (or `MPL-2.0-no-copyleft-exception`). **OSI:** Yes. **FSF:** Yes (GPL-compatible by default).
- **Plain English:** File-level weak copyleft — any *file* that originated from MPL code stays MPL (modifications must be shared), but you can freely combine those files with proprietary files in a "Larger Work."
- **Permissions:** + **patent use**.
- **Conditions:** disclose-source, include-copyright, **same-license (file)**.
- **Scope:** Weak / **file-level**. Trigger = distributing modified *MPL-covered files*; boundary = the individual file. New files you add can be under any license, even proprietary — a clean middle ground: changes to existing MPL files come back, your own additions don't have to.
- **Patent grant + retaliation:** Express patent license from each contributor; patent rights terminate if you sue a contributor alleging infringement.
- **Secondary-license / GPL compatibility:** By **default**, §3.3 lets a Larger Work combining MPL code with a "Secondary License" (GPL-2.0+, LGPL-2.1+, AGPL-3.0+) offer the MPL parts under that GNU license too — i.e., **MPL-2.0 is GPL-compatible out of the box**. A licensor can opt out via the **Exhibit B** "Incompatible With Secondary Licenses" notice (mainly to migrate legacy MPL-1.1 code). For new projects, leave Exhibit B off to keep GPL compatibility.
- **How to apply:** `LICENSE` at root + short **Exhibit A** header on each source file.
- **Pick this when:** You want *gentle* copyleft guaranteeing fixes to your files come back without scaring off proprietary integrators, plus explicit patent protection and optional GPL compatibility. Great for widely-reused libraries/components.

## EPL-2.0

- **SPDX:** `EPL-2.0`. **OSI:** Yes. **FSF:** free, but **GPL-incompatible** (unless the Secondary-License switch is used).
- **Plain English:** A commercially-friendly file-level weak copyleft license popular in the Java/Eclipse world — share modifications to EPL files, but you can link EPL code with code under other licenses (including commercial) and distribute binaries commercially.
- **Permissions:** + **patent use**.
- **Conditions:** disclose-source, include-copyright, **same-license** (for Contributions).
- **Scope:** Weak, roughly **file-level** (EPL-2.0 switched the older "module" wording to "file"). Modifications you distribute to EPL-covered files must be released in source under EPL. Separate modules/files that merely interoperate can stay proprietary — so you can build a commercial product around an EPL core.
- **GPL switch:** EPL-2.0 added an option for the licensor to designate a **"Secondary License" (a chosen GPL version)** in a notice, making that EPL code combinable with GPL. Without it, EPL is GPL-incompatible.
- **Pick this when:** You're in the **Java/JVM/Eclipse ecosystem**, want weak file-level copyleft with strong commercial-friendliness, and GPL compatibility is not a hard requirement.

---

## Compatibility matrix

A combined/derivative work must satisfy *all* its components' licenses. "A → B compatible" means A-licensed code can be incorporated into a B-licensed work.

| From ↓ / Into → | GPL-2.0-only | GPL-3.0 | AGPL-3.0 | LGPL-3.0 | MPL-2.0 | Apache-2.0 / MIT |
|---|---|---|---|---|---|---|
| **Permissive (MIT/BSD)** | Yes | Yes | Yes | Yes | Yes | Yes |
| **Apache-2.0** | **No** (patent clause) | **Yes** (one-way) | Yes | Yes | Yes | Yes |
| **MPL-2.0** (default) | Yes* | Yes* | Yes* | Yes* | Yes | No (stays MPL at file level) |
| **LGPL-3.0** | No | Yes | Yes | Yes | No | No |
| **GPL-2.0-only** | Yes | **No** | No | No | No | No |
| **GPL-3.0** | No | Yes | Yes | No | No | No |
| **AGPL-3.0** | No | Yes | Yes | No | No | No |

\* via MPL-2.0's default Secondary-License (§3.3) compatibility, unless marked "Incompatible With Secondary Licenses" (Exhibit B).

**Key one-way / gotcha facts:**
- **Apache-2.0 → GPLv3 is one-way:** Apache code can go into a GPLv3 project, not the reverse.
- **Apache-2.0 is incompatible with GPL-2.0-only** (patent-termination = extra restriction). This is why the Linux kernel (GPLv2-only) can't take Apache code.
- **GPL-2.0-only and GPLv3 are mutually incompatible.** Only `GPL-2.0-or-later` can flow into a GPLv3 work.
- **MPL-2.0 is GPL-compatible by default**, unless the author opted out with Exhibit B.
- **EPL-2.0 is GPL-incompatible** unless the author opts in via the Secondary-License (GPL) designation.

---

## Decision sub-tree: "I want it open, but no competitor running it as a closed hosted service"

1. **Is it server-side / network-accessible software (web app, API, SaaS backend)?**
   - **Yes →** Use **AGPL-3.0**. §13 means a competitor who *modifies* your code and offers it to network users must give those users the modified source. Strongest OSI-approved deterrent against a closed SaaS fork.
   - **No (desktop/CLI app, library, embedded) →** AGPL's network clause does nothing extra; use **GPL-3.0** (whole-work copyleft on distribution) or **LGPL/MPL** for proprietary-combination friendliness.

2. **Understand AGPL's limits before relying on it:** it does **not forbid** commercial/hosted use, does **not** force patches back to *you*, only triggers on **modification + network interaction**, and reaches only the AGPL work and its corresponding source. A competitor can still legally compete by **publishing their fork**.

3. **If AGPL isn't enough** (you want to actually *prevent* hosted monetization), you must leave OSI open source → **SSPL / BSL / FSL / Elastic-2.0 / Commons Clause**. See `source-available.md`. (The Neo4j litigation is a cautionary tale about stapling extra restrictions onto AGPL text.) If a true OSS badge matters, **AGPL-3.0 is the strongest option that stays open source.**

---

## GPL linking exceptions — granting extra permissions without editing the GPL

You must **never modify the GPL/AGPL/LGPL license text itself**. Instead you **add an *exception*** — an extra permission layered on top — and reference it in your file headers. A **linking exception** lets others link your GPL'd code with otherwise-incompatible code without the combined work becoming GPL-subject. Canonical examples:

- **GPL + Classpath Exception** (OpenJDK, GNU Classpath): "give you permission to link this library with independent modules to produce an executable, regardless of the license terms of those modules, and to distribute the resulting executable under terms of your choice." SPDX: `GPL-2.0-with-classpath-exception`.
- **GCC Runtime Library Exception** — lets GCC's runtime be linked into programs compiled by GCC without forcing them to be GPL.

**How to add one correctly:**
1. Keep the unmodified GPL/LGPL/AGPL text in `LICENSE`/`COPYING`.
2. Write the exception as a **separate clause** (own paragraph/file), referencing the GPL it modifies.
3. In **each source file's header**, designate that file as subject to the exception — e.g., "[Owner] designates this particular file as subject to the 'Classpath' exception as provided in the LICENSE file."

This *unedited license body + separate exception + per-file designation* pattern is exactly how LGPL-3.0 itself works. GPLv3's **Section 7** formally authorizes such "additional permissions."

---

## Real-world projects on each license

- **AGPL-3.0:** Grafana (relicensed from Apache-2.0 in 2021), Loki/Tempo, Mastodon, Nextcloud, MinIO; MongoDB was AGPL until SSPL in 2018.
- **GPL-3.0 / GPL-2.0:** Linux kernel (GPL-2.0-**only**), Git, GCC, GIMP, Bash, WordPress (GPL-2.0+).
- **LGPL-2.1 / LGPL-3.0:** FFmpeg (LGPL-2.1+ core), GTK, glibc, Qt (LGPL-3.0 option).
- **MPL-2.0:** Mozilla Firefox & Thunderbird, parts of LibreOffice.
- **EPL-2.0:** Eclipse IDE, JUnit 5, Jakarta EE components, OpenJ9.

---

## 2024–2026 context worth knowing

- **Neo4j v. Suhy/PureThink (Ninth Circuit, Case 24-5538)** was the live copyleft case of 2025–2026, centered on AGPLv3 **§7** (whether a licensee may strip an added "Commons Clause"). FSF and SFC both filed amicus briefs on the side of user freedom; pending as of mid-2026. An adverse ruling could legitimize bolting proprietary restrictions onto GPL-family licenses.
- **Relicensing trend:** infrastructure vendors moving from permissive/OSS to AGPL (Grafana) or to source-available non-OSS (MongoDB→SSPL, HashiCorp→BSL, Elastic→SSPL/Elastic then re-adding AGPL in 2024) to fight cloud free-riding. AGPL remains the **strongest option still OSI-approved**; SSPL/BSL are explicitly *not*.
- **SPDX hygiene:** tooling now expects explicit `-only` / `-or-later` GNU identifiers; bare `GPL-2.0` / `GPL-3.0` / `LGPL-*` are deprecated and throw warnings.

---

### Sources
- SPDX License List · GNU: AGPL-3.0, "Identify licenses clearly," License list, License compatibility, GCC Runtime exception FAQ · choosealicense metadata · Apache "GPL compatibility" · Mozilla MPL-2.0 FAQ · FOSSA EPL · AGPL §13: Opensource.com, "Reading AGPL" (Kyle Mitchell), Mend "SaaS loophole" · Neo4j case: The Register, FSF amicus, SFC amicus · Wikipedia (Tivoization, MPL, GPL linking exception)
