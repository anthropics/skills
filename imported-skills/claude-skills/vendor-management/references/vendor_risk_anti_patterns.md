# Vendor Risk Anti-Patterns — Lessons from Real Breaches

The strongest argument for serious TPRM discipline is post-mortems from real third-party-originated incidents. This reference catalogues seven canonical breaches and the operational anti-patterns each one demonstrates.

The point of this reference is **not** to scare. The point is: every one of these incidents had a vendor-management anti-pattern at its root, and most of them were avoidable with the discipline this skill enforces.

## 1. SolarWinds Orion (2020) — Fourth-party / supply-chain compromise

Russian state-aligned actors (UNC2452 / Cozy Bear) inserted backdoor code into the SolarWinds Orion software update pipeline. ~18,000 organizations installed the trojanized update; ~100 (including U.S. federal agencies and major enterprises) had follow-on intrusions.

**Anti-patterns demonstrated:**
- **No software supply-chain verification.** The orgs that installed the update never verified the integrity of the binary beyond "the vendor's update server said so."
- **Implicit trust in tier-1 monitoring vendor.** Orion was deployed with extraordinary network access; no one re-evaluated whether that access level was justified.
- **No fourth-party visibility.** SolarWinds' own dev pipeline was the actual breach point — most customers had never asked who SolarWinds' suppliers were.

Source: CISA Alert AA20-352A (Dec 2020). https://www.cisa.gov/news-events/cybersecurity-advisories/aa20-352a

## 2. Target / Fazio Mechanical (2013) — HVAC vendor pivot

The 40M-card Target breach originated through Fazio Mechanical Services, a refrigeration / HVAC vendor with billing-system access to Target's network. Attackers phished Fazio, used Fazio's credentials to access Target's vendor portal, and pivoted from there into the POS network.

**Anti-patterns demonstrated:**
- **Excessive vendor network access.** An HVAC vendor needed network access to a vendor portal — fine. But that network was not segmented from POS systems, which is the failure.
- **No vendor risk tier evaluation.** Fazio was probably classified as tier-3 (a maintenance vendor). But the **access** they had made them effectively tier-1.

**Lesson:** Risk tier ≠ business criticality. A janitorial vendor with badge-system access can be a tier-1 attack surface.

Source: U.S. Senate Commerce Committee Report (Mar 2014). https://www.commerce.senate.gov/services/files/24d3c229-4f2f-405d-b8db-a3a67f183883

## 3. NotPetya / M.E.Doc (2017) — Trusted update mechanism weaponized

The NotPetya malware was injected via the update mechanism of M.E.Doc, a Ukrainian tax-reporting software used by ~80% of Ukrainian businesses. Spillover damage hit Maersk, FedEx (TNT), Merck, Mondelez — total damages > $10 billion globally. Maersk alone reported ~$300M loss and a 10-day operational outage.

**Anti-patterns demonstrated:**
- **Trusted-update-channel assumption.** No one verified the signed updates from M.E.Doc — its update key had been compromised for months.
- **Geographic concentration without geographic diversification.** Maersk's exposure was through a Ukrainian subsidiary; the parent had no breakglass for losing 100% of that subsidiary's systems for two weeks.

**Lesson:** A vendor used by 80%+ of your local market is effectively a single point of failure.

Source: Wired's Maersk NotPetya retrospective by Andy Greenberg (Aug 2018). https://www.wired.com/story/notpetya-cyberattack-ukraine-russia-code-crashed-the-world/

## 4. Capital One (2019) — AWS misconfiguration via former employee

A former AWS employee exploited a Capital One server-side request forgery (SSRF) vulnerability to access 100M+ customer records held in S3. Total cost to Capital One: ~$190M in regulatory fines + settlement.

**Anti-patterns demonstrated:**
- **Shared-responsibility model misunderstood.** Capital One assumed AWS would catch the misconfiguration. AWS's model puts misconfiguration responsibility on the customer.
- **No third-party penetration testing of the cloud config.** A reasonably scoped TPRM-driven pen test would have caught the SSRF.

**Lesson:** Cloud vendor due diligence must include "what is **my** responsibility under their shared-responsibility model?" — not just "are they SOC2?"

Source: Capital One incident summary + OCC consent order (Aug 2020). https://occ.gov/news-issuances/news-releases/2020/nr-occ-2020-101.html

## 5. Verkada (2021) — Camera vendor super-admin compromise

A hacking group obtained super-admin credentials to Verkada, a cloud-based security-camera vendor. Result: live-feed access to 150,000 cameras across hospitals, prisons, schools, Tesla factories, and corporate offices. The credentials were apparently exposed in a public Jenkins server.

**Anti-patterns demonstrated:**
- **Super-admin tooling without MFA enforcement.** Verkada had a super-admin role that bypassed customer-tenant boundaries — and apparently wasn't MFA-enforced.
- **No customer-side visibility into vendor admin actions.** Customers had no way to detect that vendor super-admins had viewed their feeds.

**Lesson:** For any SaaS handling sensitive data, ask: "Do your engineers have super-admin access to my tenant? How is that access logged and how can I audit it?"

Source: Bloomberg reporting (Mar 2021). https://www.bloomberg.com/news/articles/2021-03-09/hackers-expose-tesla-jails-in-breach-of-150-000-security-cameras

## 6. Okta (2022) — Lapsus$ / Sitel third-party support compromise

The Lapsus$ group compromised a Sitel customer-support engineer who had remote-support tooling access to Okta tenant data. Window of access: ~5 days. Okta's initial public disclosure was widely criticized as too slow and underplayed.

**Anti-patterns demonstrated:**
- **Subcontractor-of-subcontractor risk.** Sitel was Okta's outsourced support; the compromised engineer was Sitel's. Most Okta customers had no idea Sitel existed.
- **Slow disclosure of vendor incidents to downstream customers.** Customers found out about the breach months after Okta became aware internally.

**Lesson:** Contractually require your tier-1 vendors to disclose incidents within 24-72 hours, not "when investigation completes." This is now standard in DPAs but often missing from older contracts.

Source: Okta's official Lapsus$ statement updates (Mar-Apr 2022). https://www.okta.com/blog/2022/03/updated-okta-statement-on-lapsus/

## 7. Log4Shell / log4j (2021) — Open-source dependency as a vendor

CVE-2021-44228 in the log4j Java logging library affected ~3 billion devices and embedded in tens of thousands of commercial vendor products. Most affected orgs had no idea log4j was in their supply chain because it was a transitive dependency of vendor SaaS, not a direct dependency.

**Anti-patterns demonstrated:**
- **Open-source dependencies treated as "not vendors."** They are. They have SLAs (effectively zero), have security disclosure processes (variable), and have maintainers who can disappear.
- **No SBOM (Software Bill of Materials) requested from vendors.** Customers couldn't tell which of their vendors were affected.

**Lesson:** Add an SBOM requirement to vendor contracts for tier-1 and tier-2 vendors. Without an SBOM, every new transitive CVE is a multi-week fire drill.

Source: CISA Apache Log4j Vulnerability Guidance. https://www.cisa.gov/news-events/news/apache-log4j-vulnerability-guidance

## Synthesis: The 7 vendor-risk anti-patterns to avoid

1. **Treat all vendors at the same tier.** Tier-1 vendors get quarterly review + full SIG. Tier-2 semi-annual. Tier-3 at renewal. Network-access privilege is the override — see Target.
2. **Annual review is enough.** It isn't. Continuous monitoring (Forrester) + quarterly QBR is the operating cadence.
3. **Trust the vendor security questionnaire without verification.** Ask for the SOC2 Type II report. Read the exceptions section. Verify cert validity dates.
4. **No break-glass plan for a tier-1 vendor.** If the vendor disappears tomorrow (acquisition, bankruptcy, NotPetya-class outage), what's the 72-hour plan? Document it before you need it.
5. **No offboarding checklist when vendor changes hands.** SolarWinds and Okta both demonstrate why you need a data-deletion + access-revocation runbook ready to execute.
6. **Ignore fourth parties.** Your vendors have vendors. For tier-1, ask: "Who are your top 5 subcontractors? Which ones have access to my data?"
7. **No SBOM for SaaS vendors.** When the next log4j-class CVE drops, you want to be able to query a list, not start an email thread.

The risk classifier in this skill catches most of these via the 4-vector classification, but the **mitigations** are the human-in-the-loop step. Use them.
