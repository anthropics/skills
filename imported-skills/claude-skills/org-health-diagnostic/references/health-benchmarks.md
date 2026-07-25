# Org Health Benchmarks by Stage

Benchmarks for scoring each dimension at Seed, Series A, Series B, and Series C.

---

## Financial Health Benchmarks (CFO)

| Metric | Seed | Series A | Series B | Series C |
|--------|------|----------|----------|----------|
| Runway (green) | >18mo | >12mo | >12mo | >18mo |
| Runway (yellow) | 9-18mo | 6-12mo | 6-12mo | 9-18mo |
| Runway (red) | <9mo | <6mo | <6mo | <9mo |
| Burn multiple (green) | <3x | <2x | <1.5x | <1x |
| Burn multiple (yellow) | 3-5x | 2-3x | 1.5-2.5x | 1-1.5x |
| Gross margin (green) | >50% | >65% | >70% | >75% |
| MoM growth (green) | >15% | >10% | >7% | >5% |
| Revenue concentration | <30% | <25% | <15% | <10% |

**Stage-specific notes:**
- **Seed:** Burn multiple is looser — you're investing in PMF, not efficiency
- **Series A:** Efficiency starts to matter; board watching burn multiple closely
- **Series B:** Capital efficiency is table stakes; burn >2x raises serious questions
- **Series C:** Approaching path to profitability; investors expect <1.5x

---

## Revenue Health Benchmarks (CRO)

| Metric | Seed | Series A | Series B | Series C |
|--------|------|----------|----------|----------|
| NRR (green) | >100% | >110% | >115% | >120% |
| NRR (yellow) | 90-100% | 100-110% | 105-115% | 110-120% |
| NRR (red) | <90% | <100% | <105% | <110% |
| Logo churn (green) | <15%/yr | <10%/yr | <7%/yr | <5%/yr |
| Pipeline coverage | >2x | >3x | >3.5x | >4x |
| CAC payback (green) | <24mo | <18mo | <12mo | <9mo |
| Win rate (green) | >20% | >25% | >28% | >30% |
| ACV trend | growing | growing | growing | growing |

**What "green" NRR signals:**
- >100%: product creates value; expansion outpaces churn
- >110%: customers grow inside your platform; land-and-expand working
- >120%: exceptional — net negative churn; growth from existing base alone
- <100%: customers leave faster than others expand; structural retention problem

**Warning: NRR can mask problems.** NRR of 110% with 25% logo churn means you're retaining revenue from large customers while losing small ones. Check both.

---

## Product Health Benchmarks (CPO)

| Metric | Seed | Series A | Series B | Series C |
|--------|------|----------|----------|----------|
| NPS (green) | >30 | >40 | >45 | >50 |
| NPS (yellow) | 10-30 | 20-40 | 30-45 | 40-50 |
| NPS (red) | <10 | <20 | <30 | <40 |
| DAU/MAU (green) | >25% | >35% | >40% | >45% |
| Core feature adoption | >40% | >55% | >65% | >70% |
| Time-to-value | <7 days | <5 days | <3 days | <2 days |
| CSAT | >4.0/5 | >4.2/5 | >4.3/5 | >4.4/5 |

**PMF proxy metrics:**
- "Very disappointed" if product disappeared: >40% = strong PMF signal (Sean Ellis test)
- 6-month retention cohort: >40% is healthy; <20% means PMF not yet achieved
- Organic referral rate: >20% of new users from referrals = product-led growth signal

**What low DAU/MAU actually means:**
- <20% DAU/MAU for a daily-use product = product isn't integrated into workflow
- DAU/MAU benchmarks vary by use case: email tool (daily use expected) vs. annual budget tool (weekly use is fine)
- Always compare to category, not absolute benchmarks

---

## Engineering Health Benchmarks (CTO)

DORA metrics are the industry standard (Google's DevOps Research and Assessment):

| Metric | Elite | High | Medium | Low |
|--------|-------|------|--------|-----|
| Deployment frequency | Multiple/day | Weekly | Monthly | <Monthly |
| Lead time for changes | <1 hour | 1 day-1 week | 1-6 months | >6 months |
| Change failure rate | <5% | 5-10% | 10-15% | >15% |
| MTTR | <1 hour | <1 day | 1 day-1 week | >1 week |

**Translation for startup stages:**

| Metric | Seed | Series A | Series B | Series C |
|--------|------|----------|----------|----------|
| Deploy freq (green) | Weekly | Daily | Daily | Multiple/day |
| MTTR (green) | <4h | <2h | <1h | <30min |
| Change failure rate (green) | <15% | <10% | <7% | <5% |
| Tech debt ratio (green) | <30% | <25% | <20% | <15% |
| P0 incidents/month (green) | <3 | <2 | <2 | <1 |

**Warning signs unique to early-stage:**
- Bus factor = 1 on critical systems (one person knows how it works) → immediate risk
- No on-call rotation → incidents wake the same person every time → attrition risk
- No staging environment → production is the test environment → change failure spike risk
- "We'll fix it after launch" for >12 months → tech debt is now a strategic problem

---

## People Health Benchmarks (CHRO)

| Metric | Seed | Series A | Series B | Series C |
|--------|------|----------|----------|----------|
| Regrettable attrition (green) | <15% | <12% | <10% | <8% |
| Regrettable attrition (red) | >25% | >18% | >15% | >12% |
| eNPS (green) | >20 | >30 | >35 | >40 |
| Time-to-fill (green) | <60d | <45d | <45d | <30d |
| Internal promotion rate | >20% | >25% | >30% | >35% |
| Manager span of control | 1:4-8 | 1:5-8 | 1:6-10 | 1:6-12 |
| % under-performers managed out | 3-5% | 3-5% | 3-5% | 3-5% |

**Regrettable vs non-regrettable attrition:**
- Regrettable: you'd rehire them immediately; they leave for better opportunity
- Non-regrettable: performance-based exits; mutual agreement; role evolution
- Only regrettable attrition signals health problems

**eNPS benchmarks by sector:**
- Tech startups: >30 is good; >50 is exceptional
- General: >0 means more promoters than detractors (minimum bar)
- Below -10: serious cultural issue; expect more attrition

**The cascade warning:** People health is a leading indicator, not lagging. By the time attrition shows up in your numbers, the next wave is already decided. Watch eNPS and engagement quarterly.

---

## Operational Health Benchmarks (COO)

| Metric | Seed | Series A | Series B | Series C |
|--------|------|----------|----------|----------|
| OKR completion rate (green) | >60% | >70% | >75% | >80% |
| Decision cycle time (green) | <3 days | <2 days | <48h | <24h |
| Process maturity level | 1-2 | 2-3 | 3-4 | 4-5 |
| Cross-functional delivery (on time) | >60% | >70% | >75% | >80% |
| Leadership team tenure | N/A | >12mo avg | >18mo avg | >24mo avg |

**OKR interpretation:**
- 100% completion = OKRs were too easy (not ambitious enough)
- 60-70% completion = appropriate stretch, realistic execution
- <40% completion = disconnect between strategy and capacity, or OKRs set without buy-in
- OKRs nobody can remember = OKRs that don't guide decisions = wasted exercise

---

## Security Health Benchmarks (CISO)

| Metric | Seed | Series A | Series B | Series C |
|--------|------|----------|----------|----------|
| Security incidents (P1+) | 0-1/yr | 0/yr | 0/yr | 0/yr |
| Pen test cadence | Annual | Annual | Bi-annual | Bi-annual |
| SOC 2 Type II | Roadmap | In progress | Complete | Complete |
| ISO 27001 | — | Roadmap | In progress | Complete |
| Security training completion | >80% | >90% | >95% | >95% |
| Critical CVE patching SLA | <72h | <48h | <24h | <12h |
| MFA coverage | >80% | >95% | 100% | 100% |
| Employee background checks | Key roles | All | All | All |

**Stage-specific compliance priorities:**
- **Seed:** Basic hygiene (MFA, encryption, access control)
- **Series A:** SOC 2 Type I on roadmap; sales increasingly requiring it
- **Series B:** SOC 2 Type II complete; ISO 27001 if selling to enterprise/EU
- **Series C:** Full compliance stack; GDPR, HIPAA if applicable

---

## Market Health Benchmarks (CMO)

| Metric | Seed | Series A | Series B | Series C |
|--------|------|----------|----------|----------|
| CAC trend | Acceptable | Improving | Improving | Stable/improving |
| Organic % of pipeline | >30% | >40% | >50% | >60% |
| Win rate (green) | >20% | >25% | >27% | >30% |
| Competitive win rate | >40% | >45% | >50% | >55% |
| Brand awareness in ICP | Low OK | Growing | Recognized | Leader |
| Content-to-pipeline conversion | Tracked | >2% | >3% | >4% |

---

## How Dimensions Interact

Understanding interdependencies helps predict cascades before they happen:

```
People Health degrades
    ↓ (60-90 day lag)
Engineering Health degrades (velocity drops, debt rises)
    ↓ (30-60 day lag)
Product Health degrades (features slip, quality drops)
    ↓ (60-90 day lag)
Revenue Health degrades (churn rises, deals stall)
    ↓ (30-60 day lag)
Financial Health degrades (cash gap, runway shortens)
    ↓ (immediate)
People Health degrades further (hiring freeze, morale)
```

**The prevention prescription:**
- Fix People and Engineering problems first — they cascade to everything
- Financial problems require immediate response (no lag)
- Revenue problems are often symptoms of Product or People problems upstream
- Security problems can cascade fast (breach → customer churn → financial → people)

**Weighting by stage (for overall score):**

| Dimension | Seed | Series A | Series B | Series C |
|-----------|------|----------|----------|----------|
| Financial | 30% | 25% | 20% | 20% |
| Revenue | 20% | 25% | 25% | 25% |
| People | 20% | 15% | 15% | 15% |
| Product | 15% | 15% | 15% | 15% |
| Engineering | 10% | 10% | 10% | 10% |
| Operations | 5% | 5% | 8% | 8% |
| Market | — | 5% | 5% | 5% |
| Security | — | — | 2% | 2% |
