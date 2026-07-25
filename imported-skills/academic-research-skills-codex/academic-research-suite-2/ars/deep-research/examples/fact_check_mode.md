---
scenario: Fact-checking claims about Taiwan's higher education
mode: fact-check
agents_used:
  - source_verification_agent
input: User provides 7 claims about Taiwan's higher education
output: Claim-by-claim verification report + verification summary
note: This example uses Taiwan HEI data. The fact-check mode works with any topic — just provide claims about your research area (e.g., "US enrollment has declined 15% since 2010", "EU universities spend more on research than US ones").
---

# Fact-Check Mode Example: Taiwan Higher Education Claim Verification

This example demonstrates the complete workflow of `fact-check` mode using Taiwan higher education as a domain-specific case. The same workflow applies to any research domain — simply replace the claims with statements relevant to your field. The source_verification_agent verifies each claim against available evidence.

---

## User Request

```
Please fact-check the following claims about Taiwan's higher education:

1. Taiwan currently has 152 colleges and universities.
2. HEEACT was established in 2005 and is the only institution responsible for higher education accreditation in Taiwan.
3. The average student-to-faculty ratio in Taiwan's universities is 1:20.
4. Declining birth rates have caused more than 10 universities in Taiwan to complete their exit or closure procedures.
5. Taiwan's higher education expenditure as a percentage of GDP is approximately 0.4%, lower than the OECD average.
6. The vacancy rate for the 2024 academic year university examination distribution admission reached 15%.
7. Taiwan produces approximately 4,000 doctoral graduates per year, of which more than half enter academia as faculty.
```

---

## source_verification_agent Verification Report

### Claim 1

> "Taiwan currently has 152 colleges and universities."

**Verdict:** Warning — Partially True

**Verification Basis:** According to MOE's higher education overview statistics for Academic Year 112 (2023-2024), Taiwan's total number of higher education institutions is 145 (including universities, independent colleges, and junior colleges). This number continues to change due to school closures or mergers. If military and police academies (e.g., National Defense University, Central Police University) are included, the total increases slightly but still does not reach 152. "152" likely references data from an earlier year (approximately Academic Year 108-109), when more schools were still operating.

**Source:** MOE Statistics Division, *Higher Education Overview Statistics*, Academic Year 112 (2023-2024).

**Correction Suggestion:** Should be updated to the latest academic year figure, with clear definition of the statistical scope (whether military/police academies, religious seminary institutions, and other special types are included).

---

### Claim 2

> "HEEACT was established in 2005 and is the only institution responsible for higher education accreditation in Taiwan."

**Verdict:** Warning — Partially True

**Verification Basis:** The Higher Education Evaluation and Accreditation Council of Taiwan (HEEACT) was indeed established on December 26, 2005 — this part is correct. However, the claim of "only" is inaccurate. Taiwan's higher education evaluation system has promoted diversification since 2017. In addition to HEEACT, the Taiwan Assessment and Evaluation Association (TWAEA) and the Institute of Engineering Education Taiwan (IEET), among others, are also recognized by the MOE to conduct specific types of quality assurance accreditation. Furthermore, from the third cycle of institutional accreditation starting in 2023, universities are also allowed to choose self-conducted external evaluation. Therefore, HEEACT is the most prominent but not the only accreditation body.

**Sources:**
- HEEACT official website, About Us > History
- MOE, "Principles for Reviewing University Self-Evaluation Results" (2017 revision)
- MOE, "Implementation Plan for Commissioned Quality Assurance Accreditation of Higher Education Institutions" (Academic Year 116)

**Correction Suggestion:** Revise to "HEEACT was established in 2005 and is one of the most prominent higher education accreditation bodies in Taiwan."

---

### Claim 3

> "The average student-to-faculty ratio in Taiwan's universities is 1:20."

**Verdict:** Warning — Partially True

**Verification Basis:** The student-to-faculty ratio varies depending on the calculation formula used. The MOE's published full-school student-to-faculty ratio (including full-time and part-time equivalents) differs significantly from one calculated using only full-time faculty. According to Academic Year 112 data, the equivalent student-to-faculty ratio for public university daytime programs is approximately 18:1 to 22:1 (varies by institution), while private universities are approximately 22:1 to 28:1. The overall average is approximately 23:1, not 20:1. Additionally, "1:20" is an unconventional notation — the student-to-faculty ratio is typically written as "20:1" (20 students per 1 faculty), not "1:20."

**Source:** MOE Statistics Division, *Student and Faculty Statistics by Institution*, Academic Year 112.

**Correction Suggestion:** Revise to "The equivalent student-to-faculty ratio for Taiwan's daytime higher education programs is approximately 23:1, with significant differences between public and private institutions," and use the correct notation format.

---

### Claim 4

> "Declining birth rates have caused more than 10 universities in Taiwan to complete their exit or closure procedures."

**Verdict:** Verified

**Verification Basis:** According to MOE announcements and the implementation status of the "Private Senior High School and Above Exit Act," as of early 2025, institutions that have completed enrollment suspension or closure procedures include: Kao Fong College of Digital Contents (closed 2014), Yung Ta Institute of Technology (enrollment suspended 2014, closed 2021), Kao-Mei College of Health Care and Management (enrollment suspended 2018), Asia-Pacific Institute of Creativity (enrollment suspended 2019), Nan Jeon University of Science and Technology (enrollment suspended 2020), Toko University (enrollment suspended 2020), Taiwan Tourism College (closed 2022), Lan Yang Institute of Technology (enrollment suspended 2022), Chung Chou University of Science and Technology (enrollment suspended 2023), Hechun Institute of Technology (enrollment suspended 2023), Tatung Institute of Technology (enrollment suspended 2023), Taiwan Shoufu University (closed 2023), MingDao University (enrollment suspended 2024), TransWorld University (enrollment suspended 2024), among others. The total exceeds 10 institutions; this claim is verified.

**Sources:**
- MOE, annual higher education institution enrollment suspension/closure announcements
- MOE, "Private Senior High School and Above Exit Act" implementation progress report

**Note:** This number continues to increase; some schools are in the "special counseling" stage and have not yet completed their exit process.

---

### Claim 5

> "Taiwan's higher education expenditure as a percentage of GDP is approximately 0.4%, lower than the OECD average."

**Verdict:** Warning — Partially True

**Verification Basis:** This claim requires distinguishing between "government public expenditure" and "total expenditure (including private)." According to MOE statistics, Taiwan's government public expenditure on higher education as a percentage of GDP is approximately 0.4-0.5%, which is indeed lower than the OECD average of approximately 0.9% (Education at a Glance 2021 data). However, when private expenditure (tuition, corporate sponsorship, etc.) is included, Taiwan's total higher education expenditure as a percentage of GDP is approximately 1.2-1.3%, approaching the OECD average of 1.5%. Therefore, the "0.4%" figure only reflects the public expenditure portion. The claim does not distinguish between public and private expenditure, which can be misleading.

**Sources:**
- MOE Statistics Division, *Education Expenditure Statistics*, Year 112
- OECD, *Education at a Glance 2023*, Table C2.1

**Correction Suggestion:** Revise to "Taiwan's public expenditure on higher education as a percentage of GDP is approximately 0.4-0.5%, lower than the OECD average of 0.9%; however, when including private expenditure, the total proportion is approximately 1.2-1.3%, narrowing the gap."

---

### Claim 6

> "The vacancy rate for the 2024 academic year university examination distribution admission reached 15%."

**Verdict:** Unverifiable

**Verification Basis:** The University Entrance Exam Center for Placement publishes distribution results annually, but the definition and calculation method of "vacancy rate" may vary across reports. The "15%" cited here lacks a clear source and calculation basis: is the denominator the approved enrollment quota? Or the remaining quota after subtracting admissions through other channels? Media-reported figures in recent years vary widely, from single-digit percentages to over 20%, depending on the calculation method and whether only general universities or also technical colleges are included. Furthermore, the 2024 academic year distribution results should be based on the official announcement from the University Entrance Exam Center for Placement, not media estimates.

**Source:** Unable to obtain precise official data to verify this specific figure.

**Correction Suggestion:** Cite the official statistics from the University Entrance Exam Center for Placement, clearly define the calculation method for the vacancy rate, and specify the data source year.

---

### Claim 7

> "Taiwan produces approximately 4,000 doctoral graduates per year, of which more than half enter academia as faculty."

**Verdict:** False

**Verification Basis:** The first part is roughly correct — according to MOE statistics, the number of doctoral degrees awarded annually in Taiwan in recent years is approximately 3,800 to 4,200, making "approximately 4,000" a reasonable claim. However, the second part — "more than half enter academia as faculty" — does not match available data. According to the NSTC (formerly MOST) doctoral talent tracking survey and the MOE graduate career tracking survey, the proportion of doctoral graduates entering academia (as full-time faculty at higher education institutions) in recent years is approximately 25-30%. As faculty vacancies at higher education institutions have significantly decreased due to declining birth rates, new faculty positions have declined year by year, and the proportion of doctoral graduates entering academia continues to fall. Most doctoral graduates flow to industry, research institutions, or postdoctoral positions, rather than directly becoming full-time faculty.

**Sources:**
- MOE Statistics Division, *Graduate Career Tracking Survey*
- NSTC, *Doctoral Talent Development and Employment Survey*
- MOE Statistics Division, *Degrees Awarded at Higher Education Institutions*, Academic Years 111-112

**Correction Suggestion:** Revise to "Taiwan produces approximately 4,000 doctoral graduates per year, of which approximately 25-30% enter higher education institutions as full-time faculty. This proportion continues to decline as declining birth rates reduce faculty vacancies."

---

## Verification Summary Report

### Overview

| # | Claim Summary | Verdict | Severity |
|------|----------|------|--------|
| 1 | 152 higher education institutions | Warning — Partially True | Low — outdated figure |
| 2 | HEEACT is the only accreditation body | Warning — Partially True | Medium — factual error |
| 3 | Student-to-faculty ratio 1:20 | Warning — Partially True | Low — approximate but notation error |
| 4 | Over 10 schools have exited | Verified | N/A |
| 5 | HE expenditure 0.4% of GDP | Warning — Partially True | Medium — public vs private not distinguished |
| 6 | Vacancy rate 15% | Unverifiable | High — cannot verify |
| 7 | Over half of doctoral graduates enter academia | False | High — seriously inaccurate |

### Verification Statistics

- Verified: 1 claim (14%)
- Warning — Partially True: 4 claims (57%)
- False: 1 claim (14%)
- Unverifiable: 1 claim (14%)

### Overall Assessment

The overall accuracy of this set of claims is low. Of the 7 claims, only 1 is completely correct, 4 are partially correct but have omissions or insufficient precision, 1 is clearly false, and 1 cannot be verified. The most serious issue is Claim 7 (doctoral graduate career path), which diverges significantly from actual data and could lead to incorrect conclusions if used in policy discourse.

### Verification Recommendations

1. All data should indicate the specific source and year
2. Claims involving proportions or percentages should clearly define the numerator and denominator
3. Claims describing institutional systems (such as the accreditation system) should reflect the latest institutional changes
4. Claims where precise data cannot be obtained should be qualified as "estimated" or "according to media reports" rather than stated as established facts
