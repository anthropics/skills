---
name: turkish-academic-writing
description: Tier-1 keyword-triggered skill for Turkish-first academic writing with APA 7, IMRAD structure, and journal targeting (TR Dizin, ULAKBIM, SSCI). Includes anti-AI-pattern detection, citation verification, and bilingual abstract generation. Use when the user writes Turkish or bilingual academic manuscripts, theses, or grant proposals.
license: MIT
author: Onour Impram (Hezarfen)
version: 0.1.0
---

# Turkish Academic Writing — Skill

> Turkish-first academic writing assistant with APA 7 enforcement, IMRAD structure validation, anti-AI-pattern detection, and journal targeting for Turkish and international venues.

## When to use

Trigger this skill when the user:
- Writes Turkish or bilingual (Turkish + English) academic manuscripts
- Drafts thesis chapters, journal articles, or grant proposals in Turkish
- Needs APA 7 citation in Turkish edition
- Targets Turkish indices (TR Dizin, ULAKBIM TR Index) or SSCI journals with Turkish authors
- Wants to detect AI writing patterns in their own drafts and rewrite for natural academic voice
- Generates bilingual abstracts (Turkish + English) for journal submissions

## Outputs

This skill produces:
1. **Manuscript drafts** in IMRAD structure with APA 7 in-text citations
2. **Citation verification reports** flagging missing or malformed references
3. **Bilingual abstracts** (Turkish + English) with parallel keyword extraction
4. **AI-pattern detection reports** identifying inflated symbolism, vague attributions, AI vocabulary
5. **Journal-fit scores** for Turkish, SSCI, and open-access venues
6. **Method section templates** aligned with reporting guidelines (CONSORT, STROBE, PRISMA)

## How to use

### Step 1: Identify writing context

Ask the user:
- Manuscript type (thesis chapter, journal article, grant proposal, conference paper)
- Target language (Turkish-only, English-only, bilingual)
- Target venue (TR Dizin journal, SSCI Q1/Q2/Q3/Q4, open access)
- Section needed (Abstract, Introduction, Methods, Results, Discussion, Conclusion, References)

### Step 2: Apply IMRAD structure

For empirical research:
- **Introduction**: literature gap → research question → hypotheses (2-3 paragraf)
- **Methods**: design → participants → procedure → analysis (her birinin alt baslik)
- **Results**: descriptive statistics → inferential analyses → effect sizes
- **Discussion**: key findings → integration with prior work → limitations → implications
- **Conclusion**: 1-2 paragraf, no new findings introduced

For theoretical/review:
- **Introduction**: scope + significance
- **Background**: theoretical framework + key terms
- **Body**: thematic synthesis
- **Discussion**: gaps + future research

### Step 3: APA 7 Turkish edition rules

**In-text citation (Turkish narrative):**
- Tek yazar: (Smith, 2023) veya Smith (2023) "iddia etti"
- Iki yazar: (Smith ve Jones, 2023) — Turkce metinde "ve", Ingilizce metinde "&"
- 3+ yazar: (Smith vd., 2023) — Turkce "ve digerleri", Ingilizce "et al."
- Cite-while-writing rule: ilk gectiginde tum yazarlar yazilirsa cumle uzar — kisa form tercih edilir
- Sayfa numarasi: dogrudan alintida zorunlu (Smith, 2023, s. 45) — Turkce "s." (sayfa), Ingilizce "p."

**Reference list:**
- Soyad, A. A. (yyyy). Makale basligi. Dergi Adi, cilt(sayi), sayfa-araligi. https://doi.org/...
- Kitap: Soyad, A. A. (yyyy). Kitap basligi (italik). Yayinevi.
- Edited book chapter: Yazar, A. A. (yyyy). Bolum basligi. Editor (Ed.), Kitap basligi (s. xx-yy). Yayinevi.
- Online kaynak: DOI varsa kullan, yoksa stable URL + erisim tarihi (sadece dinamik icerik icin)

**Common errors to flag:**
- "ve diğerleri" yerine "vd." kullan (kisaltma kurali APA 7 with TR adaptation)
- DOI yoksa journal url ekleme zorunluluk degil, ama "https://doi.org/" formati zorunlu DOI varsa
- 3 yazar ilk gecisinde tum yazarlar listelenmez — ilk gecisten itibaren "vd." kullanilir
- Bibliography hanging indent 1.27 cm (0.5 inch) — APA 7 norm

### Step 4: Anti-AI-pattern detection

Tara metin icin Wikipedia "Signs of AI writing" + observed patterns:
- **Inflated symbolism**: "bu bulgular, bilgi okuryazarliginin temellerinin yeniden tanimlandigi bir doneme isaret etmektedir" → "bilgi okuryazarligi degisiyor"
- **Vague attributions**: "uzmanlar bildirmektedir ki" → spesifik kaynak ver
- **AI vocabulary**: "delve into", "tapestry", "navigating", "in the realm of", Turkce karsiliklari: "derinlemesine incelemek", "...alaninda gezinmek"
- **Negative parallelisms**: "...sadece X degil, ayni zamanda Y" — abartilmis kullanim
- **Em-dash overuse**: Ingilizcede tehlike isareti, Turkcede daha az ama yine de fark edilir
- **Promotional language**: "groundbreaking", "revolutionary" — akademik metinde yer almaz
- **Sequential transition words**: "Moreover, Furthermore, Additionally" arka arkaya — Turkce karsiliklari "Ayrica, Bunun yaninda, Buna ek olarak" — alternatif kullan

### Step 5: Bilingual abstract generation

Iki versiyonu paralel yaz:
- Turkce: 250-300 kelime, structured (Amac, Yontem, Bulgular, Sonuc)
- English: 200-250 word, structured (Aim, Method, Findings, Conclusion)
- 4-6 keyword (Turkce + English ayri liste)
- Cross-check: terminoloji tutarli mi (orn. "ozyeterlik = self-efficacy"; "ihtiyac doyumu = need satisfaction")

### Step 6: Journal targeting

**TR Dizin** (Turkce hakemli, Q1-Q4 ulusal):
- Klinik psikoloji: Klinik Psikoloji Dergisi, Turk Psikoloji Dergisi
- Saglik: Hacettepe Saglik Bilimleri Dergisi
- Egitim: Egitim ve Bilim, Hacettepe Universitesi Egitim Fakultesi Dergisi

**SSCI** (uluslararasi, Turkce yazarlar bilingual gonderebilir):
- Q1: Journal of Affective Disorders, Computers & Education, Cyberpsychology Behavior and Social Networking
- Q2: Internet Interventions, JMIR Mental Health, Frontiers in Psychology

**Open access (academic equity)**:
- PsyArXiv (preprint, hizli gorunurluk)
- PLOS ONE (mega journal)
- Frontiers in Psychiatry, Frontiers in Digital Health

**Mental health + AI ozel hedefler**:
- Nature Mental Health (Q1, prestige)
- The Lancet Digital Health (policy + clinical AI)
- JMIR Mental Health (digital therapy + interventions)
- AI & Society (interdisciplinary)

## Examples

See `examples/` for:
- `psychology-abstract-tr-en.md` — Turkish + English abstract pair
- `methods-section-sample.md` — Methods section with APA 7 in Turkish narrative
- `apa7-cite-validator-output.md` — sample citation verification report

## Scripts

`scripts/apa7-cite-validator.py` runs:
- Detect (Author, YYYY) patterns
- Cross-check against reference list section
- Flag missing/extraneous references
- Report orphan citations (in-text but not in references)
- Report orphan references (in references but not cited)

## References (skill-internal)

- **APA Style 7th Edition** (American Psychological Association, 2020)
- **Karadut, A.** (2023). *Bilimsel Yazim Klavuzu (Turkce APA 7 Adaptation)*. Pegem Akademi.
- **CONSORT 2010** Statement for randomized trials
- **STROBE 2007** Statement for observational studies
- **PRISMA 2020** Statement for systematic reviews
- **Wikipedia: Signs of AI writing** (May 2026 version)

## Contribution

PR to upstream `anthropics/skills`:
1. Fork [anthropics/skills](https://github.com/anthropics/skills)
2. Create branch: `add-turkish-academic-writing`
3. Copy this skill folder to `skills/turkish-academic-writing/`
4. Open PR with description: "Adds Turkish-first academic writing skill with APA 7 enforcement, IMRAD structure, journal targeting (TR Dizin + SSCI), and anti-AI-pattern detection."

## License

MIT — free to use, fork, modify.
