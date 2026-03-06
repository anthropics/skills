# Sensitivity, Analysis & Regional Research Patterns

## Handling Name Variations

Names change across borders, languages, time periods, and levels of literacy of the registrar. Common patterns:

| Original | Common Variants |
|---|---|
| Giuseppe | José (Portuguese/Spanish), Joseph (English/French) |
| Giovanni | João (Portuguese), Juan (Spanish), John (English) |
| Pietro | Pedro (Portuguese/Spanish), Peter (English) |
| Müller | Muller, Miller, Mueller |
| Jakub | Jacob, James |
| Władysław | Ladislaus, Ladislau |
| Catarina / Catharina / Caterina | All valid depending on era and registrar |

**Rule**: Record ALL variants in `alt_names`. Search databases with every variant. The same person's mother's surname might appear differently in every document.

## Confidence Levels

```
high   — Primary document (certificate, official record, parish register)
medium — Secondary source (oral history from direct witness, family Bible,
         newspaper, blog citing sources)
low    — Single oral source, unverified claim, conflicting information,
         or inference from indirect evidence
```

## Resolving Conflicts Between Sources

When sources disagree (and they WILL):

1. **Primary documents beat secondary sources.** A birth certificate beats a GEDCOM entry.
2. **Marriage certificates are often the most reliable** for ages and birthplaces (both parties stated under oath).
3. **Immigration records are unreliable for ages** — people routinely lied or guessed.
4. **Multiple independent sources agreeing** beats any single source.
5. **Contemporary records** (written at the time) beat retrospective ones (written years later).
6. **Church records pre-date civil records** in most countries and may have different (sometimes better) information.

Always document the conflict in the YAML, even after resolving:

```yaml
notes: |
  CONFLICT RESOLVED: Birth date
  - Marriage certificate (1923): "28 September 1897" → ACCEPTED (primary, contemporary)
  - GEDCOM from Ancestry: "28 June 1897" → REJECTED (likely transcription error)
  - Immigration record (1888): age 47 → ~1841 → REJECTED (ages unreliable)
```

## Dangerous Assumptions to Avoid

- "Same name = same person" — WRONG. Names were reused constantly, especially after a child died
- "This GEDCOM entry is correct" — MAYBE. GEDCOMs are full of unverified data
- "FamilySearch tree data is reliable" — SOMETIMES. Anyone can edit it. Check sources.
- "My relative remembers correctly" — VALUABLE BUT VERIFY. Birth orders, years, and even identities can be misremembered
- First children who died young often had their names reused for later siblings — common in Italian, Portuguese, and many other cultures

---

## The "Immigration Wall" Strategy

For families that immigrated, the critical transition point is:

```
Records in destination country (post-arrival)
        ↕  THE WALL — you need a bridge document
Records in country of origin (pre-departure)
```

**Bridge documents** (in order of usefulness):
1. **Marriage certificate in destination country** — often lists birthplace abroad
2. **Immigration/arrival record** — port of departure + age + family group
3. **Ship manifest** — origin, destination, sometimes exact town/parish
4. **Baptism of first child born after arrival** — parents' origins sometimes listed
5. **Death certificate** — sometimes lists birthplace (but often just the country)
6. **Naturalization records** — detailed personal history
7. **Passport** — issued by country of origin with exact birthplace

---

## Research Patterns by Origin

### General Timeline

- **Civil registration**: Started at different times in different countries — check when it began in your target region
- **Church records**: Often go back centuries before civil registration
- **Immigration peak eras**: Vary by destination country (e.g., 1870s-1920s for the Americas)

### Italian Ancestry
- **Antenati** (antenati.cultura.gov.it) — Italian state archives online, free, browse by province
- FamilySearch Italian collections organized by province + archive type
- Civil registration: 1809 (Southern Italy, Napoleonic) or 1871 (Northern Italy)
- Church records go back much further
- **Naming patterns**: First son after paternal grandfather, first daughter after paternal grandmother, second children after maternal grandparents. Dead children's names were reused.
- Contact the relevant Comune's civil registry office for specific certificates

### Portuguese Ancestry
- **CEPESE** (cepese.pt) — emigration database (passports, ship lists)
- **DigitArq** (digitarq.arquivos.pt) — national archives
- FamilySearch Portuguese collections (parish records by district)
- Civil registration began 1911; church records go back to the 1500s
- Watch for spelling variations between Portugal and destination countries

### Spanish Ancestry
- **PARES** (pares.mcu.es) — Portal de Archivos Españoles
- FamilySearch Spanish collections by province
- Civil registration began 1870

### Polish / Eastern European Ancestry
- **Geneteka** (geneteka.genealodzy.pl) — parish record index by surname + parish
- **Szukajwarchiwach** — Polish state archives
- Borders changed constantly — "Poland" may mean modern-day Ukraine, Lithuania, or Belarus
- Determine which empire controlled the region at the time (Russian, Prussian, or Austrian partition)

### German Ancestry
- **Archion** (archion.de) — Protestant church records
- **Matricula** (data.matricula-online.eu) — Catholic church records
- FamilySearch German collections are extensive
- Germany was many separate states before 1871 — records are organized by state/region

### Japanese Ancestry
- Koseki (family register) system is extremely detailed if accessible
- Immigration museums in destination countries often have arrival records
- FamilySearch Japanese collections include koseki registers

### African Ancestry
- The hardest genealogy in many countries due to slavery erasing records
- Church baptism records sometimes list enslaved people by first name + owner
- Post-emancipation: civil records with adopted surnames
- Estate inventories sometimes list enslaved people by name
- DNA testing can identify broad African regions of origin
- Oral tradition is especially important — document it carefully

### General Tips for Any Origin
- Learn what records exist for the specific region and time period
- Church records and civil records may contain different information
- Spelling of names was not standardized until recently — expect variations
- The language of records depends on who controlled the region (Latin for church, local language or imperial language for civil)

---

## Sensitivity & Privacy Rules

### At Project Start, Ask:
- "Are your parents alive?"
- "Are there divorces or remarriages I should be sensitive about?"
- "Is there anyone who wouldn't want their information in a family tree?"
- "Are there family conflicts or sensitive topics I should know about?"

### Rules for Living People:
- Never publish full birth dates without consent
- Be careful with addresses, phone numbers, email addresses
- Handle divorce/remarriage with discretion

### Rules for Multiple Families:
- If the user has children from different relationships, keep each branch STRICTLY separate
- Never cross-reference between ex-spouse's family and current spouse's family
- Ask the user explicitly about boundaries at the start

### Rules for Deceased People:
- Historical figures are generally fair game
- Recently deceased (within ~20 years): be sensitive about cause of death, financial details
- Illegitimate births, secret adoptions, affairs — let the user decide how to handle

---

## GEDCOM Integration

If the user has a GEDCOM file:
1. Import as starting point, but **treat every fact as `confidence: low`** until verified
2. Create YAMLs for the most important people first (direct line)
3. Cross-reference GEDCOM data against documents as you find them
4. Keep the GEDCOM as reference, but YAMLs are the source of truth going forward

To export: generate from YAMLs (only facts with `confidence: high` or `medium`).
