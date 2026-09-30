# Legal Document Drafting Map (Pro Se Formatter Suite)

WE.[READ FIRST]
- Read `.readme` in this folder first.

This file is a shared **map/cheat sheet** for the formatter suite.

It is intentionally **framework-first**:
- It defines what each document type *is*, what sections it usually contains, and where it sits in the workflow.
- It uses cited sources for local rules, certificates, and jurisdiction requirements.
- Jurisdiction-specific rules come from **source-backed extraction** (local rules, FRAP/FRCP, standing orders).

It also supports two operational modes (choose one per run):
- **Evidence-backed mode**: the tool receives structured timeline/events/inputs (more verifiable).
- **User-asserted mode**: the tool proceeds on user assertions (must list assumptions + unknowns).

---

## A. System Sections (Drafting Software = building blocks)

These are the major “sections/modules” your drafting system is already expressing across skills:

1. **Template Merge (DOCX placeholder fill)**
   - Deterministic rendering from a user-supplied template with `{{TOKENS}}`.
   - Owned by: `universal-motion-brief`.

2. **XML-first DOCX Builder (OOXML generation / overlays)**
   - Deterministic document generation via WordprocessingML + zip packaging.
   - Owned by: `declaration-builder`.

3. **Cover / Caption Generation**
   - Generates cover pages/captions from a fixed template.
   - Owned by: `ninth-circuit-cover`.

4. **Brief Assembly (FRAP 28 ordering + TOC/TOA + validation)**
   - Section order, markers, validation, word counts.
   - Owned by: `ninth-circuit-opening-brief` and `ninth-circuit-brief-body`.

5. **Jurisdiction Overlay / Rule Injection (planned + incremental)**
   - Adds jurisdiction-specific deltas (certificates, word limits, formatting rules).
   - Must be built from **cited sources**.

6. **Evidence Integration (existing system, preserve exactly)**
   - Evidence IDs / naming / UID system is external and must remain stable.
  - Preserve the evidence UID system exactly as provided by the external system.

---

## B. Document Type Classification (what each thing *is*)

This section is a classification index. Fill the placeholders with citations and jurisdiction-specific deltas.

### 1) Declaration (supporting evidence document)
- **Role**: sworn factual statement supporting another filing (motion, opposition, complaint, etc.).
- **Inputs**:
  - declarant identity
  - fact blocks (your 2+2+1 structure)
  - execution date/location
- **Outputs**:
  - declaration body
  - signature block
  - optional exhibits references (use provided exhibit references)
- **Rule sources (placeholders)**:
  - `[DECLARATION_RULE_SOURCES]` (e.g., FRCP/FRAP + local rules)
- **Certificates possibly required (placeholders)**:
  - `[DECLARATION_CERTS_REQUIRED]`

### 2) Motion
- **Role**: request for an order (relief) from the court.
- **Core sections (typical)**:
  - title + relief requested
  - introduction/summary
  - procedural posture
  - legal standard
  - argument
  - conclusion/prayer
  - proposed order (if required)
- **Rule sources (placeholders)**:
  - `[MOTION_RULE_SOURCES]`
- **Certificates (placeholders)**:
  - `[MOTION_CERTS_REQUIRED]`

### 3) Sanctions (motion / request category)
- **Role**: request that the court impose sanctions for misconduct.
- **Special constraints**:
  - notice requirements / safe-harbor (jurisdiction and rule dependent)
- **Rule sources (placeholders)**:
  - `[SANCTIONS_RULE_SOURCES]`

### 4) Complaint
- **Role**: initiates civil action; states claims and requested relief.
- **Rule sources (placeholders)**:
  - `[COMPLAINT_RULE_SOURCES]`

### 5) Appellate Brief (Opening Brief)
- **Role**: merits brief; must comply with FRAP 28 + circuit rules.
- **Owned section order**: see `ninth-circuit-opening-brief`.
- **Rule sources (placeholders)**:
  - `[BRIEF_RULE_SOURCES]`
- **Certificates**:
  - certificate of compliance
  - certificate of service

---

## B2. Filing Types vs Heading1 Groups (two-dict model)

To reduce confusion, keep these concepts simple:

1. **Filing Types** = “what document are we building?” (motion, opposition, complaint, judgment, etc.)
   - Each filing type includes its own default `headings_h1` list.
2. **Rules Workspace** = “what does THIS jurisdiction require?” (word counts, conferral, certificates, formatting)
   - Populated only from cited sources.

Working data files:
- Baseline (framework-only):
  - [../../pro-se-formatter-taxonomy/pro-se-formatter-taxonomy_instructions/filing_types_federal_baseline.json](../../pro-se-formatter-taxonomy/pro-se-formatter-taxonomy_instructions/filing_types_federal_baseline.json)
- Mutable workspace (source-backed extraction target):
  - [../../pro-se-formatter-taxonomy/pro-se-formatter-taxonomy_instructions/rules_workspace_federal_template.json](../../pro-se-formatter-taxonomy/pro-se-formatter-taxonomy_instructions/rules_workspace_federal_template.json)

Optional reference (legacy glossary/back-compat):
- [../../pro-se-formatter-taxonomy/pro-se-formatter-taxonomy_instructions/heading1_groups_baseline.json](../../pro-se-formatter-taxonomy/pro-se-formatter-taxonomy_instructions/heading1_groups_baseline.json)

## C. Dependency / Build Order Matrix (inside-out)

Use this matrix to know “what’s missing” and what to build next.

| Step | Build Block | Required Inputs | Produces | Used By | Notes |
|---:|---|---|---|---|---|
| 1 | Fact blocks (2+2+1) | narrative, parties, time/place, link | `[DECLARATION_FACT_BLOCKS]` | Declaration | Must remain deterministic |
| 2 | Declaration wrapper | declarant, facts, signature info | `[DECLARATION_DOC]` | Motion/Opp/Complaint support | |
| 3 | Cover/caption | case number, parties, filing name, judge | `[COVER_CAPTION_BLOCK]` | Brief/Motion/Declaration (when needed) | Ninth-circuit has separate generator |
| 4 | Certificates | jurisdiction key + sources | `[CERTIFICATE_BLOCKS]` | Brief/Motion/etc. | Build from cited sources |
| 5 | Assembly | section JSON + template | final `.docx` | Brief/Motion | Deterministic merge |

---

## D. Jurisdiction & Rules Capture (source-backed)

When jurisdiction is known:
1. Identify controlling regime (federal/district/circuit + case type).
2. Collect sources:
   - local rules URLs/PDFs
   - standing orders
   - FRAP/FRCP/FRBP etc.
3. Extract ONLY what you can quote/cite into:
   - `[LOCAL_RULE_SOURCES]`
   - `[CERTIFICATIONS_REQUIRED]`
   - `[WORD_LIMITS]`
   - `[FORMATTING_DELTAS]`

Output format suggestion (for future automation): `rules/{jurisdiction_key}.json` with source URLs + extracted requirements.
