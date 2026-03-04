# Stap-voor-stap: Pull Request indienen op anthropics/skills

## Wat je nodig hebt
- Een GitHub account (je zei dat je er al op zit)
- Een browser
- De bestanden uit de map: skills/document-typography/

## Stappen

### 1. Fork de repository
- Ga naar: https://github.com/anthropics/skills
- Klik rechtsboven op de knop **"Fork"**
- Laat alle opties standaard en klik **"Create fork"**
- Je hebt nu een kopie op: https://github.com/JOUW-USERNAME/skills

### 2. Navigeer naar de skills map
- In jouw fork, klik op de map **"skills"**
- Je ziet daar nu mappen als docx, pdf, pptx, etc.

### 3. Maak de nieuwe skill-map aan
- Klik op **"Add file"** → **"Create new file"**
- Type als bestandsnaam: **document-typography/SKILL.md**
  (door de "/" maakt GitHub automatisch de map aan)
- Plak de inhoud van het SKILL.md bestand
- Klik **"Commit changes"** (groen knop onderaan)

### 4. Upload de scripts
- Navigeer naar de nieuw aangemaakte map:
  skills/document-typography/
- Klik op **"Add file"** → **"Create new file"**
- Type: **scripts/measure_m_count.py**
- Plak de inhoud
- Commit

- Herhaal voor:
  - **scripts/check_orphans.py**
  - **scripts/check_layout.sh**
  - **scripts/measure_line_width.py**

### 5. Open de Pull Request
- Ga naar jouw fork: https://github.com/JOUW-USERNAME/skills
- GitHub toont bovenaan een banner:
  "This branch is X commits ahead of anthropics:main"
  met een knop **"Contribute"** → **"Open pull request"**
- Klik daarop

### 6. Vul de PR in
- **Title**: Add document-typography skill: typographic quality control for generated documents
- **Description**: Plak de inhoud uit PR_DESCRIPTION.md
  (het deel onder "## Description")
- Klik **"Create pull request"**

### 7. Klaar!
Nu wacht je op review van het Anthropic team. Ze kunnen vragen stellen
of wijzigingen voorstellen. Je krijgt een notificatie op GitHub.

## Tips
- Het Anthropic team heeft 167 open PRs, dus het kan even duren
- Als ze wijzigingen vragen, kun je die direct in de browser doen
  (klik op het bestand → potlood-icoon → edit)
- Wees niet bang om te reageren op comments, het is een vriendelijke community
