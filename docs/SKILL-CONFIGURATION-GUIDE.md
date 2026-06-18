# Skills Configuratie Handleiding

Deze handleiding beschrijft hoe je skills configureert en integreert in Claude. Je leert over project skills, user preferences, en de verschillende integratiemethoden.

---

## Inhoudsopgave

1. [Overzicht van Skills](#overzicht-van-skills)
2. [Project Skills vs User Preferences](#project-skills-vs-user-preferences)
3. [Skills Installeren in Claude Code](#skills-installeren-in-claude-code)
4. [Skills Configureren in Claude.ai](#skills-configureren-in-claudeai)
5. [Skills via de API](#skills-via-de-api)
6. [Eigen Skills Maken](#eigen-skills-maken)
7. [Best Practices](#best-practices)

---

## Overzicht van Skills

Skills zijn mappen met instructies, scripts en resources die Claude dynamisch laadt om gespecialiseerde taken beter uit te voeren. Ze leren Claude hoe specifieke taken op een herhaalbare manier te voltooien.

### Structuur van een Skill

```
mijn-skill/
├── SKILL.md           # Vereist: Instructies en metadata
├── scripts/           # Optioneel: Uitvoerbare code
├── references/        # Optioneel: Referentiedocumentatie
├── assets/            # Optioneel: Templates, fonts, etc.
└── LICENSE.txt        # Optioneel: Licentie-informatie
```

### Minimale SKILL.md

```markdown
---
name: mijn-skill-naam
description: Een duidelijke beschrijving van wat deze skill doet en wanneer te gebruiken
---

# Mijn Skill Naam

[Instructies die Claude volgt wanneer deze skill actief is]
```

---

## Project Skills vs User Preferences

### Project Skills

Project skills zijn skills die **specifiek voor een project** worden geconfigureerd. Ze zijn zichtbaar voor iedereen die aan het project werkt.

**Wanneer gebruiken:**
- Team-specifieke workflows
- Project-specifieke stijlgidsen
- Gedeelde coding conventies
- Brand guidelines voor het project

**Locatie:** In de projectmap, bijvoorbeeld `.claude/skills/`

**Voorbeeld projectstructuur:**
```
mijn-project/
├── .claude/
│   └── skills/
│       ├── project-coding-style/
│       │   └── SKILL.md
│       └── team-workflow/
│           └── SKILL.md
├── src/
└── package.json
```

### User Preferences (Persoonlijke Skills)

User preference skills zijn **persoonlijke skills** die alleen voor jou gelden, ongeacht welk project je gebruikt.

**Wanneer gebruiken:**
- Persoonlijke schrijfstijl
- Favoriete coding conventies
- Persoonlijke workflows
- Taalvoorkeuren (bijv. Nederlands)

**Locatie:** In je home directory, bijvoorbeeld `~/.claude/skills/`

**Voorbeeld structuur:**
```
~/.claude/
└── skills/
    ├── mijn-schrijfstijl/
    │   └── SKILL.md
    └── nederlands-communicatie/
        └── SKILL.md
```

### Prioriteit

Wanneer beide types skills bestaan:
1. **Project skills** hebben prioriteit voor project-specifieke taken
2. **User preferences** worden gebruikt voor algemene voorkeuren
3. Bij conflicten wordt de meest specifieke skill gebruikt

---

## Skills Installeren in Claude Code

### Methode 1: Via Plugin Marketplace

```bash
# Voeg de Anthropic skills marketplace toe
/plugin marketplace add anthropics/skills

# Installeer specifieke skill sets
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
```

### Methode 2: Directe Installatie van Repository

```bash
# Voeg een skills repository toe als marketplace
/plugin marketplace add WouterArtsRecruitin/skills

# Bekijk beschikbare plugins
/plugin list

# Installeer gewenste skills
/plugin install <skill-naam>
```

### Methode 3: Lokale Skills

1. Maak een `.claude/skills/` map in je project
2. Voeg skill-mappen toe met `SKILL.md` bestanden
3. Claude detecteert deze automatisch

**Voorbeeld:**
```bash
mkdir -p .claude/skills/mijn-skill
cat > .claude/skills/mijn-skill/SKILL.md << 'EOF'
---
name: mijn-skill
description: Beschrijving van mijn skill
---

# Instructies
...
EOF
```

### Skills Gebruiken in Claude Code

Na installatie kun je skills activeren door ze te noemen:

```
"Gebruik de PDF skill om de formuliervelden uit document.pdf te extraheren"

"Pas de brand-guidelines skill toe op dit document"

"Maak een presentatie met de pptx skill"
```

---

## Skills Configureren in Claude.ai

### Stap 1: Toegang tot Settings

1. Ga naar Claude.ai
2. Klik op je profielicoon
3. Selecteer "Settings"
4. Navigeer naar "Skills" of "Capabilities"

### Stap 2: Skills Uploaden

**Voor Project Skills:**
1. Open een project in Claude
2. Ga naar Project Settings
3. Upload je skill-map of SKILL.md bestand
4. De skill is nu beschikbaar voor dat project

**Voor User Preferences:**
1. Ga naar Account Settings
2. Navigeer naar "My Skills" of "Preferences"
3. Upload je persoonlijke skills
4. Deze zijn nu beschikbaar in alle projecten

### Stap 3: Skills Beheren

- **Activeren/Deactiveren:** Toggle skills aan/uit per project
- **Prioriteit instellen:** Bepaal welke skills voorrang krijgen
- **Verwijderen:** Verwijder skills die je niet meer nodig hebt

---

## Skills via de API

### Skill Toevoegen aan API Request

```python
import anthropic

client = anthropic.Anthropic()

# Skill content laden
with open("mijn-skill/SKILL.md", "r") as f:
    skill_content = f.read()

response = client.messages.create(
    model="claude-sonnet-4-20250514",
    max_tokens=1024,
    system=f"""
    Je hebt de volgende skill beschikbaar:

    {skill_content}

    Gebruik deze skill wanneer relevant.
    """,
    messages=[
        {"role": "user", "content": "Jouw vraag hier"}
    ]
)
```

### Meerdere Skills Combineren

```python
skills = []
skill_paths = ["skills/pdf/SKILL.md", "skills/docx/SKILL.md"]

for path in skill_paths:
    with open(path, "r") as f:
        skills.append(f.read())

combined_skills = "\n\n---\n\n".join(skills)

response = client.messages.create(
    model="claude-sonnet-4-20250514",
    max_tokens=1024,
    system=f"Beschikbare skills:\n\n{combined_skills}",
    messages=[...]
)
```

---

## Eigen Skills Maken

### Stap 1: Bepaal het Doel

Beantwoord deze vragen:
- Welk probleem lost deze skill op?
- Wanneer moet Claude deze skill gebruiken?
- Welke specifieke instructies zijn nodig?

### Stap 2: Maak de Basisstructuur

```bash
mkdir mijn-nieuwe-skill
touch mijn-nieuwe-skill/SKILL.md
```

### Stap 3: Schrijf SKILL.md

```markdown
---
name: mijn-nieuwe-skill
description: |
  Gebruik deze skill wanneer de gebruiker [specifieke taak] wil uitvoeren.
  Trigger woorden: [keyword1], [keyword2], [keyword3]
---

# Mijn Nieuwe Skill

## Doel
[Beschrijf wat deze skill doet]

## Instructies
1. [Stap 1]
2. [Stap 2]
3. [Stap 3]

## Voorbeelden

### Voorbeeld 1: [Scenario]
[Input en verwachte output]

### Voorbeeld 2: [Scenario]
[Input en verwachte output]

## Richtlijnen
- [Richtlijn 1]
- [Richtlijn 2]
- [Richtlijn 3]

## Beperkingen
- [Wat deze skill NIET doet]
```

### Stap 4: Voeg Optionele Resources Toe

**Scripts** (voor deterministische taken):
```bash
mkdir mijn-nieuwe-skill/scripts
# Voeg Python/Bash scripts toe
```

**References** (voor gedetailleerde documentatie):
```bash
mkdir mijn-nieuwe-skill/references
# Voeg .md bestanden toe met diepgaande info
```

**Assets** (voor templates en resources):
```bash
mkdir mijn-nieuwe-skill/assets
# Voeg templates, fonts, etc. toe
```

### Stap 5: Test de Skill

1. Installeer lokaal in Claude Code
2. Test met verschillende prompts
3. Verfijn instructies gebaseerd op resultaten

---

## Best Practices

### 1. Houd het Beknopt

Claude is al slim. Focus op:
- Specifieke procedures
- Uitzonderingen op standaardgedrag
- Domain-specifieke kennis

**Vermijd:**
- Algemene instructies die Claude al kent
- Overbodige uitleg
- Te veel context

### 2. Duidelijke Triggers

Gebruik beschrijvende `description` velden:

```yaml
# Goed
description: |
  Gebruik deze skill voor het maken van PowerPoint presentaties.
  Trigger woorden: presentatie, slides, pptx, deck, slideshow

# Minder goed
description: Een skill voor documenten
```

### 3. Structureer voor Schaalbaarheid

```
skill/
├── SKILL.md              # Essentieel, compact
├── references/           # Details on-demand
│   ├── advanced.md
│   └── troubleshooting.md
└── scripts/              # Betrouwbare uitvoering
    └── helper.py
```

### 4. Versie Beheer

- Gebruik Git voor skill development
- Tag releases voor stabiliteit
- Documenteer wijzigingen in CHANGELOG

### 5. Test Grondig

- Test met edge cases
- Valideer output kwaliteit
- Controleer op conflicten met andere skills

---

## Veelgestelde Vragen

### Hoeveel skills kan ik tegelijk gebruiken?

Er is geen harde limiet, maar houd rekening met:
- Context window grootte
- Mogelijke conflicten tussen skills
- Performance impact

### Kan ik skills delen met mijn team?

Ja, op verschillende manieren:
- Via Git repository (zoals deze)
- Als Project skills in gedeelde projecten
- Via de Claude.ai interface

### Werken skills offline?

Skills zelf werken offline, maar:
- Claude Code vereist een internetverbinding
- Sommige skill-scripts kunnen externe dependencies hebben

### Hoe debug ik een skill die niet werkt?

1. Controleer de `name` en `description` in frontmatter
2. Vraag Claude expliciet de skill te gebruiken
3. Vereenvoudig de instructies
4. Check op syntax fouten in YAML frontmatter

---

## Handige Links

- [Agent Skills Specificatie](https://agentskills.io/specification)
- [What are skills?](https://support.claude.com/en/articles/12512176-what-are-skills)
- [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [Creating custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide)

---

## Bijdragen

Wil je bijdragen aan deze skills repository?

1. Fork de repository
2. Maak een nieuwe branch
3. Voeg je skill toe of verbeter bestaande
4. Maak een Pull Request

Voor vragen of suggesties, open een issue op GitHub.
