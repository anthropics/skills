# Examples for TOGAF ADM Visualization Scripts

This directory contains example JSON files to help you quickly test the visualization scripts.

## Two Diagram Formats Available

### ArchiMate (PlantUML) - **Recommended for Professional Work**
- Industry-standard EA modeling language
- Compatible with enterprise EA tools (Archi, Sparx EA)
- Precise relationship types and standardized notation
- Renders to PNG/SVG/PDF
- Scripts ending in `_archimate.py`

### Mermaid - Legacy/Quick Prototyping
- Quick visualization in markdown
- Auto-renders in GitHub, Notion, etc.
- Good for rapid iteration and informal docs
- Original scripts without `_archimate` suffix

## Available Examples

### 1. Value Chain Examples

**ArchiMate Version (`value_chain_example.json`):**
```bash
cd togaf-adm
python3 scripts/generate_value_chain_archimate.py examples/value_chain_example.json
plantuml value_chain_archimate.puml  # Renders to PNG
```

**Mermaid Version (same JSON):**
```bash
python3 scripts/generate_value_chain.py examples/value_chain_example.json
```

Example for a Fintech Lending Platform showing:
- Support activities: Infrastructure, HR, Technology, Procurement
- Primary activities: Lead Acquisition → Scoring → Underwriting → Disbursement → Servicing

**ArchiMate Output:** PlantUML diagram using Value_Stream and Business_Function elements
**Mermaid Output:** Simple flow diagram

---

### 2. Value Stream Examples

**ArchiMate Version (`value_stream_example.json` or `apple_value_stream_archimate.json`):**
```bash
cd togaf-adm
python3 scripts/generate_value_stream_archimate.py examples/value_stream_example.json
plantuml value_stream_archimate.puml  # Renders to PNG
```

**Mermaid Version (same JSON):**
```bash
python3 scripts/generate_value_stream.py examples/value_stream_example.json
```

Example for "Credit Origination" value stream showing:
- Trigger: Customer applies for credit online
- 4-5 stages with business processes
- Actors and application components per stage
- Metrics: lead time, cycle time, automation rate

**ArchiMate Output:** PlantUML using Value_Stream, Business_Process, Business_Actor, Application_Component
**Mermaid Output:** Swimlane-style flow diagram

**Apple Example:** `apple_value_stream_archimate.json` shows iPhone Product Launch value stream

---

### 3. Capability Map Examples

**ArchiMate Version (`capability_map_example.json`):**
```bash
cd togaf-adm
python3 scripts/generate_capability_map_archimate.py examples/capability_map_example.json
plantuml capability_map_archimate.puml  # Renders to PNG
```

**Mermaid Version (same JSON):**
```bash
python3 scripts/generate_capability_map.py examples/capability_map_example.json
```

Example for Fintech Lending Platform showing:
- 4 domains: Customer Management, Credit Management, Risk Management, Technology
- Multiple capabilities per domain with maturity levels (current vs target)
- Sub-capabilities for detailed breakdown
- Criticality levels: LOW, MEDIUM, HIGH, CRITICAL

**ArchiMate Output:** PlantUML using Capability elements with color-coded maturity gaps + summary table
**Mermaid Output:** Hierarchical diagram with heat map

---

---

## Interactive Mode

All scripts support interactive mode (without JSON input):

**ArchiMate versions:**
```bash
# Value Chain - interactive ArchiMate
python3 scripts/generate_value_chain_archimate.py

# Value Stream - interactive ArchiMate
python3 scripts/generate_value_stream_archimate.py

# Capability Map - interactive ArchiMate
python3 scripts/generate_capability_map_archimate.py
```

**Mermaid versions:**
```bash
# Value Chain - interactive Mermaid
python3 scripts/generate_value_chain.py

# Value Stream - interactive Mermaid
python3 scripts/generate_value_stream.py

# Capability Map - interactive Mermaid
python3 scripts/generate_capability_map.py
```

The scripts will prompt you for all necessary information.

---

## Rendering PlantUML Diagrams

**Option 1: Install PlantUML locally**
```bash
# Mac
brew install plantuml

# Then render
plantuml diagram.puml
# Creates diagram.png
```

**Option 2: Use online**
1. Go to https://www.plantuml.com/plantuml/uml/
2. Paste the .puml file contents
3. Get PNG/SVG output

**Option 3: VS Code Extension**
- Install "PlantUML" extension
- Open .puml file
- Press Alt+D to preview

---

## Customization

Feel free to modify these JSON files to match your organization's specific context:

1. Copy an example file
2. Edit the JSON to reflect your organization
3. Run the script with your custom JSON
4. Use the generated Mermaid diagram in your architecture documentation

---

## Maturity Levels Reference

Used in Capability Map:
- **Level 0:** Doesn't exist
- **Level 1:** Ad-hoc, manual, dependent on individuals
- **Level 2:** Repeatable but manual
- **Level 3:** Defined, documented, standardized
- **Level 4:** Managed with metrics
- **Level 5:** Optimized, automated, continuous improvement

---

## ArchiMate Benefits

**Why use ArchiMate instead of Mermaid?**

1. **Standardization:** Industry-recognized notation from The Open Group
2. **Interoperability:** Import/export with professional EA tools (Archi, Sparx EA, BiZZdesign)
3. **Precision:** Specific relationship types (Assignment, Serving, Realization, etc.) vs generic arrows
4. **Layered architecture:** Clear separation of Business, Application, Technology concerns
5. **Professional output:** Suitable for stakeholder presentations and formal documentation
6. **TOGAF alignment:** Same organization (The Open Group) maintains both TOGAF and ArchiMate

**When to use Mermaid:**
- Quick prototyping and iteration
- Informal documentation
- Markdown-based wikis (GitHub, Notion)
- When stakeholders prefer simpler diagrams

---

## Heat Map Colors

Used in Capability Map diagrams (both Mermaid and ArchiMate):
- 🟢 **Green (#C8E6C9):** No gap (on target)
- 🟡 **Yellow (#FFF9C4):** Small gap (1 level)
- 🟠 **Orange (#FFE0B2):** Medium gap (2 levels)
- 🔴 **Red (#FFCDD2):** Critical gap (3+ levels or high criticality with any gap)
