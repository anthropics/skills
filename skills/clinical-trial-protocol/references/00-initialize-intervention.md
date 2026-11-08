# Clinical Trial Initialization Skill

## Purpose
This skill initializes a new clinical trial protocol by collecting information about the intervention (device or drug) and creating the metadata file that all subsequent steps will use.

## What This Skill Does
1. Collects essential intervention information from the user (device OR drug)
2. Creates a unique intervention identifier for file management
3. Writes the intervention metadata to a JSON waypoint file
4. Confirms readiness to begin protocol development

## Execution Flow

### Step 1: Determine Intervention Type

First, ask the user:
```
Is this a clinical trial protocol for:
1. Medical Device
2. Drug/Pharmaceutical

Please select (1 or 2):
```

### Step 2: Collect Intervention Information

Based on the intervention type, ask for the following information:

**For DEVICE interventions:**
1. **Device Name**: The official or working name of the medical device
2. **Device Description**: A brief technical description (2-3 sentences) of what the device is and how it works
3. **Intended Use**: The medical indication, condition, or procedure the device is intended for
4. **Target Population**: Who will use or benefit from this device (patients, specific age groups, disease stage)
5. **Special Considerations**: Any unique features, novel technology, or clinical concerns

**For DRUG interventions:**
1. **Drug Name**: The official or working name of the pharmaceutical/biologic
2. **Drug Description**: Mechanism of action, formulation, route of administration (2-3 sentences)
3. **Indication**: The medical condition or disease the drug is intended to treat
4. **Target Population**: Patient population (age, disease stage, prior treatments, etc.)
5. **Special Considerations**: Known safety concerns, prior clinical data, mechanism insights

**Handling Rich Initial Context:**
If the user provides substantial documentation, technical specifications, research data, or detailed information in their initial prompt, capture this as "initial_context" for use by later steps. This might include:
- Detailed technical specifications or investigator's brochure
- Research findings or preliminary data (preclinical, Phase 1/2 results)
- Competitive analysis or market research
- Technical architecture descriptions or chemistry data
- Engineering design documents or manufacturing process
- Clinical rationale or preliminary efficacy/safety evidence

This information will be preserved in the waypoint file to provide valuable context for protocol development.

### Step 2.5: Optional Custom Protocol Template

Ask the user if they want to provide a custom protocol template:

```
📋 Custom Protocol Template (Optional)

Do you have a custom protocol template you'd like to use for this project?

If you have a template file (.md format), you can:
- Drag and drop it into this chat now, OR
- Type 'skip' to use the default templates in the assets/ folder

Your choice (drag file or type 'skip'):
```

**If user provides a file:**
1. Note the file path/name in the conversation
2. Store reference in metadata (Step 4) as `user_provided_template` field
3. Confirm: "✓ Custom template received: [filename]. This will be used in protocol generation."

**If user types 'skip' or doesn't provide:**
1. Continue without custom template
2. Step 2 will use templates from the `assets/` directory

### Step 2.6: Optional Discovery Questions (ONLY if needed for clarity)

**IMPORTANT**: Only ask additional questions if the initial information is unclear, ambiguous, or missing critical details needed for protocol development. Do NOT ask these questions if the user has already provided clear, complete information.

**When to ask clarifying questions:**
- Intervention description is vague or missing technical details
- Intended use could apply to multiple different clinical scenarios
- Unclear what the primary clinical objective should be
- Ambiguous about patient population or disease stage
- Missing key information about how the intervention works

**Examples of good clarifying questions (maximum 3-5 questions):**

For a vague device like "AI heart monitor":
1. "Is this intended for continuous monitoring in a hospital setting, or for home/ambulatory use?"
2. "What specific cardiac conditions is it designed to detect (e.g., arrhythmias, heart failure, ischemia)?"
3. "Is this for initial diagnosis or for ongoing monitoring of known conditions?"

For a drug with unclear phase like "cancer immunotherapy":
1. "What phase trial are you planning? (Phase 1/2/3)"
2. "Is this first-in-human, or do you have prior safety data?"
3. "What is the target cancer type and line of therapy?"

For unclear comparator:
1. "What will this be compared against? (placebo, standard of care, active control)"
2. "Are there existing treatments that should be considered as comparators?"

**Guidelines for asking questions:**
- Ask ONLY if genuinely needed for protocol clarity
- Keep to maximum 3-5 focused questions
- Don't ask if the answer can be reasonably inferred
- Don't ask for information that will be gathered in later steps (like specific endpoints, sample sizes)
- Focus on clarifying the WHAT and HOW of the intervention, not detailed study design

### Step 3: Create Intervention Identifier

Generate a file-safe identifier from the intervention name:
- Convert to lowercase
- Replace spaces with hyphens
- Remove special characters
- Example: "Pembrolizumab" → "pembrolizumab"
- Example: "CardioSync Pacemaker" → "cardiosync-pacemaker"

### Step 4: Write Metadata File

Create `waypoints/intervention_metadata.json` with this structure:

```json
{
  "intervention_id": "generated-identifier",
  "intervention_type": "device" or "drug",
  "intervention_name": "User-provided name",
  "intervention_description": "User-provided description",
  "indication": "User-provided indication/intended use",
  "target_population": "User-provided target population",
  "special_considerations": "User-provided considerations (if any)",
  "initial_context": "Substantial documentation or detailed information provided in the initial prompt (if any). This preserves rich context for later phases.",
  "user_provided_template": {
    "provided": true or false,
    "file_path": "Full path to the user-provided template file (if provided)",
    "file_name": "Original filename (if provided)",
    "notes": "Any notes about the template source"
  },
  "discovery_clarifications": {
    "phase": "e.g., Phase 1, Phase 2, Phase 3 (for drugs)",
    "setting": "e.g., hospital, home, ambulatory",
    "mechanism": "e.g., checkpoint inhibitor, electrical stimulation, etc.",
    "comparator": "e.g., placebo, standard of care, active control",
    "additional_details": "Any other clarifications from Step 2.6"
  },
  "created_date": "YYYY-MM-DD",
  "protocol_status": "initialized",
  "completed_steps": []
}
```

**Note:**
- Only include `initial_context` if the user provided substantial documentation or detailed information beyond basic answers. If the user only provided brief answers to the core questions, omit this field or set it to an empty string.
- Set `user_provided_template.provided` to `false` and omit the `file_path` and `file_name` fields if user skipped template upload.
- Only include `discovery_clarifications` fields that were actually clarified through Step 2.6 questions. If no additional questions were asked, you can omit this section or leave it as an empty object `{}`.

### Step 5: Confirm Initialization

Display a confirmation message:

```
✓ Intervention metadata initialized: [Intervention Name]
✓ Intervention Type: [Device/Drug]
✓ Metadata saved to: waypoints/intervention_metadata.json

Ready to begin clinical protocol development.

Next Steps:
  1. Run Step 1: Research Similar Protocols
  2. Or run the full orchestrated workflow (main clinical-trial-protocol)

To proceed with protocol development, invoke the full orchestrator.
```

## Output Files

**Created:**
- `waypoints/intervention_metadata.json` (~1KB)

**Format:**
JSON file containing intervention metadata used by all subsequent steps

## Error Handling

If `waypoints/intervention_metadata.json` already exists:
1. Display the existing intervention information
2. Ask user: "Intervention metadata already exists. Do you want to: (a) Continue with existing intervention, (b) Create new intervention, (c) Update existing metadata?"
3. Handle accordingly


## Notes for Claude

- Be friendly and conversational when collecting information
- If user provides incomplete information, ask clarifying questions
- Ensure the intervention_id is filesystem-safe (no spaces, special chars)
- Validate that required fields are not empty
- Write clean, formatted JSON with proper indentation
- Handle both device and drug interventions appropriately with the right terminology