---
license: Provided under Anthropic's Terms of Service (not the Apache-2.0 LICENSE.txt used by most skills in this repo) — see NOTICE.md
source: https://github.com/anthropics/healthcare/tree/main/plugins/healthcare/skills/clinical-trial-protocol
name: clinical-trial-protocol-skill
description: Generate clinical trial protocols for medical devices or drugs. This skill should be used when users say "Create a clinical trial protocol", "Generate protocol for [device/drug]", "Help me design a clinical study", "Research similar trials for [intervention]", or when developing FDA submission documentation for investigational products.
---

# Clinical Trial Protocol Skill

## ⚠️ EXECUTION CONTROL - READ THIS FIRST

**CRITICAL: This orchestrator follows a SIMPLE START approach:**

1. **Display the welcome message FIRST** (shown in "Startup: Welcome and Confirmation" section below)
2. **Ask user to confirm they're ready to proceed** - Wait for confirmation (yes/no)
3. **Jump directly into Full Workflow Logic** - Automatically run subskills sequentially
4. **Do NOT pre-read subskill files** - Subskills are loaded on-demand only when their step executes

**Why this matters:**
- Pre-reading all subskills wastes context and memory
- Subskills should only load when actually needed during execution
- Workflow automatically handles resuming from existing waypoints

## Overview

This skill generates clinical trial protocols for **medical devices or drugs** using a **modular, waypoint-based architecture** 

## What This Skill Does

Starting with an intervention idea (device or drug), this orchestrated workflow offers two modes:

**🔬 Research Only Mode (Steps 0-1):**
0. **Initialize Intervention** - Collect device or drug information
1. **Research Similar Protocols** - Find similar trials, FDA guidance, and published protocols
   - **Deliverable:** Comprehensive research summary as formatted .md artifact

**📄 Full Protocol Mode (Steps 0-5):**
0. **Initialize Intervention** - Collect device or drug information
1. **Research Similar Protocols** - Find similar trials, FDA guidance, and published protocols
2. **Protocol Foundation** - Generate protocol sections 1-6 (foundation, design, population)
3. **Protocol Intervention** - Generate protocol sections 7-8 (intervention details)
4. **Protocol Operations** - Generate protocol sections 9-12 (assessments, statistics, operations)
5. **Generate Protocol** - Create professional file ready for stakeholder review

## Architecture

### Waypoint-Based Design

All analysis data is stored in `waypoints/` directory as JSON/markdown files:

```
waypoints/
├── intervention_metadata.json           # Intervention info, status, initial context
├── 01_clinical_research_summary.json   # Similar trials, FDA guidance, recommendations
├── 02_protocol_foundation.md            # Protocol sections 1-6 (Step 2)
├── 03_protocol_intervention.md          # Protocol sections 7-8 (Step 3)
├── 04_protocol_operations.md            # Protocol sections 9-12 (Step 4)
├── 02_protocol_draft.md                 # Complete protocol (concatenated in Step 4)
├── 02_protocol_metadata.json            # Protocol metadata
└── 02_sample_size_calculation.json      # Statistical sample size calculation
```

**Rich Initial Context Support:**
Users can provide substantial documentation, technical specifications, or research data when initializing the intervention (Step 0). This is preserved in `intervention_metadata.json` under the `initial_context` field. Later steps reference this context for more informed protocol development.

### Modular Subskill Steps

Each step is an independent skill in `references/` directory:

```
references/
├── 00-initialize-intervention.md    # Collect device or drug information
├── 01-research-protocols.md         # Clinical trials research and FDA guidance
├── 02-protocol-foundation.md        # Protocol sections 1-6 (foundation, design, population)
├── 03-protocol-intervention.md      # Protocol sections 7-8 (intervention details)
├── 04-protocol-operations.md        # Protocol sections 9-12 (assessments, statistics, operations)
└── 05-generate-document.md          # NIH Protocol generation
```

### Utility Scripts

```
scripts/
└── sample_size_calculator.py   # Statistical power analysis (validated)
```

## Prerequisites

### 1. clinical trials MCP Server (Required)

**Installation:**
- Install via drag-and-drop `.mcpb` file into Claude Desktop
- Or configure manually in Claude Desktop settings

**Available Tools:**
`search_clinical_trials` - Search by:

condition - Disease or condition (e.g., "pancreatic cancer")
intervention - Drug, device, or treatment (e.g., "pembrolizumab", "CAR-T")
sponsor - Sponsor or collaborator name (e.g., "Pfizer", "NIH")
location - City, state, or country (e.g., "California", "Boston")
status - "recruiting" (default), "active", "completed", "all"
phase - Trial phase: "1", "2", "3", "4", "early_phase1"
max_results - Default 25, max 100


`get_trial_details` - Get comprehensive details for a specific trial using its nct_id (e.g., "NCT04267848"). Returns eligibility criteria, outcomes, study design, and contact information.

**Verification:** Step 1 will automatically test MCP connectivity at startup.

### 2. FDA Database Access (Built-in)

**Purpose:** FDA regulatory pathway research via explicit database URLs

**Sources:**
- Step 1: FDA device/drug databases (510(k), PMA, De Novo, Drugs@FDA, Orange Book, Purple Book)
- All sources use direct FDA database URLs - no generic web searches

### 3. Clinical Protocol Template

**Template Files:** Any `.md` files in the `assets/` directory

**Purpose:** Reference template for protocol structure and content guidance. The system automatically detects available templates and uses them dynamically.

### 4. Python Dependencies (Required for Step 2)

**Installation:**
```bash
pip install -r requirements.txt
```

**Dependencies:**
- scipy >= 1.11.0 (statistical calculations)
- numpy >= 1.24.0 (numerical operations)

**Purpose:** Accurate statistical sample size calculations for clinical protocols

## How to Use

Simply invoke the skill and select your desired mode:

**🔬 Research Only Mode:**
1. Select "Research Only" from the main menu
2. Provide intervention information
3. Receive comprehensive research summary as formatted .md artifact
4. Option to continue with full protocol generation or exit

**📄 Full Protocol Mode:**
1. Select "Full Protocol" from the main menu
2. Guide you through all steps sequentially (Steps 0-5)
3. Pause after Step 4 to review the draft protocol
4. Generate the final protocol document when ready

**Resume Capability:** If interrupted, simply restart the skill and it will automatically resume from your last completed step.

## Execution Flow

### Startup: Welcome and Mode Selection

When skill is invoked, display the following message:

```
🧬 CLINICAL TRIAL PROTOCOL

Welcome! This skill generates clinical trial protocols for medical devices or drugs.

[If waypoints/intervention_metadata.json exists:]
✓ Found existing protocol in progress: [Intervention Name]
  Type: [Device/Drug]
  Completed: [List of completed steps]
  Next: [Next step to execute]

📋 SELECT MODE:

1. 🔬 Research Only - Run clinical research analysis (Steps 0-1)
   • Collect intervention information
   • Research similar clinical trials
   • Find FDA guidance and regulatory pathways
   • Generate comprehensive research summary as .md artifact

2. 📄 Full Protocol - Generate complete clinical trial protocol (Steps 0-5)
   • Everything in Research Only, plus:
   • Generate all protocol sections
   • Create professional protocol document

3. ❌ Exit

Please select an option (1, 2, or 3):
```

**🛑 STOP and WAIT for user selection (1, 2, or 3)**

- If **1 (Research Only)**: Set `execution_mode = "research_only"` and proceed to Research Only Workflow Logic
- If **2 (Full Protocol)**: Set `execution_mode = "full_protocol"` and proceed to Full Workflow Logic
- If **3 (Exit)**: Exit gracefully with "No problem! Restart the skill anytime to continue."

---

### Research Only Workflow Logic

**This workflow executes only Steps 0 and 1, then generates a formatted research summary artifact.**

**Step 1: Check for Existing Waypoints**
- If `waypoints/intervention_metadata.json` exists: Load metadata, check if steps 0 and 1 are already complete
- If no metadata exists: Start from Step 0

**Step 2: Execute Research Steps (0 and 1)**

For each step (0, 1):

1. **Check completion status:** If step already completed in metadata, skip with "✓ Step [X] already complete"

2. **Execute step:**
   - Display "▶ Executing Step [X]..."
   - Read and follow the corresponding subskill file instructions
   - Wait for completion
   - Display "✓ Step [X] complete"
   - **Step execution method (ON-DEMAND LOADING):** When a step is ready to execute (NOT before), read the subskill markdown file and execute ALL instructions within it
   - **Step-to-file mapping:**
     - Step 0: `references/00-initialize-intervention.md` (collect intervention info)
     - Step 1: `references/01-research-protocols.md` (clinical research and FDA guidance)

3. **Handle errors:** If step fails, ask user to retry or exit. Save current state for resume capability.

**Step 3: Generate Research Summary Artifact**

After Step 1 completes successfully:

1. **Read waypoint files:**
   - `waypoints/intervention_metadata.json` (intervention details)
   - `waypoints/01_clinical_research_summary.json` (research findings)

2. **Create formatted markdown summary:** Generate a comprehensive, well-formatted research summary as a markdown artifact with the following structure:

```markdown
# Clinical Research Summary: [Intervention Name]

## Intervention Overview
- **Type:** [Device/Drug]
- **Indication:** [Target condition/disease]
- **Description:** [Brief intervention description]
- **Mechanism of Action:** [How it works]

## Similar Clinical Trials
[List top 5-10 similar trials with NCT ID, title, phase, status, key findings]

## FDA Regulatory Pathway
- **Recommended Pathway:** [510(k), PMA, De Novo, IND, NDA, BLA, etc.]
- **Regulatory Basis:** [Rationale for pathway selection]
- **Key Requirements:** [Major regulatory considerations]

## FDA Guidance Documents
[List relevant FDA guidance documents with links and key excerpts]

## Study Design Recommendations
- **Suggested Study Type:** [RCT, single-arm, etc.]
- **Phase Recommendation:** [Phase 1, 2, 3, etc.]
- **Primary Endpoint Suggestions:** [Based on similar trials]
- **Sample Size Considerations:** [Preliminary thoughts]

## Key Insights and Recommendations
[Synthesized recommendations for protocol development]

## Next Steps
[If user wants to proceed with full protocol development]

---
*Generated by Clinical Trial Protocol Skill*
*Date: [Current date]*
```

3. **Save artifact:** Write the formatted summary to `waypoints/research_summary.md`

4. **Display completion message:**

```
✅ RESEARCH COMPLETE

Research Summary Generated: waypoints/research_summary.md

📊 Key Findings:
  • Similar Trials Found: [X trials]
  • Recommended Pathway: [Pathway name]
  • FDA Guidance Documents: [X documents identified]
  • Study Design: [Recommended design]

📄 The research summary has been saved as a formatted markdown artifact.

Would you like to:
1. Continue with full protocol generation (steps 2-5)
2. Exit and review research summary

```

**Option 1 Logic (Continue to Full Protocol):**
- Set `execution_mode = "full_protocol"`
- Continue to Full Workflow Logic starting from Step 2 (since 0 and 1 are complete)

**Option 2 Logic (Exit):**
- Display: "✓ Research summary saved. Restart the skill anytime to continue with protocol generation."
- Exit orchestrator gracefully

---

### Full Workflow Logic

**Step 1: Check for Existing Waypoints**
- If `waypoints/intervention_metadata.json` exists: Load metadata, check `completed_steps` array, resume from next incomplete step
- If no metadata exists: Start from Step 0

**Step 2: Execute Steps in Order**

For each step (0, 1, 2, 3, 4, 5):

1. **Check completion status:** If step already completed in metadata, skip with "✓ Step [X] already complete"

2. **Execute step:** Display "▶ Executing Step [X]...", read and follow the corresponding subskill file instructions, wait for completion, display "✓ Step [X] complete"
   - **Step execution method (ON-DEMAND LOADING):** When a step is ready to execute (NOT before), read the subskill markdown file and execute ALL instructions within it
   - **IMPORTANT:** Do NOT read subskill files in advance. Only read them at the moment of execution.
   - **Step-to-file mapping:**
     - Step 0: `references/00-initialize-intervention.md` (read when Step 0 executes)
     - Step 1: `references/01-research-protocols.md` (read when Step 1 executes)
     - Step 2: `references/02-protocol-foundation.md` (read when Step 2 executes - sections 1-6)
     - Step 3: `references/03-protocol-intervention.md` (read when Step 3 executes - sections 7-8)
     - Step 4: `references/04-protocol-operations.md` (read when Step 4 executes - sections 9-12)
     - Step 5: `references/05-concatenate-protocol.md` (read when Step 5 executes - final concatenation)

3. **Handle errors:** If step fails, ask user to retry or exit. Save current state for resume capability.

4. **Display progress:** "Progress: [X/6] steps complete", show estimated remaining time

5. **Step 4 Completion Pause:** After Step 4 completes, pause and display the Protocol Completion Menu (see below). Wait for user selection before proceeding.

**Step 2.5: Protocol Completion Menu**

After Step 4 completes successfully, display the EXACT menu below (do not improvise or create alternative options):

```
✅ PROTOCOL COMPLETE: Protocol Draft Generated

Protocol Details:
  • Study Design: [Design from metadata]
  • Sample Size: [N subjects from metadata]
  • Primary Endpoint: [Endpoint from metadata]
  • Study Duration: [Duration from metadata]

Protocol file: waypoints/02_protocol_draft.md
File size: [Size in KB]

📋 WHAT WOULD YOU LIKE TO DO NEXT?

1. 📄 Review Protocol in Artifact - click on the .md file above

2. 📄 Concatenate Final Protocol (Step 5)

3. ⏸️  Exit and Review Later

```

**Option 1 Logic (Review in Artifact):**
Pause, let user open the section files, wait for further instruction

**Option 2 Logic (Concatenate Protocol):**
1. Execute Step 5 by reading and following `references/05-concatenate-protocol.md`
2. Step 5 will concatenate all section files into final protocol document
3. Continue to Step 3 (Final Summary) after Step 5 completes

**Option 3 Logic (Exit):**
1. Display: "✓ Protocol sections saved. You can resume with Step 5 anytime to concatenate."
2. Exit orchestrator gracefully

**Step 3: Final Summary**

Display completion message with:
- Intervention name, type (device/drug), indication
- Protocol details (design, sample size, endpoints, duration)
- All completed steps list
- Final deliverable: Complete protocol markdown file location (waypoints/protocol_complete.md)
- Waypoint files list for reference
- Important disclaimers (FDA Pre-Sub, biostatistician review, IRB approval required)
- Thank you message

## Technical Details

### Waypoint File Formats

**JSON Waypoints** (Steps 0, 1):
- Structured data for programmatic access
- Small file sizes (1-15KB)
- Easy to parse and reference

**Markdown Waypoints** (Steps 2, 3, 4):
- Step 2: `02_protocol_foundation.md` (Sections 1-6)
- Step 3: `03_protocol_intervention.md` (Sections 7-8)
- Step 4: `04_protocol_operations.md` (Sections 9-12)
- Step 4: `02_protocol_draft.md` (concatenated complete protocol)
- Human-readable protocol documents
- Can be directly edited by users
- Individual section files preserved for easier regeneration

### Data Minimization Strategy

Each step implements aggressive summarization:
- **Keep:** Top-N results (5-10 max)
- **Keep:** Key facts and IDs (NCT numbers, endpoint types)
- **Keep:** Concise rationale (2-3 sentences)
- **Discard:** Raw MCP query results (not needed after analysis)
- **Discard:** Full FDA guidance text (only excerpts/citations kept)
- **Discard:** Lower-ranked search results

### Step Independence

Each subskill is designed to:
- Read only from waypoint files (not conversation history)
- Produce complete output in single execution
- Not depend on conversation context from previous steps
- Be runnable standalone

## Error Handling

### MCP Server Unavailable
- Detected in: Step 1
- Action: Display error with installation instructions
- Allow user to retry after installing MCP server
- No fallback available - MCP server is required for protocol research

### Step Fails or Returns Error
- Action: Display error message from subskill
- Ask user: "Retry step? (Yes/No)"
  - Yes: Re-run step
  - No: Save current state, exit orchestrator

### User Interruption
- All progress saved in waypoint files
- User can resume anytime by restarting the skill
- Workflow automatically detects completed steps and resumes from next step
- No data loss

## Disclaimers

⚠️ **IMPORTANT:** This protocol generation tool provides preliminary clinical study protocol based on NIH/FDA guidelines and similar trials. It does NOT constitute:
- Official FDA or IRB determination or approval
- Medical, legal, or regulatory advice
- Substitute for professional biostatistician review
- Substitute for FDA Pre-Submission meeting
- Guarantee of regulatory or clinical success

**REQUIRED before proceeding with clinical study:**
- Biostatistician review and sample size validation
- FDA Pre-Submission meeting (Q-Submission for devices, Pre-IND for drugs)
- IRB review and approval
- Clinical expert and regulatory consultant engagement
- Legal review of protocol and informed consent
- Site investigator review and input
- Sponsor completion of all [TBD] items in protocol

**PROFESSIONAL CONSULTATION STRONGLY RECOMMENDED**

Clinical trial protocols are complex, high-stakes documents requiring expertise across multiple disciplines. Professional consultation with clinical trial experts, biostatisticians, and regulatory affairs specialists is essential before proceeding with clinical study planning.


## Implementation Requirements

When this skill is invoked:

1. **Display the welcome message with mode selection** (shown in "Startup: Welcome and Mode Selection" section)

2. **Wait for user mode selection** (1: Research Only, 2: Full Protocol, 3: Exit)

3. **Execute based on selected mode:**
   - **Research Only Mode (Option 1):**
     - Execute Research Only Workflow Logic (Steps 0-1 only)
     - Generate formatted research summary as .md artifact
     - Offer option to continue with full protocol or exit
   - **Full Protocol Mode (Option 2):**
     - Execute Full Workflow Logic (Steps 0-5)
     - Check for existing waypoints and resume from last completed step
     - OR start from Step 0 if no waypoints exist
     - Execute all steps sequentially until complete

4. **For each step execution (LAZY LOADING - On-Demand Only):**
   - **ONLY when a step is ready to execute**, read the corresponding subskill file
   - Do NOT read subskill files in advance or "to prepare"
   - Example: When Step 1 needs to run, THEN read `references/01-research-protocols.md` and follow its instructions
   - **For protocol development:** Execute Steps 2, 3, 4 sequentially in order
   - Do NOT try to execute multiple steps in parallel - run sequentially
   - Read each step's subskill file only when that specific step is about to execute

5. **Research summary artifact generation (Research Only Mode):**
   - After Step 1 completes, read waypoint files
   - Generate comprehensive, well-formatted markdown summary
   - Save to `waypoints/research_summary.md`
   - Display completion message with key findings

6. **Handle errors gracefully:**
   - If a step fails, give user option to retry or exit
   - If MCP server unavailable, explain how to install
   - All progress is saved automatically in waypoints

7. **Track progress:**
   - Update `waypoints/intervention_metadata.json` after each step
   - Show progress indicators to user (e.g., "Progress: 3/6 steps complete" or "Progress: 2/2 research steps complete")
   - Provide clear feedback on what's happening

8. **Final output:**
   - **Research Only:** Display research summary location and offer to continue with full protocol
   - **Full Protocol:** Congratulate user, display protocol location and next steps
   - Remind user of disclaimers


