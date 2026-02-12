# 🖐️ THE PIMP HAND IS STRONG: BUILD INSTRUCTIONS
## Codename: "WHO'S MORE CORRUPT THAN CLACKAMAS COUNTY?"
### A Pro Se Legal Document Automation System

---

# EXECUTIVE SUMMARY (For The Impatient)

Build me a **React TypeScript (TSX)** web application that helps pro se litigants (people representing themselves in court) create properly formatted legal documents. The app collects their story, structures it into legal format, and outputs court-ready filings.

**Vibe:** Cyberpunk legal tech meets "the system is corrupt and we're gonna expose it."

**Target User:** Someone with no legal training who needs to file documents in federal court and NOT get their case dismissed because of formatting errors.

**The PIMP Hand Philosophy:** We work BACKWARDS. Story first, legal structure second. The user tells us what happened, and we turn it into a weapon of legal destruction.

---

# PART 1: APPLICATION ARCHITECTURE

## 1.1 Tech Stack

```
Framework:       React 18+ with TypeScript (TSX)
Styling:         TailwindCSS + custom cyberpunk theme
UI Components:   shadcn/ui (modern, accessible)
Icons:           Lucide React
State:           React Context or Zustand
Forms:           React Hook Form + Zod validation
File Output:     docx library for Word documents
Storage:         localStorage (for now) / IndexedDB later
```

## 1.2 Application Structure

```
pimp-legal-app/
├── src/
│   ├── app/
│   │   ├── layout.tsx              # Root layout with navigation
│   │   ├── page.tsx                # Landing page
│   │   ├── intake/                 # Story intake wizard
│   │   │   ├── page.tsx
│   │   │   └── components/
│   │   ├── claims/                 # Claim builder
│   │   │   ├── page.tsx
│   │   │   └── components/
│   │   ├── evidence/               # Evidence manager
│   │   │   ├── page.tsx
│   │   │   └── components/
│   │   ├── documents/              # Document generator
│   │   │   ├── page.tsx
│   │   │   └── components/
│   │   ├── timeline/               # Visual timeline
│   │   │   └── page.tsx
│   │   └── pimp-cards/             # Deadline tracker
│   │       └── page.tsx
│   ├── components/
│   │   ├── ui/                     # shadcn components
│   │   ├── layout/
│   │   │   ├── Navbar.tsx
│   │   │   ├── Sidebar.tsx
│   │   │   └── Footer.tsx
│   │   ├── forms/
│   │   │   ├── StoryIntakeForm.tsx
│   │   │   ├── PartyInfoForm.tsx
│   │   │   ├── CaseInfoForm.tsx
│   │   │   └── EvidenceUploadForm.tsx
│   │   └── displays/
│   │       ├── TimelineView.tsx
│   │       ├── ClaimCard.tsx
│   │       ├── EvidenceCard.tsx
│   │       └── DocumentPreview.tsx
│   ├── lib/
│   │   ├── schema/
│   │   │   ├── masterSchema.ts     # TypeScript types matching JSON schema
│   │   │   ├── filingTypes.ts      # Filing type definitions
│   │   │   └── headingDefinitions.ts
│   │   ├── generators/
│   │   │   ├── documentGenerator.ts
│   │   │   ├── captionGenerator.ts
│   │   │   └── certificateGenerator.ts
│   │   ├── utils/
│   │   │   ├── uidSystem.ts        # The legendary 3-digit UID system
│   │   │   ├── dateHelpers.ts
│   │   │   └── validation.ts
│   │   └── data/
│   │       ├── courts.json
│   │       ├── claims.json         # Common claim templates
│   │       └── elements.json       # Elements for each claim type
│   ├── hooks/
│   │   ├── useCaseData.ts
│   │   ├── useDocumentGenerator.ts
│   │   └── useDeadlineTracker.ts
│   ├── context/
│   │   └── CaseContext.tsx         # Global case state
│   └── styles/
│       └── cyberpunk.css           # Custom theme overrides
├── public/
│   └── assets/
└── package.json
```

---

# PART 2: CORE FEATURES & COMPONENTS

## 2.1 LANDING PAGE - "The Pimp Hand Welcomes You"

**Purpose:** Explain what this is, who it's for, get them started.

**Elements:**
- Hero section with tagline: "The System is Corrupt. Let's Fight Back. Properly Formatted."
- Three value props:
  1. "Tell Your Story" - We listen, we structure
  2. "Build Your Case" - Claims, elements, evidence linked
  3. "Generate Documents" - Court-ready, no formatting errors
- Big CTA button: "START YOUR CASE" → goes to /intake
- Smaller link: "I already have a document" → paste TOC flow

**Visual Style:**
- Dark background (#0a0a0a)
- Neon accents (cyan #00ffff, magenta #ff00ff)
- Glitch text effects on headers
- Circuit board patterns in background

---

## 2.2 INTAKE WIZARD - "Tell Me Everything"

**Purpose:** Collect the user's story in plain language.

**Flow:** 6 steps, progress bar at top

### Step 1: Who Are You?
```tsx
<PartyInfoForm>
  - Full legal name
  - Mailing address (line 1, line 2, city, state, zip)
  - Email address
  - Phone number
  - "Are you the Plaintiff or Defendant?"
</PartyInfoForm>
```

### Step 2: What Court?
```tsx
<CaseInfoForm>
  - Case number (with format hint: "2:24-cv-01234-ABC")
  - Court selector (dropdown with federal courts)
  - Judge name (optional, can look up later)
  - "Is this an appeal?" → if yes, show lower court fields
</CaseInfoForm>
```

### Step 3: Who Did This To You?
```tsx
<DefendantsForm>
  - Add defendant button (repeatable)
  - For each:
    - Name
    - Role (individual, company, government entity)
    - What they did (brief)
  - Auto-assigns defendant numbers (1, 2, 3...)
</DefendantsForm>
```

### Step 4: What Happened?
```tsx
<StoryIntakeForm>
  - Large textarea: "Tell me your story like you're telling a friend"
  - Prompt helpers:
    - "What happened?"
    - "When did it happen?"
    - "Where did it happen?"
    - "What did you lose?"
  - AI assist button: "Help me organize this" (future: Gemini integration)
</StoryIntakeForm>
```

### Step 5: What Proof Do You Have?
```tsx
<EvidenceOverviewForm>
  - Checklist of evidence types:
    [ ] Emails
    [ ] Documents/contracts
    [ ] Photos/videos
    [ ] Witness statements
    [ ] Official records
    [ ] Other
  - Text field: "Describe your evidence briefly"
</EvidenceOverviewForm>
```

### Step 6: What Do You Want?
```tsx
<ReliefForm>
  - Checkboxes:
    [ ] Money damages - amount field
    [ ] Injunction (make them stop)
    [ ] Declaratory relief (court says you're right)
    [ ] Attorney fees and costs
    [ ] Other - text field
</ReliefForm>
```

**End of Wizard:** "CASE CREATED" → redirect to Dashboard

---

## 2.3 DASHBOARD - "Your War Room"

**Purpose:** Central hub showing case status and next steps.

**Layout:**
```
┌─────────────────────────────────────────────────────────────┐
│  CASE: 2:24-cv-01234    STATUS: Building Claims             │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐    │
│  │ CLAIMS   │  │ EVIDENCE │  │ TIMELINE │  │ GENERATE │    │
│  │    3     │  │    7     │  │  12 evts │  │   DOCS   │    │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘    │
│                                                             │
│  UPCOMING DEADLINES (PIMP CLAP CARDS)                       │
│  ┌─────────────────────────────────────────────────────┐    │
│  │ ⚠️ Answer due in 14 days (FRCP 12(a))               │    │
│  │ 📋 Initial disclosures in 28 days (FRCP 26(a))     │    │
│  └─────────────────────────────────────────────────────┘    │
│                                                             │
│  RECENT ACTIVITY                                            │
│  • Added Claim: 42 USC 1983 - Deprivation of Rights        │
│  • Uploaded evidence: Termination Letter                    │
│  • Generated: Notice of Appeal draft                        │
└─────────────────────────────────────────────────────────────┘
```

---

## 2.4 CLAIMS BUILDER - "Pick Your Weapons"

**Purpose:** Select claims that fit the facts, map elements.

**Layout:**

**Left Panel:** Claim Selector
```tsx
<ClaimSelector>
  - Search bar
  - Categories:
    - Civil Rights (42 USC 1983, Title VII, ADA)
    - Contract (Breach, Fraud, etc.)
    - Tort (Negligence, Defamation)
    - Employment
    - Constitutional
  - Each claim shows:
    - Name
    - Statute
    - Number of elements
    - "ADD" button
</ClaimSelector>
```

**Right Panel:** Active Claims with Elements
```tsx
<ClaimCard claim={claim}>
  - Claim title + statute
  - Elements list (checkboxes):
    [ ] Element 1: Description
    [ ] Element 2: Description
  - For each element:
    - Status indicator (✓ satisfied, ⚠️ needs evidence, ✗ missing)
    - "Link Evidence" button
    - UID display (e.g., "UID: 111")
  - "Map to Defendant" dropdown
</ClaimCard>
```

**UID System Visual:**
```
┌─────────────────────────────────────┐
│ UID: 1 2 3                          │
│      │ │ └─ Defendant 3             │
│      │ └─── Element 2               │
│      └───── Claim 1                 │
└─────────────────────────────────────┘
```

---

## 2.5 EVIDENCE MANAGER - "Load Your Ammo"

**Purpose:** Upload, tag, and link evidence to claims/elements.

**Features:**

```tsx
<EvidenceUploader>
  - Drag & drop zone
  - File picker button
  - Supported: PDF, images, text
</EvidenceUploader>

<EvidenceList>
  - Grid or list view toggle
  - For each evidence item:
    <EvidenceCard>
      - Thumbnail/icon
      - File name
      - Description (editable)
      - Date (from file or entered)
      - "Assigned UIDs" badges
      - "Key Quote" field
      - "Assign to Element" button
    </EvidenceCard>
</EvidenceList>

<EvidenceLinkModal>
  - Shows all claims/elements
  - Checkbox to link this evidence
  - Up to 3 UIDs per evidence item
  - "This evidence proves..." text field
</EvidenceLinkModal>
```

---

## 2.6 TIMELINE VIEW - "See The Corruption Unfold"

**Purpose:** Visual chronological display of events.

**Layout:**
```tsx
<TimelineView>
  - Vertical timeline, scrollable
  - Each event:
    <TimelineEvent>
      - Date (large, bold)
      - Description
      - Actors involved (defendant badges)
      - Evidence links (clickable)
      - UID badges
    </TimelineEvent>
  - "Add Event" button
  - Filter by defendant
  - Filter by claim
</TimelineView>
```

**Visual Style:**
- Dark background
- Cyan timeline line
- Event nodes that glow on hover
- Magenta highlights for defendant actions

---

## 2.7 DOCUMENT GENERATOR - "Fire The Cannon"

**Purpose:** Select document type, preview, generate.

**Layout:**

**Step 1: Select Document Type**
```tsx
<DocumentTypeSelector>
  - Cards for each type:
    - Motion (various subtypes)
    - Brief / Opposition
    - Declaration
    - Notice
    - Complaint
    - Discovery (RFAs, Interrogatories, RFPs)
  - Click to select
</DocumentTypeSelector>
```

**Step 2: Configure**
```tsx
<DocumentConfigForm>
  - Document title (with suggestions)
  - Court (pre-filled from case)
  - Sections to include (checkboxes, based on filing type)
  - "Include Declaration?" toggle
  - "Include Proposed Order?" toggle
</DocumentConfigForm>
```

**Step 3: Fill Content**
```tsx
<SectionEditor>
  - For each required section (from heading_order):
    <SectionBlock>
      - Heading (from heading1_definitions)
      - Rich text editor for content
      - "Why this matters" tooltip (legal_reason)
      - "AI Assist" button (future)
    </SectionBlock>
</SectionEditor>
```

**Step 4: Preview & Generate**
```tsx
<DocumentPreview>
  - Live preview (styled like actual document)
  - Word count display
  - Validation warnings:
    - "Missing required section: Jurisdictional Statement"
    - "Word count exceeds limit: 14,523 / 14,000"
  - "GENERATE DOCX" button
  - "GENERATE PDF" button (if available)
</DocumentPreview>
```

---

## 2.8 PIMP CLAP CARDS - "Don't Get Caught Slipping"

**Purpose:** Deadline tracker with consequences.

**Layout:**
```tsx
<DeadlineTracker>
  <DeadlineCard deadline={deadline}>
    - Title: "Answer to Complaint"
    - Due date (countdown)
    - Rule citation: "FRCP 12(a)"
    - Consequence: "DEFAULT JUDGMENT"
    - Status: Not Started / In Progress / Complete
    - Mark Complete button
  </DeadlineCard>
  
  - Add custom deadline button
  - Calendar view toggle
  - Export to calendar (.ics)
</DeadlineTracker>
```

**Visual:**
- Color coding:
  - Green: 30+ days
  - Yellow: 7-30 days
  - Orange: 1-7 days  
  - Red/pulsing: OVERDUE

---

# PART 3: DATA SCHEMA (TypeScript Types)

```typescript
// src/lib/schema/masterSchema.ts

interface PartyInfo {
  name: string;
  nameCaps: string;
  addressLine1: string;
  addressLine2?: string;
  cityStateZip: string;
  email: string;
  phone: string;
  role: 'Plaintiff' | 'Defendant' | 'Appellant' | 'Appellee';
  proSe: boolean;
}

interface CaseInfo {
  caseNumber: string;
  courtName: string;
  courtType: 'district' | 'appeals' | 'state' | 'bankruptcy';
  jurisdiction: string;
  judgeName?: string;
  lowerCourtCase?: string;
  lowerCourtName?: string;
  filingDate?: string;
}

interface Defendant {
  id: number;  // 1-9, used in UID
  name: string;
  role: string;
  description: string;
}

interface ClaimElement {
  elementNumber: number;  // 1-9, used in UID
  name: string;
  description: string;
  satisfied: boolean;
  evidenceIds: string[];
}

interface Claim {
  claimNumber: number;  // 1-9, used in UID
  name: string;
  statute: string;
  elements: ClaimElement[];
  defendantIds: number[];
}

interface Evidence {
  id: string;
  type: 'document' | 'email' | 'photo' | 'video' | 'testimony' | 'admission';
  description: string;
  date?: string;
  filePath?: string;
  uidsSatisfied: string[];  // e.g., ["111", "121", "231"]
  keyQuote?: string;
}

interface TimelineEvent {
  id: string;
  date: string;
  description: string;
  actors: string[];
  evidenceIds: string[];
  claimUids: string[];
}

interface Deadline {
  id: string;
  name: string;
  dueDate: string;
  rule: string;
  consequence: string;
  status: 'not_started' | 'in_progress' | 'complete';
}

interface CaseData {
  partyInfo: PartyInfo;
  caseInfo: CaseInfo;
  defendants: Defendant[];
  claims: Claim[];
  evidence: Evidence[];
  timeline: TimelineEvent[];
  deadlines: Deadline[];
  story: {
    whatHappened: string;
    whatYouLost: string;
    whatYouWant: string;
  };
}
```

---

# PART 4: KEY UTILITY FUNCTIONS

```typescript
// src/lib/utils/uidSystem.ts

/**
 * Generate UID from claim, element, defendant
 * Format: [Claim 1-9][Element 1-9][Defendant 0-9]
 * Defendant 0 = all defendants
 */
export function generateUID(
  claimNumber: number, 
  elementNumber: number, 
  defendantNumber: number
): string {
  return `${claimNumber}${elementNumber}${defendantNumber}`;
}

/**
 * Parse UID back to components
 */
export function parseUID(uid: string): {
  claim: number;
  element: number;
  defendant: number;
} {
  return {
    claim: parseInt(uid[0]),
    element: parseInt(uid[1]),
    defendant: parseInt(uid[2])
  };
}

/**
 * Get all UIDs for a claim
 */
export function getClaimUIDs(claimNumber: number): string[] {
  const uids: string[] = [];
  for (let e = 1; e <= 9; e++) {
    for (let d = 0; d <= 9; d++) {
      uids.push(generateUID(claimNumber, e, d));
    }
  }
  return uids;
}
```

---

# PART 5: STYLING REQUIREMENTS

## Cyberpunk Theme

```css
/* src/styles/cyberpunk.css */

:root {
  --bg-primary: #0a0a0a;
  --bg-secondary: #1a1a2e;
  --bg-card: #16213e;
  --text-primary: #e0e0e0;
  --text-secondary: #a0a0a0;
  --accent-cyan: #00ffff;
  --accent-magenta: #ff00ff;
  --accent-yellow: #ffff00;
  --danger: #ff3333;
  --success: #00ff88;
  --warning: #ffaa00;
}

/* Glitch text effect for headers */
.glitch-text {
  text-shadow: 
    2px 2px var(--accent-magenta),
    -2px -2px var(--accent-cyan);
  animation: glitch 2s infinite;
}

/* Neon glow on focus */
input:focus, button:focus {
  box-shadow: 0 0 10px var(--accent-cyan);
  border-color: var(--accent-cyan);
}

/* Pulsing deadline warning */
.deadline-urgent {
  animation: pulse 1s infinite;
  border-color: var(--danger);
}
```

---

# PART 6: INTEGRATION POINTS

## 6.1 Local Storage (MVP)

```typescript
// Save case data
localStorage.setItem('pimp_case_data', JSON.stringify(caseData));

// Load case data
const saved = localStorage.getItem('pimp_case_data');
if (saved) {
  setCaseData(JSON.parse(saved));
}
```

## 6.2 Document Generation

Use `docx` npm package:
```typescript
import { Document, Packer, Paragraph, TextRun } from 'docx';

async function generateDocument(caseData: CaseData, filingType: string) {
  const doc = new Document({
    sections: [{
      properties: {
        page: {
          margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 }
        }
      },
      children: [
        // Generate content based on filing type
      ]
    }]
  });
  
  const blob = await Packer.toBlob(doc);
  // Trigger download
}
```

## 6.3 Future: Gemini Integration

```typescript
// Placeholder for AI assist
async function aiAssist(prompt: string, context: string): Promise<string> {
  // Call Gemini API
  // Return structured suggestion
}
```

---

# PART 7: COMPONENT CHECKLIST

## Must Have (MVP)
- [ ] Landing page with CTA
- [ ] Intake wizard (6 steps)
- [ ] Dashboard with case overview
- [ ] Claims builder with element mapping
- [ ] Evidence manager (basic)
- [ ] Document type selector
- [ ] Section editor (basic)
- [ ] Document preview
- [ ] DOCX export
- [ ] Deadline tracker

## Nice to Have (V2)
- [ ] Timeline visualization
- [ ] AI-assisted content suggestions
- [ ] PDF export
- [ ] Calendar integration
- [ ] Multi-case support
- [ ] Cloud sync

---

# FINAL NOTES

## The Philosophy

1. **User First:** They don't know legal formatting. We do.
2. **Work Backwards:** Story → Structure, not Structure → Story.
3. **No Gotchas:** Warn about deadlines, required sections, word limits.
4. **The Pimp Hand is Strong:** Proper formatting = power over the system.

## The Name

Feel free to name it:
- "PIMP Legal" (Pro Se Intelligent Motion Processor)
- "Who's More Corrupt Than Clackamas County?"
- "The Pimp Hand"
- "Legal Cannon"
- Whatever makes you laugh while fighting corruption.

## The Goal

A pro se litigant should be able to:
1. Tell their story
2. Get help picking claims
3. Link their evidence
4. Generate a properly formatted document
5. Not get their case dismissed because of a font error

**LET'S BUILD THIS THING.**

---

*Built with righteous anger and a strong pimp hand.*
*A-Team Productions*
