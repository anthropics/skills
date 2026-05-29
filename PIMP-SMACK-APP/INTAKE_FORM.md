# PIMP INTAKE FORM
## For Pro Se Litigants - Have Your AI Model Fill This Out

---

## INSTRUCTIONS FOR YOUR AI MODEL

```
You are helping a pro se litigant prepare legal documents. 
Fill out each section by asking the user questions.
Work BACKWARDS: Story first, then claims, then evidence.
Save everything to MASTER_SCHEMA.json format.
```

---

## STEP 1: WHO ARE YOU?

**Ask the user:**
- What is your full legal name?
- What is your mailing address?
- What is your email address?
- What is your phone number?

**Fill out:**
```json
{
  "name": "John Smith",
  "name_caps": "JOHN SMITH",
  "address_line_1": "123 Main Street",
  "city_state_zip": "Los Angeles, CA 90001",
  "email": "john@email.com",
  "phone": "(555) 123-4567",
  "pro_se": true
}
```

---

## STEP 2: WHAT CASE?

**Ask the user:**
- What is your case number? (Look at any court document)
- Which court is your case in?
- Who is the judge assigned?
- Are you the Plaintiff or Defendant? (Appellant or Appellee if appeals)

**Fill out:**
```json
{
  "case_number": "2:24-cv-01234-ABC",
  "court_name": "United States District Court, Central District of California",
  "court_type": "district",
  "jurisdiction": "ninth",
  "judge_name": "Hon. Jane Doe"
}
```

---

## STEP 3: TELL ME YOUR STORY

**Ask the user (in plain language):**

1. **What happened to you?**
   > Just tell me the story like you're telling a friend.

2. **Who did this to you?**
   > List every person or company that wronged you.

3. **When did it happen?**
   > Give me dates if you have them. "Around March 2024" is fine.

4. **Where did it happen?**
   > City, state, specific location if relevant.

5. **What did you lose?**
   > Money? Job? Freedom? Health? Reputation?

6. **What proof do you have?**
   > Emails? Documents? Witnesses? Photos? Recordings?

7. **What do you want the court to do?**
   > Money damages? Make them stop? Get your job back?

---

## STEP 4: BUILD THE TIMELINE

**From the story, extract events:**

| Date | What Happened | Who Did It | Evidence |
|------|---------------|------------|----------|
| 2024-01-15 | Terminated from job | ABC Corp | Termination letter |
| 2024-01-20 | Filed complaint with HR | HR Director | Email chain |
| ... | ... | ... | ... |

**Create event entries:**
```json
{
  "event_id": "E001",
  "date": "2024-01-15",
  "description": "Plaintiff was terminated from employment",
  "actors": ["ABC Corp", "Manager John Doe"],
  "evidence_uids": ["EV001"]
}
```

---

## STEP 5: IDENTIFY CLAIMS

**Based on the facts, suggest claims:**

"Based on your story, here are possible legal claims:"

| Claim | Why It Might Apply | Key Fact |
|-------|-------------------|----------|
| Title VII Discrimination | You were fired after complaining | Termination followed complaint |
| 42 USC 1983 | Government actor violated rights | Police used excessive force |
| Breach of Contract | They broke the agreement | Contract says X, they did Y |
| Fraud | They lied and you lost money | False statement, reliance, damages |

**Ask:** "Which of these sound right? Are there others?"

---

## STEP 6: MAP ELEMENTS TO FACTS

**For each claim, list the required elements:**

### Example: Title VII Retaliation
1. **Protected activity** - Did you complain about discrimination?
2. **Adverse action** - Were you fired, demoted, etc.?
3. **Causal connection** - Was the firing because of the complaint?

**Map your facts to elements:**

| Element | Your Fact | Evidence | UID |
|---------|-----------|----------|-----|
| Protected activity | Complained to HR on Jan 10 | Email to HR | 111 |
| Adverse action | Fired on Jan 15 | Termination letter | 121 |
| Causal connection | 5 days between complaint and firing | Timeline | 131 |

---

## STEP 7: ASSIGN UIDs

**UID Format: [Claim][Element][Defendant]**

- **Claim 1** = 100-199
- **Claim 2** = 200-299
- **Element 1** of Claim 1 = 110-119
- **Element 2** of Claim 1 = 120-129
- **Defendant 1** = ends in 1
- **Defendant 2** = ends in 2
- **All Defendants** = ends in 0

**Example:**
- UID 111 = Claim 1, Element 1, Defendant 1
- UID 120 = Claim 1, Element 2, All Defendants
- UID 231 = Claim 2, Element 3, Defendant 1

---

## STEP 8: LINK EVIDENCE

**For each piece of evidence:**

```json
{
  "evidence_id": "EV001",
  "type": "document",
  "description": "Termination letter dated Jan 15, 2024",
  "uids_satisfied": ["121", "122"],
  "quote": "Your employment is terminated effective immediately."
}
```

---

## STEP 9: FIND THE GAPS

**List elements without evidence:**

| Claim | Element | Missing Evidence | RFA Strategy |
|-------|---------|------------------|--------------|
| 1 | Causal connection | No direct statement | RFA: "Admit you fired Plaintiff within 5 days of complaint" |

**If they admit it → Element satisfied without trial**
**If they deny it → You know what to prove at trial**

---

## STEP 10: TRACK DEADLINES

**PIMP CLAP CARDS - Don't Get Caught Slipping**

| Deadline | Date | Rule | Consequence |
|----------|------|------|-------------|
| Answer to Complaint | 21 days | FRCP 12(a) | Default judgment |
| Initial Disclosures | 14 days after 26(f) | FRCP 26(a) | Sanctions |
| Discovery Cutoff | Per scheduling order | Local Rules | Evidence excluded |
| MSJ Deadline | Per scheduling order | FRCP 56 | Can't file MSJ |
| Response to RFA | 30 days | FRCP 36 | Deemed admitted |

---

## OUTPUT

Once complete, you have:
1. ✅ Party info for all documents
2. ✅ Case info for captions
3. ✅ Timeline of events
4. ✅ Claims with elements
5. ✅ Evidence linked by UID
6. ✅ Gaps identified for discovery
7. ✅ Deadlines tracked

**Send to PIMP for formatting.**

---

## FOR THE FORMATTING MODEL

When you receive a completed MASTER_SCHEMA.json:

1. Read `FILING_QUEUE.pending` to see what needs to be generated
2. For each filing:
   - Look up `filing_type` in `build_manifest.json`
   - Get `build_order` (what pieces to assemble)
   - Get `heading_order` (what sections in what order)
   - Pull data from MASTER_SCHEMA
   - Generate formatted document
3. Output to `output/` directory

**NO MANUAL EDITING - Everything programmatic.**
