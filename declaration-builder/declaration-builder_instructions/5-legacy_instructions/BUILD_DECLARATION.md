# Building Declarations

## Overview

Declarations are built using the 2+2+1 structure for EACH fact:
- **2 Circumstance Statements** - Set the scene
- **2 Element Descriptions** - What happened
- **1+ Party-Link Statement** - Connect to opposing party

## Structure Template

```xml
<FACT num="[N]" title="[ELEMENT_TITLE]">
  <CIRCUMSTANCE type="time_place">
    On [DATE], at approximately [TIME], I was present at [LOCATION].
  </CIRCUMSTANCE>
  <CIRCUMSTANCE type="parties_roles">
    At said time and location, [PARTIES] were present in their official capacities.
  </CIRCUMSTANCE>
  <ELEMENT type="primary">
    [Primary description of what happened - specific and factual]
  </ELEMENT>
  <ELEMENT type="supporting">
    [Supporting detail that corroborates the primary description]
  </ELEMENT>
  <PARTY_LINK defendant="[DEFENDANT_NAME]">
    [How this defendant caused/participated in this event]
  </PARTY_LINK>
  <WITNESSES>
    [List of witnesses who observed this, if any]
  </WITNESSES>
  <EVIDENCE uids="[UID1,UID2,...]">
    [References to evidence cards supporting this fact]
  </EVIDENCE>
</FACT>
```

## Extraction Rules

When analyzing a user's narrative, extract:

### Constitutional Violations
- Rights denied or violated
- Due process failures
- Fourth Amendment (search/seizure)
- First Amendment (speech/petition)
- Fourteenth Amendment (equal protection)

### Fraud Indicators
- Misrepresentations to the court
- Concealment of material facts
- False statements under oath
- Document falsification

### Procedural Errors
- Missed deadlines by opposing party
- Improper service
- Rule violations
- Failure to disclose

### Evidence Issues
- Spoliation (destruction of evidence)
- Tampering
- Chain of custody breaks
- Delayed production

## Building the Declaration Document

### Step 1: Create Header Block

```xml
<w:p>
  <w:pPr>
    <w:jc w:val="center"/>
    <w:rPr>
      <w:rFonts w:ascii="Century Schoolbook" w:hAnsi="Century Schoolbook"/>
      <w:b/><w:caps/>
      <w:sz w:val="28"/>
    </w:rPr>
  </w:pPr>
  <w:r>
    <w:rPr><w:b/><w:caps/><w:sz w:val="28"/></w:rPr>
    <w:t>DECLARATION OF [DECLARANT]</w:t>
  </w:r>
</w:p>
```

### Step 2: Create Preamble

```xml
<w:p>
  <w:pPr>
    <w:spacing w:line="480" w:lineRule="auto"/>
    <w:ind w:firstLine="720"/>
  </w:pPr>
  <w:r>
    <w:t>I, [DECLARANT], declare under penalty of perjury under the laws of [JURISDICTION] that the following is true and correct:</w:t>
  </w:r>
</w:p>
```

### Step 3: Insert Facts (Loop)

For each extracted fact, generate the 2+2+1 structure block.

### Step 4: Create Signature Block

```xml
<w:p>
  <w:pPr>
    <w:spacing w:before="480" w:line="480" w:lineRule="auto"/>
    <w:ind w:firstLine="720"/>
  </w:pPr>
  <w:r>
    <w:t>I declare under penalty of perjury that the foregoing is true and correct.</w:t>
  </w:r>
</w:p>
<w:p>
  <w:pPr>
    <w:spacing w:before="240" w:line="480" w:lineRule="auto"/>
    <w:ind w:firstLine="720"/>
  </w:pPr>
  <w:r>
    <w:t>Executed on [EXECUTION_DATE] at [EXECUTION_LOCATION].</w:t>
  </w:r>
</w:p>
<w:p>
  <w:pPr><w:spacing w:before="720"/></w:pPr>
  <w:r><w:t>_______________________________</w:t></w:r>
</w:p>
<w:p>
  <w:r><w:t>[DECLARANT]</w:t></w:r>
</w:p>
```

### Step 5: Wrap with Cover Page

Insert `[PLACEHOLDER_COVER]` at document start. This resolves to the jurisdiction-specific cover XML.

## Example: Tyler's Declaration on Defendants' False Statements

**User Input:**
> The defendants stated not once but twice the same set of half truths - 
> in the Motion to Dismiss AND the Reply (filed late). They claimed my whole 
> day didn't exist. This is fraud upon the court to end the case based on lies 
> and procedural manipulation.

**Extracted Facts:**

**FACT 1: FALSE STATEMENTS IN MOTION TO DISMISS**
- CIRCUMSTANCE 1: On [DATE], Defendants filed a Motion to Dismiss in Case No. 25-6461 in the Ninth Circuit Court of Appeals.
- CIRCUMSTANCE 2: Said Motion was prepared and filed by Defendants' counsel acting in their official capacity as legal representatives of Clackamas County.
- ELEMENT 1: Defendants' Motion to Dismiss contained material misrepresentations of fact, specifically denying events that Declarant can establish occurred.
- ELEMENT 2: These misrepresentations were made with knowledge of their falsity, as Defendants possessed evidence contradicting their statements.
- PARTY LINK: Clackamas County, through its counsel, deliberately submitted false statements to this Court with the intent to obtain dismissal through fraud.

**FACT 2: REPEATED FALSE STATEMENTS IN REPLY BRIEF**
- CIRCUMSTANCE 1: On [DATE], Defendants filed a Reply Brief in Case No. 25-6461, which was filed after the deadline and should be struck.
- CIRCUMSTANCE 2: Said Reply repeated the same material misrepresentations previously made in the Motion to Dismiss.
- ELEMENT 1: Defendants' Reply Brief contained identical false statements to those in their Motion to Dismiss, demonstrating a pattern of deliberate deception.
- ELEMENT 2: The repetition of these false statements indicates willful fraud upon the court rather than inadvertent error.
- PARTY LINK: Clackamas County continued its course of fraudulent conduct by doubling down on false statements, compounding the fraud upon this Court.

**FACT 3: FRAUD UPON THE COURT**
- CIRCUMSTANCE 1: Throughout the proceedings in Case No. 25-6461, Defendants have engaged in a pattern of misrepresentation.
- CIRCUMSTANCE 2: These misrepresentations were made in formal court filings under the signature of counsel.
- ELEMENT 1: The cumulative effect of Defendants' false statements constitutes fraud upon the court under applicable precedent.
- ELEMENT 2: Defendants' intent to deceive is evidenced by procedural manipulation, including late filings and repeated false claims.
- PARTY LINK: Clackamas County seeks to terminate this case not on its merits but through systematic deception and procedural abuse.

## Peer Review Prompt for GPT-5.2

After building the declaration, send to GPT-5.2 with this prompt:

```
Review this declaration for:
1. Completeness - Are all elements properly structured (2+2+1)?
2. Specificity - Are facts specific enough to be actionable?
3. Linkage - Does each fact properly connect to the defendant?
4. Legal sufficiency - Would this survive a motion to strike?
5. Consistency - Are there any internal contradictions?

Return structured feedback with suggested improvements.
```
