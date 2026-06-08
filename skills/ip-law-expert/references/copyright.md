# Copyright Law for Technology Companies

## What Copyright Protects in Software

Copyright in software is governed by **17 U.S.C. §§ 101–1332**. Software qualifies as a "literary work" under 17 U.S.C. § 101 and is automatically copyrighted upon creation (no registration required for protection to exist).

### What IS protected:
- Source code and object code (literal elements)
- Non-literal elements: structure, sequence, and organization of code where creative choices exist
- Comments, documentation, and creative variable naming
- UI design elements (visual appearance, not functionality)
- Compilation and arrangement of elements where creative selection exists

### What is NOT protected (17 U.S.C. § 102(b)):
- **Ideas, procedures, processes, systems, methods of operation** — regardless of the form in which described
- Functionality (patent protects this, not copyright)
- Interfaces and APIs that are purely functional (Google v. Oracle, 2021 — API copyrightability is disputed but fair use often applies)
- Algorithms (protectable only by patent, not copyright)
- Data, facts, and raw information
- Commonly used programming constructs (loops, conditionals, standard data structures)

### The Idea-Expression Dichotomy and Merger Doctrine
The **merger doctrine** applies when an idea can only be expressed in one or a very limited number of ways — in that case, the expression merges with the idea and cannot be copyrighted (otherwise copyright would effectively protect the idea itself). For standard software functions with only a few ways to implement them, copyright protection may be thin or absent.

### Scenes-à-Faire Doctrine
Elements that are standard, stock, or commonplace in a particular type of software (e.g., a login screen with username/password fields) are not protected. Only truly creative expression is protected.

## Copyright Registration: Critical Timing (17 U.S.C. § 412)

Copyright subsists automatically, but **registration is essential for meaningful enforcement**.

**Without registration, you cannot recover**:
- Statutory damages ($750–$30,000 per infringed work; up to $150,000 for willful infringement)
- Attorney's fees (often the most valuable remedy)

**The § 412 timing rule**:
- For published works: Must register BEFORE infringement begins, OR within 3 months of first publication, to be eligible for statutory damages and attorney's fees
- For unpublished works: Must register before infringement begins

**Practical advice for tech startups**:
1. Register source code with the Copyright Office at each major release (ASAP after release)
2. Registration fee: $45–$65 online per registration
3. For source code, you can register a deposit copy with portions redacted as trade secret (the Copyright Office accepts selective deposits)
4. Registration processing time: 3–6 months (can pay $800+ for expedited processing when litigation is imminent)

## Software Copyright Registration Mechanics

- Deposit requirement for software: Identify first and last 25 pages of source code, or all pages if fewer than 50 pages; trade secrets can be redacted
- Version updates: Each new version with more than minimal changes can be registered
- Unpublished works: Can register before public release
- "Best edition" rule: Submit source code, not compiled binary

## Copyright in Third-Party Components

All software products use third-party libraries. Failure to comply with their licenses is a copyright infringement risk.

**License compliance basics**:
- MIT, BSD, Apache: Must include copyright notice and license text in your distribution
- GPL/LGPL: Copyleft obligations — distributing GPL code in your product may require open-sourcing your code
- AGPL: Closes the "SaaS loophole" — even if you only run AGPL software as a service (no distribution), modifications must be made available
- Creative Commons: Cannot apply to software code (use for documentation, assets)

**Tools for compliance auditing**:
- FOSSA, Black Duck, WhiteSource/Mend — automated SBOM (Software Bill of Materials) generation and license scanning
- SPDX (Software Package Data Exchange) format for documenting dependencies

See references/open-source.md for full license strategy analysis.

## Work-for-Hire Doctrine

Under 17 U.S.C. § 101, work created by an employee within the scope of employment is automatically owned by the employer — the employer is deemed the "author." No assignment agreement is needed for employees.

**Contractors are different**: Work by independent contractors is NOT work-for-hire unless (1) the work falls into one of nine statutory categories, AND (2) there is a written agreement designating it as work-for-hire. Software development does not fall into the nine statutory categories for contractor work-for-hire. This means: **without a written IP assignment agreement, contractors own the copyright in code they write for you**.

Solution: All contractor agreements must include an explicit, present-tense IP assignment clause: "Contractor hereby irrevocably assigns to Company all right, title, and interest in and to all Work Product..." See references/ip-ownership.md.

## DMCA: Digital Millennium Copyright Act (17 U.S.C. § 512)

### Takedown Notices
Copyright holders can send DMCA takedown notices to Online Service Providers (OSPs) requiring removal of infringing content. The OSP must act expeditiously to remove content to maintain "safe harbor" protection.

Elements of a valid DMCA takedown notice:
1. Identification of the copyrighted work
2. Identification of the infringing material and its location
3. Statement of good faith belief that the use is unauthorized
4. Statement under penalty of perjury that the information is accurate
5. Contact information and signature of the copyright owner or authorized agent

### Safe Harbor (17 U.S.C. § 512)
OSPs are shielded from copyright liability for user-uploaded content IF they:
- Have no actual knowledge of infringement
- Act expeditiously to remove infringing content upon notification
- Have a registered DMCA agent with the Copyright Office
- Do not financially benefit from infringement they have the ability to control

**For AI startups**: If users upload and share content through your platform, register a DMCA agent and implement a takedown policy. Without this, you're exposed to direct infringement liability for user content.

### Counter-Notices
If your content is wrongly removed via DMCA, you can file a counter-notice. The OSP must restore the content within 10–14 business days unless the claimant files suit. Counter-notices include a consent to jurisdiction statement.

## Duration and Copyright Term

- Works created by employees/WFH: 95 years from publication or 120 years from creation, whichever expires first
- Works created by individual authors: Life of author + 70 years
- Public domain: Works published before 1928 are in the US public domain

## Key Copyright Cases for Software

- **Oracle v. Google** (2021): Google's use of Java APIs in Android was fair use; left copyrightability of APIs unresolved
- **Apple Computer v. Franklin Computer** (1983): Object code is copyrightable
- **Computer Associates v. Altai** (1992): Established "abstraction-filtration-comparison" test for non-literal software elements
- **Whelan v. Jaslow** (3d Cir. 1986): Structure, sequence and organization of program can be protected
