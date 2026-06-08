# IP Ownership: Employment, Contractors, and Founders

## IP Assignment Agreements (PIIA)

A **Proprietary Information and Inventions Agreement (PIIA)** — also called an Employee IP Agreement or Invention Assignment Agreement — is the foundational document for capturing all IP created by employees and contractors.

**Every employee and contractor must sign a PIIA before they start work or before any IP is created.** This is non-negotiable for any IP-driven company. Signing after-the-fact creates chain of title complications.

### Core Provisions of a Proper PIIA

**1. Assignment of Inventions**
Use present-tense language: "Employee hereby assigns and agrees to assign to Company all right, title, and interest in and to all Inventions..."

The critical distinction in patent law:
- "I agree to assign" = future promise (courts sometimes hold this creates only a contract claim, not automatic title transfer)
- "I hereby assign" = immediate present assignment (courts have held this automatically transfers title to future inventions when they come into existence — see *Stanford v. Roche*, 2011)

Draft PIIAs with "hereby assign" to effect automatic present assignment of future inventions.

**2. Definition of "Inventions"**
Should be broad: patents, copyrights, trade secrets, know-how, ideas, designs, software, data, models, processes, methods, formulae, whether or not protectable by law.

**3. Work-for-Hire Confirmation**
"All Inventions created within the scope of Employee's duties are works made for hire within the meaning of 17 U.S.C. § 101. To the extent any Inventions do not qualify as works made for hire, Employee hereby assigns all copyright..."

**4. Disclosure Obligation**
Employees must promptly disclose all inventions to the company (even those they believe may be excluded from assignment) so the company can evaluate assignment scope.

**5. Assistance with IP Prosecution**
Employees must assist in filing patent applications, executing assignments, and other IP protection steps during and after employment.

**6. Return of Property**
All company property (code, data, devices, credentials) must be returned upon termination.

**7. DTSA Whistleblower Immunity Notice**
Required by federal law in all contracts governing trade secret use. See references/trade-secrets.md.

## California Labor Code § 2870: Employees' Protected Inventions

California Labor Code § 2870 limits what employers can require employees to assign. An assignment provision is **void and unenforceable** to the extent it purports to assign an invention that:

**Must NOT be required to assign if ALL of the following apply**:
1. Developed entirely on the employee's own time
2. Without using employer's equipment, supplies, facilities, or trade secret information
3. Does not relate to the employer's business or actual/demonstrably anticipated R&D, AND
4. Does not result from any work performed by the employee for the employer

**California Labor Code § 2872**: Employers must provide written notification to employees at the time the PIIA is signed describing the § 2870 limits. Failure to provide notice may affect enforceability.

**Similar statutes in other states**: Washington (RCW 49.44.140), Minnesota, North Carolina, Delaware, Illinois — all have similar employee invention protection statutes with varying scope.

**Practical impact**: A Silicon Valley startup employee who invents a completely unrelated tool (e.g., a fitness app) entirely on personal time, without using any company resources, and where the invention has no relation to the company's business, owns that invention personally. The PIIA cannot override this.

**Important nuance**: "Relates to employer's business" is construed broadly. A startup building ML infrastructure — its employees' AI-related side projects likely "relate to" the employer's business even if not directly competitive.

## Contractor IP Ownership

**Default rule**: Independent contractors own the copyright in code they create. There is no automatic work-for-hire for contractor-developed software (software is not among the nine statutory work-for-hire categories under 17 U.S.C. § 101 for non-employees).

**Solution**: All contractor agreements must include:
1. An explicit IP assignment clause ("hereby assigns")
2. A confirmation that work constitutes work made for hire to the maximum extent possible under law, and to the extent it does not, contractor assigns all rights
3. A warranty that the contractor has the right to make the assignment (not bound by other agreements, not using others' IP)
4. DTSA whistleblower notice

**Common mistake**: Founders who had contractors build early versions of their product without IP assignments create chain of title defects that surface in due diligence. Remedy: Get executed IP assignments from all prior contractors ASAP. If a contractor is unavailable or refuses, document efforts and disclose to investors.

## Founder IP Assignment

All founders must assign their pre-company IP to the company at formation. Key situations:
- **Pre-incorporation work**: IP created before the company was formed (e.g., code built in a garage) must be assigned to the company at formation
- **Prior employer assignments**: Founders who built the core technology while at a prior employer may have assigned that IP to the prior employer under their PIIA. This is a chain of title risk. Review all prior employment agreements before founding a company using IP developed while employed elsewhere
- **University IP**: Technology developed at a university may be subject to the university's IP policy (often claims ownership of inventions using university resources). Many universities (Stanford, MIT, etc.) have technology transfer offices and may require a license from the university

**Restricted Stock and IP**: At incorporation, founder shares are typically subject to a vesting schedule (4 years, 1-year cliff). IP assignments from founders should NOT be conditioned on vesting — the company needs the IP immediately and fully regardless of whether the founder's stock has vested.

## Non-Compete Agreements

See references/trade-secrets.md for the full analysis. Key summary:
- FTC federal non-compete ban is dead (September 2025)
- California: non-competes void and unenforceable; SB 699 makes it illegal to even require signing one
- Most other states still enforce reasonably scoped non-competes
- Trade secret protection (DTSA) is the primary tool in ban states

## Non-Solicitation Agreements

Non-solicitation of employees (no-hire agreements) and non-solicitation of customers are separate from non-competes:

**Non-solicitation of employees**: Generally enforceable with reasonable scope and duration (1-2 years). Prohibits directly soliciting specific former colleagues, not hiring anyone who applies independently. California courts have narrowed enforcement — blanket prohibitions on contacting former colleagues may not survive.

**Non-solicitation of customers**: Prohibits contacting specific customers the employee worked with, not all customers. Must be tied to relationships the employee actually developed. Typically 1-2 year duration, limited to customers the employee had contact with.

## IP Audits Before Key Events

**Before a funding round**:
- Verify PIIA signed by all current and former employees and contractors
- Verify founder IP assignment documents
- Check for any IP created at prior employer that has been incorporated
- Review any open source dependencies for license compliance
- Verify copyright registrations for key software

**Before M&A**:
- Full IP chain of title review
- Prior employment agreement review for key founders/engineers
- Patent ownership verification (all assignments recorded at USPTO)
- Copyright registration and ownership documentation
- Trade secret identification and protection documentation
- Open source license compliance audit

**After acquiring a company**:
- Immediately get IP assignments from all employees/contractors who weren't covered
- Audit for open source compliance issues
- Verify that seller warranted chain of title and that reps & warranties insurance covers IP
