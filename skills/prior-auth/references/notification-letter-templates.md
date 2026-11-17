# Notification Letter Templates

This folder contains custom templates for prior authorization notification letters.

## How It Works

During Subskill 2 (Decision & Notification), the skill automatically searches this folder for custom letter templates:

- **Approval letters**: Files containing "approval" or "approve" in the name
- **Denial letters**: Files containing "denial" or "deny" in the name
- **Pend letters**: Files containing "pend" or "pending" in the name

If a matching template is found, it will be used to generate the notification letter.

## Creating Custom Templates

1. Create a new template file based on the placeholders below
2. Customize the letterhead, formatting, and content
3. Use the placeholders below (they will be automatically replaced)
4. Save with a descriptive name (e.g., `medicare_approval_letter.txt`)

## Available Placeholders

### Common to All Letters
- `[DATE]` - Current date (MM/DD/YYYY)
- `[PROVIDER_NAME]` - Provider name
- `[PROVIDER_NPI]` - Provider NPI number
- `[MEMBER_NAME]` - Member name
- `[MEMBER_ID]` - Member ID
- `[DOB]` - Date of birth (MM/DD/YYYY)
- `[SERVICE_DESCRIPTION]` - Description of requested service
- `[CPT_CODES]` - CPT/HCPCS procedure codes (comma-separated)
- `[ICD10_CODES]` - Diagnosis codes (comma-separated)
- `[POLICY_ID]` - Coverage policy identifier
- `[POLICY_TITLE]` - Coverage policy title

### Approval Letters Only
- `[AUTH_NUMBER]` - Generated authorization number (e.g., PA-20251207-47392)
- `[VALID_FROM]` - Authorization start date (MM/DD/YYYY)
- `[VALID_THROUGH]` - Authorization end date (MM/DD/YYYY)

### Denial Letters Only
- `[DENIAL_REASONS]` - Formatted list of specific denial reasons with explanations

### Pend Letters Only
- `[DOC_REQUESTS]` - Formatted list of required documentation
- `[RESPONSE_DEADLINE]` - Date by which information must be submitted (MM/DD/YYYY)

## Examples

### File Naming
✅ Good examples:
- `medicare_approval_letter.txt`
- `commercial_denial_template.txt`
- `medicaid_pend_notification.txt`
- `approval.txt`
- `deny_letter.txt`

❌ Won't be recognized:
- `notification.txt` (no decision type keyword)
- `template.txt` (no decision type keyword)

### Template Types Supported
- `.txt` - Plain text
- `.md` - Markdown
- Any other text-based format

## Tips

1. **Keep placeholders exact**: Use exact spelling and brackets (e.g., `[MEMBER_NAME]`)
2. **Test your templates**: Run a test PA request to verify formatting
3. **Include required elements**: Ensure regulatory disclosures are present (appeal rights for denials, etc.)
4. **Customize per payer type**: Create separate templates for Medicare, Commercial, Medicaid
5. **Update letterhead**: Replace placeholder letterhead with your organization's

## Fallback Behavior

If no custom template is found, the skill generates letters based on the decision type and available data.

## Sample Template Provided

See `Medicare_PA_Approval_Letter.pdf` in `prior-auth-review-skill/assets/` for a sample approval letter format.
