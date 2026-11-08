1. [Description]
This skill is a legal document formatter designed for pro se litigants. It uses a taxonomy-based system to format ANY legal document (motions, complaints, briefs) according to specific jurisdiction rules. It does NOT write legal content; it applies structure and formatting.

2. [requirements]
- Access to `PimpJuice_instructions/` directory.
- `taxonomy/filing_types.json` (for document types).
- `taxonomy/build_manifest.json` (for build order).
- `jurisdictions/courts.json` (for court-specific rules).

3. [Cautions]
- This is a FORMATTER, not a drafter. Do not use it to generate legal arguments or advice.
- Ensure the correct filing type is selected from the taxonomy.
- Verify the jurisdiction rules in `courts.json` match the target court.

4. [Definitions]
- **Taxonomy**: The classification system for legal documents.
- **Build Manifest**: The sequence of sections required for a specific document type.
- **Pro Se**: Representing oneself in court without an attorney.

5. [log]
(No run logs available yet. This section will be populated by the system upon successful execution.)

6. [model_readme]
Workflow:
1. **Identify Need**: User requests formatting for a specific document (e.g., "Summary Judgment Motion").
2. **Lookup**: Find the filing type in `taxonomy/filing_types.json`.
3. **Get Order**: Retrieve the `construct_order` from `taxonomy/build_manifest.json`.
4. **Apply Rules**: Use `jurisdictions/courts.json` to apply font, margin, and styling rules.
5. **Format**: Structure the user's content according to the manifest and rules.
