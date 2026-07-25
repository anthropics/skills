# Declaration Boundary

## No fabrication

The skill must not fabricate:

- Funding statements
- Conflict of interest declarations
- Data availability statements
- Ethics statements
- Suggested reviewers
- CRediT author contributions

## Placeholder rule

If a declaration field is empty in the manifest, `declarations.md` leaves
a `[LIVE-VERIFICATION: ...]` placeholder. The user must fill and verify
the statement before submission.

## Source of truth

Declaration requirements come from the journal-templates yaml
(`declaration_requirements` block), which mirrors the journal-formats
fact sheet. If the two disagree, the fact sheet wins; report the mismatch
as a warning.
