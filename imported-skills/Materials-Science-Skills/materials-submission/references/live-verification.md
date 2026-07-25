# Live-Verification Placeholders

## Why live verification

Journal formatting requirements change. The journal-formats fact sheets
are accurate as of early 2026 but must be re-checked before submission.

## Fields that always need live verification

- Word limit
- Abstract word count
- Reference cap
- APC rate
- Submission portal URL

These fields are listed in `live_verification_fields` in each
journal-templates yaml.

## Placeholder format

`[LIVE-VERIFICATION: <field name> — re-check against current Guide for Authors]`

The `build_submission_package.py` script refuses to write a final package
when `live_verification_acknowledged` is false. The user must set it to
true after re-checking every live-verification field.
