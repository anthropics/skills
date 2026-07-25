# Workflow

1. Read `manifest.yaml` and every `always_load` file.
2. Apply profile-first routing.
3. Detect all response axes and load their mapped paths from the manifest.
4. Assign a stable ID to every reviewer comment.
5. Classify the concern and choose ACCEPT_TEXT, ACCEPT_ANALYSIS,
   SOFTEN_CLAIM, DISAGREE, or AUTHOR_INPUT_NEEDED.
6. Separate the reviewer concern, response, manuscript action, evidence basis,
   and revision proof.
7. Load detailed strategy, remediation, language, format, ethics, evidence, or
   weakness guidance only when its manifest condition applies.
8. Emit the response package and, when composed, the response handoff.
9. Regression-check each claimed revision against the revised manuscript.
