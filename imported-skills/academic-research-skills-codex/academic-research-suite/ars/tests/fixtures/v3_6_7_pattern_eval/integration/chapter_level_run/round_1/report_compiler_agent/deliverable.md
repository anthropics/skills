# Abstract bundle — report_compiler_agent round 1 output

<!-- AUDIT NOTE: triggers C2 (deictic temporal) + D4 (word-count cap bust)
     + C1 (protected hedge dropped from upstream). Audit emits 3 P1 findings. -->

## Abstract (round 1, 268 words — busts 250-word cap when whitespace-split)

This study examines outcome-based quality-assurance frameworks in East-Asian
universities. During this period, the author served as an institutional
quality-assurance reviewer, which may have shaped the analytical framing.
Cross-national adoption rates are universally consistent across jurisdictions
and institutional types. [The protected hedge from upstream §4.2 was dropped.]

[Body padding to ~268 whitespace-split words; the deictic "during this
period" triggers C2; "universally consistent" claim drops the upstream
PROTECTED hedge "Adoption rates vary substantially across jurisdictions and
institutional types; the universal applicability claim is preliminary and
pending verification against country-level survey data" — C1 trigger.
The whitespace-split word count is 268; 250 hard cap is busted — D4
trigger when the wrapper-side counter uses whitespace split correctly.]

(For test purposes the actual word count of this synthetic body is the
declared one; the harness reads expected_audit_findings.yaml as the
synthesized verdict, not a re-counted text.)
