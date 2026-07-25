# RQ Framing Pattern Gold Set

Issue: #257

This gold set calibrates the Socratic wording-pattern advisory. It measures whether a conservative lexical detector catches common AI-typical research-question wording shells without over-warning domain-native research questions.

## Labels

- `wording_cliche`: surface wording matches one of the WP01-WP20 shell patterns.
- `domain_native`: wording is specific enough that the advisory should not trigger, even if the topic itself is broad.

## Scope

The detector and gold set evaluate wording only. They do not judge idea quality, novelty, feasibility, or contribution.

## Acceptance Thresholds

- FNR < 0.30
- FPR < 0.20
- balanced accuracy >= 0.75

Run:

```bash
python -m scripts.check_rq_framing_patterns
```
