# Survey Methodology

Reference for survey design and sampling. Pairs with `sample_size_planner.py`.

## Sample size from first principles

For estimating a proportion, the required sample is n₀ = z²·p·(1−p)/e², where z is the critical value for the confidence level, p the expected proportion, and e the margin of error. The maximum-variance choice p = 0.5 is the conservative default. When the sample is a meaningful fraction of a finite population N, apply the **finite-population correction**: n = n₀ / (1 + (n₀−1)/N). The planner does both.

The most common analyst error: powering the **overall** sample but then reporting **per-segment** results that the sample cannot support. If you will report three segments at ±8%, each segment needs ~150 respondents — so the survey must be sized to the segment floors, not the aggregate. The planner computes per-segment minimums explicitly.

## The total survey error framework

Sample size only addresses **sampling error**. Groves' total-survey-error framework names the others, often larger:

- **Coverage error** — the sampling frame omits part of the population (e.g., an email panel misses non-users).
- **Non-response error** — those who respond differ systematically from those who don't.
- **Measurement error** — the instrument itself biases answers (question wording, order, scale).

A tight margin of error on a biased frame is precision without accuracy.

## Question design

- **Avoid leading questions** that imply a preferred answer.
- **Avoid double-barreled questions** that ask two things at once ("Is the product fast and reliable?").
- **Watch scale and order effects** — response options and question sequence shift answers.
- **Pre-test** every instrument with a small cognitive-interview pass before fielding.

## Standards

AAPOR (American Association for Public Opinion Research) publishes disclosure standards and the standard definitions for response-rate calculation. Reputable market research follows them so results are comparable and auditable.

## Sources

1. Cochran, W.G., *Sampling Techniques*, 3rd ed. (Wiley, 1977).
2. Dillman, Smyth & Christian, *Internet, Phone, Mail, and Mixed-Mode Surveys: The Tailored Design Method*, 4th ed. (2014).
3. Groves et al., *Survey Methodology*, 2nd ed. (Wiley, 2009) — total survey error.
4. Schuman, H., & Presser, S., *Questions and Answers in Attitude Surveys* (1981) — wording/order effects.
5. AAPOR, *Standard Definitions: Final Dispositions of Case Codes and Outcome Rates for Surveys*.
6. Tourangeau, Rips & Rasinski, *The Psychology of Survey Response* (Cambridge, 2000).
