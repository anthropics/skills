# Reviewer Risk Writing

Check every draft for these risks before producing output.

## Explicit warning patterns

| Risk pattern | Why reviewers attack it | Self-check | Fix |
|---|---|---|---|
| **Mechanism without characterization** | Inferring a full reaction or failure mechanism from a single signal. | Does every mechanism claim have at least two independent characterizations cross-validating it? | Downgrade to `consistent with` until a second technique is added, or add the second technique. |
| **Durability without service-condition evidence** | Claiming durability without wet, aged, or conditioned data. | Is every durability claim supported by an aging or service-condition test? | Add the test, or bound the claim to dry/lab conditions. |
| **Optimum claims without statistics** | Calling a dosage "optimal" without a full dose-response curve or statistical support. | Is the complete tested range reported, including the descending branch? | Complete the curve, or say `the highest value in the tested range`. |
| **Field claims without field validation** | Claiming field performance from lab-scale data. | Is every performance claim bounded to the tested conditions? | Add `under the tested conditions` or an explicit scale/simulation boundary. |

## General risks

- overclaim from performance to mechanism.
- missing evidence for novelty.
- Missing test conditions.
- Missing replicate count or statistics.
- journal fit mismatch.
- Durability wording without wet/aged/service conditioning.
- Field application language without field or simulated-service data.

Reviewer-safe writing states what is proven, why it matters, and what remains bounded.

## Materials-specific reviewer risk dimensions

Beyond the general risks above, materials manuscripts attract focused reviewer attacks on six dimensions. Scan each dimension before submission.

### 1. Mechanism over-attribution

Inferring a full reaction or failure mechanism from a single characterization signal (for example, one FTIR peak disappearance, one SEM image, or one XRD shift).

- Self-check: does every mechanism claim have at least two independent characterizations cross-validating it?
- Fix: downgrade the claim to `consistent with` until a second technique is added, or add the second technique.

### 2. Incomplete dose-response

Reporting only the optimal ratio or dosage without the full curve, including the descending branch where performance drops.

- Self-check: is the complete tested range reported, including non-optimal groups?
- Fix: complete the curve, or explicitly state `only the range X-Y was tested`.

### 3. Lab-to-field leap

Claiming field or engineering applicability directly from lab-scale results obtained under controlled conditions.

- Self-check: is every performance claim bounded to the tested conditions?
- Fix: add `under the tested conditions` or an explicit scale/simulation boundary.

### 4. Hidden trade-off

Reporting a strength gain while omitting a toughness loss, or reporting a benefit while omitting the cost (workability, cost, durability, setting time).

- Self-check: are all materially affected key performances reported, including unfavorable ones?
- Fix: report the trade-off metric, or state that it was not measured.

### 5. Standard deviation

Citing a standard (ASTM, ISO, GB, JTG) while the actual test conditions deviate from it in specimen size, curing regime, loading rate, or temperature.

- Self-check: does every standard citation carry the full test conditions actually used?
- Fix: report the deviation explicitly, or rephrase as `based on [standard] with modifications`.

### 6. Insufficient statistics

Weibull analysis with fewer than 10 specimens; no error bars; no replicate count; claiming significant difference from n=3.

- Self-check: does every quantitative result carry a replicate count and an uncertainty estimate?
- Fix: add statistics, or downgrade the claim to `observed trend`.

## Adversarial self-review workflow

After drafting, switch to reviewer mode and scan every claim against the dimensions above. Mark each located risk as `high`, `medium`, or `low`:

- `high`: a reviewer would likely reject or require major revision on this point.
- `medium`: a reviewer would request clarification or an additional sentence.
- `low`: wording polish only.

Fix every `high` risk before producing the output draft. Re-scan after each fix to confirm no new risk was introduced. Only output the draft when no `high` risk remains.
