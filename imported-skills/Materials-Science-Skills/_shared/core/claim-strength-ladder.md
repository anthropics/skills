# Claim-Strength Ladder

Match language strength to evidence strength.

| Evidence | Safe claim strength | Example |
|---|---|---|
| single measured trend | observed trend | The bonding strength increased with epoxy content. |
| replicated trend with control | supported conclusion | The modified emulsion exhibited higher bonding strength than the control. |
| mechanism test plus performance | mechanism-supported interpretation | FTIR and fluorescence observations suggest improved compatibility and network formation. |
| field or service simulation | engineering implication | The material shows potential for pavement maintenance applications under similar conditions. |
| LCA/cost/resource data | sustainability claim | The system may reduce environmental burden within the assessed boundary. |

## Downgrade Rules

- Change `proves` to `suggests` unless direct proof exists.
- Change `significantly improves` to `improves` unless statistical significance is reported.
- Change `environmentally friendly` to `potentially sustainable` only if a boundary is stated.
- Change `first` or `novel` to a precise gap unless a live literature check supports priority.
- Change `mechanism was confirmed` to `mechanism was inferred` when only performance data exist.

## Civil Materials Red Flags

- "The mechanism is..." without FTIR, SEM, fluorescence, rheology, hydration, or equivalent evidence.
- "Durability was improved" without aging, moisture, freeze-thaw, retained strength, or service-condition data.
- "Suitable for engineering application" without constructability, storage stability, viscosity, dosage, or field boundary.

## Handling Negative or Inconclusive Results

Use negative results to define boundaries, not to hide failure.

### Non-significant trend

Before:

> The 15% epoxy dosage significantly improved bonding strength.

After:

> The 15% epoxy group showed a higher mean bonding strength than the 10% group, but the difference was not statistically significant (p = 0.12). The trend is therefore interpreted cautiously and should be confirmed with additional replicates.

### Performance decreases at high dosage

Before:

> Higher epoxy dosage improves the emulsion performance.

After:

> Bonding strength increased up to the intermediate epoxy dosage but decreased at 20%, indicating a dosage-dependent threshold. The decrease may be associated with increased viscosity or phase separation, but direct morphology evidence is required before assigning a mechanism.

### Mechanism evidence does not match hypothesis

Before:

> FTIR confirmed the expected curing mechanism.

After:

> FTIR did not show the expected reduction of the oxirane peak for the low-dosage group, suggesting that curing may have been incomplete under the tested condition. The mechanism discussion was revised to reflect this uncertainty.
