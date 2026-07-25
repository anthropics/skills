# Introduction Variant 2 — Trade-off Contradiction

`Use when existing strategies each sacrifice a different property and the contradiction is unresolved. Distilled from introduction-gap-ladder.md Move 2 and published-article-patterns Pattern E/L.`

```latex
% Move 1: classic material trade-off — name both properties
For [材料家族], [性能A] and [性能B] are known to compete: raising one typically lowers the other under [服役条件] ([文献范围]).

% Move 2: strategy A — what it gains and what it sacrifices
[策略A] improves [性能A] by [机制A], but its effect on [性能B] is inconsistent across [测试条件], with reported losses of [变化幅度] ([文献范围]).

% Move 3: strategy B — the mirror sacrifice
[策略B], in contrast, protects [性能B] through [机制B], but caps [性能A] at [天花板数值] because [限制原因] ([文献范围]).

% Move 4: contradiction as gap — frame the tension, not a missing topic
This creates a contradiction between [性能目标A] and [性能目标B]: no reported strategy simultaneously improves both within [配比/工艺窗口], and the structure-property link that would enable such a design remains unclear.

% Move 5: this study — how the design addresses both at once
Here, we propose [材料设计] that [设计思路], and evaluate both [性能A] and [性能B] together with [表征方法] to test whether [假设] can resolve the trade-off within [测试边界].
```

## Usage

- Move 1 must name BOTH competing properties in the first sentence.
- Moves 2 and 3 are mirror images — each strategy's gain is the other's sacrifice.
- Move 4 frames the gap as a contradiction, which is more compelling than "few studies exist".

## Gap quality check

The contradiction is weak if Move 4 could be resolved by simply combining strategy A and B. Anchor the gap to a structure-property link ([表征方法]) that no prior strategy has provided.
