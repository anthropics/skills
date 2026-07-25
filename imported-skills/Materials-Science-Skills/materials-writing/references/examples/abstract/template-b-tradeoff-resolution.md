# Abstract Template B — Trade-off Resolution

`Use when your design improves two competing properties at once (e.g. strength-toughness, efficiency-stability). Distilled from abstract-claim-arc.md and published-article-patterns Pattern E/L.`

```latex
% Move 1: classic contradiction — name the two competing properties explicitly
For [材料家族], improving [性能A] typically comes at the cost of [性能B], creating a long-standing trade-off between [工程目标A] and [工程目标B].

% Move 2: what each existing strategy sacrifices
[策略A] raises [性能A] but reduces [性能B], while [策略B] protects [性能B] but caps [性能A] ([文献范围]).

% Move 3: this design — how it addresses both at once
Here, we designed [材料变体] by [设计思路] to simultaneously improve [性能A] and [性能B] without the usual sacrifice.

% Move 4: dual-indicator result — both numbers, both conditions
Under [测试条件], the [优化配比] achieved [性能A数值] ([变化百分比] vs. control) while maintaining [性能B数值] ([变化百分比] vs. control), breaking the conventional [性能A]-[性能B] trade-off.

% Move 5: mechanism — why both can improve together
[表征技术] indicates that [结构特征] allows [机制A] and [机制B] to coexist, which is consistent with the dual improvement.

% Move 6: boundary — where the trade-off resolution stops holding
The dual improvement holds within [配比/工艺窗口] and under [测试条件]; [未验证的服役场景] may restore the trade-off and requires further study.
```

## Usage

- Move 1 must name BOTH properties — a trade-off abstract with only one property is incomplete.
- Move 4 must report BOTH numbers with their own comparison baseline.
- Move 6 must state where the resolution fails, not just where it works.

## Anti-overclaim check

- Do NOT write: `[材料] solves the strength-toughness problem.`
- Write instead: `[材料] improves [性能A] and [性能B] simultaneously under [测试条件], within the tested [配比] range.`
- Do NOT claim the trade-off is "eliminated" — say it is "mitigated" or "broken within the tested window".
