# Introduction Variant 4 — Performance Ceiling

`Use when a hard performance ceiling exists and a new design route is the entry point. Distilled from introduction-gap-ladder.md Move 1-2 and published-article-patterns Pattern A/D.`

```latex
% Move 1: application demand — name the service requirement with a number
[应用场景] requires [材料] to sustain [性能指标] above [需求数值] under [服役条件], but current [材料家族] typically fail at [失效数值] ([文献范围]).

% Move 2: the ceiling — state the hard limit and where it comes from
This [需求数值] threshold represents a performance ceiling: beyond [配比/工艺极限], [主导策略] no longer raises [性能指标] because [物理/化学限制] ([文献范围]).

% Move 3: limits of existing modification routes
[策略A] and [策略B] approach the ceiling from [方向A] and [方向B] respectively, but both saturate near [饱和数值] because they share the same [限制因素] ([文献范围]).

% Move 4: the breakthrough entry — a different design route
A different route is needed: [新设计思路] bypasses [限制因素] by [机制], which in principle allows [性能指标] to exceed [天花板数值] under [服役条件].

% Move 5: this study's validation
Here, we prepared [材料变体] via [制备路线] and measured [性能集合] under [标准号/条件], combined with [表征方法], to test whether [新设计思路] can break the ceiling within [测试边界].
```

## Usage

- Move 1 and Move 2 must both carry numbers — a ceiling without a number is an opinion.
- Move 3 must explain why existing routes saturate at the same place (shared limiting factor), not just that they are insufficient.
- Move 4 is the conceptual entry: it must explain WHY the new route can bypass the shared limit, before any data.

## Gap quality check

The ceiling framing is weak if Move 4 simply says "we tried a new material". Anchor the entry to a mechanism ([机制]) that explains why the new route is not subject to the same [限制因素].
