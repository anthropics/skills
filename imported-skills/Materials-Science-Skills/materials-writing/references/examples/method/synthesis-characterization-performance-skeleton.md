# Method Section Skeleton — Synthesis / Characterization / Performance

`Three-part skeleton for materials methods. Distilled from methods.md fragment and published-article-patterns Pattern F/G. Each subsection must be reproducible.`

```latex
% Overview — 1-2 sentences setting, 1-2 sentences core contribution, optional figure pointer, subsection map
[材料体系] was prepared by [制备路线] and evaluated for [性能集合] under [标准/条件]. The experimental program is illustrated in [图号] and organized as: synthesis (Section [x.1]), characterization (Section [x.2]), and performance testing (Section [x.3]).

\subsection{Synthesis and specimen preparation}
% Precursors — source, purity/specification, pretreatment
[前驱体A] ([来源, 纯度/规格]) and [前驱体B] ([来源, 纯度/规格]) were used as received / dried at [温度] for [时间].
% Formulation — precise units (wt%, phr, mol%, ratio)
Mixtures were prepared at [配比] ([单位]) of [组分] into [基体], with [添加剂] at [剂量].
% Processing parameters — temperature, time, pressure, atmosphere, cooling rate
[工艺步骤] was conducted at [温度] for [时间] under [气氛/压力], followed by [冷却/后处理].
% Standard or adapted protocol citation
The preparation followed [标准号/协议] with the following modifications: [修改内容].

\subsection{Characterization}
% For each technique: instrument, parameters, AND the purpose (what question it answers)
[表征技术A] was performed on [仪器型号] ([参数范围], [扫描次数/分辨率]) to monitor [化学键/相/形貌特征] at [特征信号].
[表征技术B] was performed on [仪器型号] ([参数]) to determine [相组成/结晶度/晶格参数/微观结构].
% See characterization-purpose-library.md for purpose-sentence templates per technique.

\subsection{Performance testing}
% Standard, specimen geometry, replicates, condition
[性能指标] was measured according to [标准号] using [试件几何/尺寸], with [重复次数] replicates per group.
% Test condition — temperature, humidity, aging state, loading
Specimens were conditioned at [温度]/[湿度] for [时间] before testing under [加载条件/速率].
% Statistical method
Results are reported as mean ± [标准差/置信区间]. Statistical comparison used [检验方法] at [显著性水平] ([软件]).
```

## Usage

- Every `[标准号]` must be a real standard you actually followed — keep a placeholder if unknown rather than inventing one.
- Each characterization entry must state the purpose (what question it answers), not just "X was performed".
- Replicates and statistical method are mandatory; a method without them is not reproducible.
