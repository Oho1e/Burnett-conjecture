# 辅助度量变换下的真空序列假设

[English](auxiliary-metric-admissibility.en.md)

锁定原文第 91–106 行使用辅助黎曼度量的 Levi-Civita 联络控制四维流形上的光滑序列。以下结论在变换辅助度量时同时比较张量范数和联络。

- `physicalNorm2_compact_compare` — 在给定紧集上，对任意协变二张量，其 s 范数至多为 r 范数的一个常数倍。常数对点和张量均统一。

- `locallyUniformlyConverges_changeAuxiliary` — 由 r 度量的局部一致收敛推出由 s 度量的局部一致收敛，序列和极限保持同一。

- `normScalar_compact_compare` — 在每个紧集上有与光滑二张量 H 无关的常数，使其 s 联络导数的 s 范数至多为该常数乘以 r 联络导数及 H 的两个 r 范数之和。

- `compactDhBound_changeAuxiliary` — 由局部一致收敛和度量误差的 r 联络导数在紧集上的原 L∞ 界，推出 s 联络导数满足对所有 n 统一的界。采用同一背景几何体积，有限个初始指标单独估计。

- `admissible_iff_changeAuxiliary` — 对给定的光滑近似度量和光滑背景，每项内禀 Ricci 真空、局部一致收敛和紧集一阶导数界这三条条件，对 r 成立当且仅当对 s 成立。Lorentz 符号和时间定向属于给定度量及背景本身。

独立复核者将九项公开声明与原文假设对照，并重新编译了两份 Lean 源码。

此结论可用于同一子列在不同辅助度量下的构造。微局部测度的变换律及输运方程需要单独证明。 [源码对应](auxiliary-metric-admissibility-source-bindings.json)
