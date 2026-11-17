# 原几何条件下局部线性化 Ricci 的强 H⁻¹ 收敛

[English](geometric-Hminus-closure.en.md)

本批对应锁定原文第 358–388 行，主要结论对应第 384–388 行。七项支持目标从同一组几何数据导出，对每张固定 preferred 图、每对固定张量指标和每个支撑紧含图域的光滑截断 χ，实际线性化 Ricci 的局部化在 H⁻¹ 算子范数下强趋于零。

固定辅助 Riemann 度量 r、光滑对称非退化背景 g₀ 及光滑对称非退化序列 gₙ。沿用相对于 r 的局部一致收敛，以及同一 g₀ 几何测度下逐紧集的 Dʳ(gₙ−g₀) 一致 L∞ 界。线性化算子内部使用背景导数 Dᵍ⁰。定理仍显式要求每个 gₙ 在该图内的实际坐标 Ricci 为零。全文所需的内禀真空到该局部前提的桥另有证明任务。

设 Cₙ 为真实连接差，Eₙ 为 Cₙ 的线性近似余项，Aₙ = −Ric(g₀) − Q(Cₙ)。在该图内有精确恒等式 ℒhₙ = Aₙ − DivΓ₀ Eₙ。证明将同一 χAₙ 和 χDivΓ₀ Eₙ 实现为强趋零的连续线性泛函，其中散度估计保留截断导数 Dχ，带密度 ρ₀ 的版本保留 D(χρ₀) 的完整修正。对固定图紧集需要的 Cₙ 一致界覆盖全部 n，包括有限个早期指标。整个构造只使用原有的一阶统一控制。

最终 Lean 定理 `Burnett.Analysis.GeometricHminusPrincipalClosure.linearizedRicci_has_strong_realization_of_original` 同时给出连续对偶序列 Fₙ、每个 n 和真实紧支撑光滑测试 φ 的乘积 φχℒhₙ 的可积性、Fₙ 在 φ 上等于此积分的身份，以及 Fₙ 与其算子范数的强零极限。图外只使用 χ 为零。

这项逐图、逐分量的结果供 F04 后续全局张量测试和 F05 定位使用。跨图拼合、内禀 Lorentz 真空包装和共同缺陷测度仍待完成。作者对本批新数学对应的确认仍待记录。

[独立复核](geometric-Hminus-closure-review.md) · [源码绑定](geometric-Hminus-closure-source-bindings.json)
