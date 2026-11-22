# 实际投影场的加权双导数配对

[English](weighted-projected-derivative-pairings.en.md)

本批接续锁定稿第 1602–1615 和 1703–1709 行。令 $z_n=\chi(G_n-G_0)$ 为实际截断的坐标度量扰动的零延拓，$u_n=\Pi z_n$ 使用已经形式化的固定投影。给定光滑坐标代表、截断支撑上的一致收敛与一阶界，Lean 证明实际 $\partial_s z_n$ 的共同支撑、分量 $L^2$ 一致界与测试弱零。

对实光滑紧支权 $d$，乘积法则给出 $\partial_s z_n-\chi\partial_s(G_n-G_0)=(\partial_s\chi)(G_n-G_0)$。乘以 $d$ 后，右侧在 $L^2$ 中强趋零。在原流形的首选图中，可以选定一个 $d$，使它在截断支撑上等于原坐标体积半密度，并选定同一 $z_n$。于是加权实际截断导数和原序列的坐标体积加权梯度仍有这个 $L^2$ 强零差。

半密度与固定投影交换所产生的误差也在 $L^2$ 中强趋零。对于两个独立的导数方向 $\alpha,\beta$，若给定原加权梯度的有序角向配对见证，其积分密度为 $\xi_\alpha\xi_\beta A$，则实际 $d\partial_\alpha u_n$ 和 $d\partial_\beta u_n$ 的有序配对极限密度为

$$
\xi_\alpha\xi_\beta\bigl(P(\xi) A P(\xi)^*\bigr)_{ji}.
$$

这里 \(P\) 是同一 \(\Pi\) 的齐次主符号，\(A\) 是原振幅，\(j,i\) 对应被算子作用的第二槽和第一槽。结论保留原配对参数和同一个截断场。从原真空序列提取共同测度与振幅，以及跨图识别为同一全局物理角向测度，仍待接入。作者确认待记录。

- `Burnett.P01.tendsto_weighted_localizationError_L2_zero`
- `Burnett.P01.localizedMetricSchwartz_coordinateDerivative_real`
- `Burnett.P01.localizedMetric_weighted_derivative_sub_original_tendsto_zero`
- `Burnett.P01.localizedMetricSchwartz_coordinateDerivative_eq_partial`
- `Burnett.P01.localizedMetricSchwartz_coordinateDerivative_test_tendsto_zero`
- `Burnett.P01.exists_localizedMetricSchwartz_coordinateDerivative_defect_inputs`
- `Burnett.P01.projectedDefectComponent_halfDensity_commutator_tendsto_zero`
- `Burnett.P01.projectionFullSchwartz_halfDensity_sub_tendsto_zero`
- `Burnett.P01.defectPairing_sub_tendsto_zero_of_strong_errors`
- `Burnett.P01.projectionFullSchwartz_weighted_defectPairing_tendsto`
- `Burnett.P01.projectionFullSchwartz_weighted_mixed_defectPairing_tendsto`
- `Burnett.P01.projectedLocalizedMetric_weighted_mixedPairing_tendsto`
- `Burnett.P01.exists_intrinsic_originalGradient_halfDensity_error_tendsto_zero`

[共同源码对应](weighted-projected-derivative-pairings-source-bindings.json)
