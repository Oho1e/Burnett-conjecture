# 固定投影场的一致趋零

[English](projected-field-uniform-convergence.en.md)

这批对应锁定稿第 1602–1606、1636–1638 和 1697–1701 行，沿用固定的红外正则化投影。

- Lean 将有限壳近似写成逐壳卷积和固定修正，并证明它对每个固定的 Schwartz 输入和空间点收敛到实际乘子。壳核的零均值与一阶矩给出高频尾估计。给定输入的共同 Lipschitz 界和误差阈值，先选分割尺度控制尾项，再用输入的全空间一致小性控制有限项。
- 对每个固定的光滑紧支截断 $\chi$，取全空间光滑的实坐标分量 $g_n,g_0$，在 $\operatorname{supp}\chi$ 上满足一致收敛及各分量差的一阶导数一致有界。以 $z_n=\chi(g_n-g_0)$ 为实际复 Schwartz 输入，同一矩阵投影 $u_n=\Pi z_n$ 在全空间一致趋零，且十六个坐标分量最大范数的 $L^\infty$ 范数趋零。这里的 $z_n$ 与有限指数结论使用的输入相同。

后续还需从原始开坐标图假设得到上述输入，并接入全空间有界散度源及角向测度保持。作者确认待记录。

- `Burnett.P01.projected_shell_convolution_bounds`
- `Burnett.P01.projectionDyadicApproximation_eq_convolution`
- `Burnett.P01.projectionDyadicApproximation_tendsto`
- `Burnett.P01.gaugeProjectionSchwartzComponent_sup_bound`
- `Burnett.P01.gaugeProjectionSchwartzComponent_uniform_small`
- `Burnett.P01.projectionFullSchwartz_uniformly_small`
- `Burnett.P01.projectionFullSchwartz_eLpNorm_top_tendsto_zero`
- `Burnett.P01.localizedMetricProjection_uniformly_small`

[共同源码对应](projected-field-uniform-convergence-source-bindings.json)
