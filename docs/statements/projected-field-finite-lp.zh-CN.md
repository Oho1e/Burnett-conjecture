# 固定投影场的有限指数范数

[English](projected-field-finite-lp.en.md)

本批对应锁定稿第 1602–1606、1625–1642 和 1697 行。

- 将同一固定 Fourier 乘子的十六项输入合成为实际复矩阵 Schwartz 投影。它具有由原矩阵符号给出的弧度制 Fourier 作用，在物理空间消去 Schwartz 协向量的对称梯度，并与四个坐标导数分别交换。
- 对每个有限实数 $p>1$，同一有限常数统一估计矩阵场及其每一坐标导数的 $L^p$ 范数。矩阵按坐标分量最大范数取值。
- 给定全空间光滑的实坐标分量 $g_n,g_0$ 和固定光滑紧支截断 $\chi$，假设 $g_n$ 在 $\operatorname{supp}\chi$ 上一致趋于 $g_0$，且该处各分量差的一阶导数一致有界。Lean 构造同一实际截断输入 $z_n=\chi(g_n-g_0)$ 的复 Schwartz 场，证明其支撑、统一 Lipschitz 界及一致小性。对每个固定的有限 $p>1$，同一投影场 $u_n=\Pi z_n$ 在全空间 $L^p$ 中趋零，其梯度的全空间 $L^p$ 范数关于 $n$ 一致有界。

完整命题 `prop:general-projection` 还需接入原开坐标图的内禀序列、$L^\infty$ 趋零、全空间散度源和角向测度保持。作者确认待记录。

- `Burnett.P01.projectionFullSchwartz_radianFourier`
- `Burnett.P01.projectionFullSchwartz_symmetrizedGradient_eq_zero`
- `Burnett.P01.projectionFullSchwartz_coordinateDerivative`
- `Burnett.P01.exists_projectionFullSchwartz_finiteLp_bounds`
- `Burnett.P01.localizedMetricSchwartz_tsupport_subset`
- `Burnett.P01.localizedMetricSchwartz_uniform_inputs`
- `Burnett.P01.localizedMetricProjection_finiteLp_norms`

[共同源码对应](projected-field-finite-lp-source-bindings.json)
