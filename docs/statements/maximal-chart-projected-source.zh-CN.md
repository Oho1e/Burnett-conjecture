# 任意光滑图上的统一投影散度源

[English](maximal-chart-projected-source.en.md)

本批对应锁定稿第 1602–1612 行。固定光滑最大图册中的任意图 $d$ 和支撑在图像内的光滑紧支截断 $\chi$。在 $d$ 中取原度量序列和背景度量的实际分量 $G_n,G_0$。这些分量由原张量在逆图的微分作用于坐标基向量后求值得到。

坐标变换的 Jacobian 与 Hessian 给出度量及其一阶导数的变换。通过图交叠上的紧集界和有限覆盖，将原来的局部一致收敛及一阶控制转移到给定图。联络及曲率的变换给出 Ricci 迹的自然性，从原序列的内禀真空条件得到这张图内的坐标真空方程。

实际零延拓 $z_n=\chi(G_n-G_0)$ 确定同一投影场 $u_n=\Pi z_n$。对每个 $1<p<\infty$，$\partial u_n$ 在 $L^p$ 中一致有界，$u_n$ 在 $L^p$ 和 $L^\infty$ 中趋于零。对给定的共同 Lipschitz 上界 $L$，可选一个 $C\geq 0$，使所有在 $\operatorname{tsupp}\chi$ 的邻域逐项等于真逆度量的合格光滑延拓族 $a_n$ 都满足

$$
\left\|-\sum_{a,b}\partial_a\bigl(a_n^{ab}\partial_bu_n\bigr)\right\|_{L^2(\mathbb R^4)}\leq C
\qquad\text{对所有 } n .
$$

同一 $z_n$ 的选择先于 $L$ 及延拓族，矩阵 $L^2$ 范数采用各分量范数的最大值。证明在给定图内施用第 53 批的欧氏开图定理和统一常数引理。

同一原序列的投影协方差与完整物理角向测度仍待识别。作者确认待记录。

- `Burnett.Geometry.MaximalChart.fixedForm_matrix_change`
- `Burnett.Geometry.MaximalChart.fixedForm_jet_change`
- `Burnett.Geometry.MaximalChart.fixedForm_connection_change`
- `Burnett.Geometry.MaximalChart.fixedForm_derivative_change`
- `Burnett.Geometry.MaximalChart.fixedForm_coordinateCurvature_change`
- `Burnett.Geometry.MaximalChart.fixedForm_coordinateVacuum_of_intrinsic`
- `Burnett.Geometry.MaximalChart.fixed_components_uniform_of_physical_C0loc`
- `Burnett.Geometry.MaximalChart.fixedJet_uniform_bound_on_compact`
- `Burnett.P01.exists_maximalChartProjectedField_norms_and_uniform_source`

[共同源码对应](maximal-chart-projected-source-source-bindings.json)
