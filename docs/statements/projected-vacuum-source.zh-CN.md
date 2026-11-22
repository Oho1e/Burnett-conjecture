# 投影真空余项与全空间散度源

[English](projected-vacuum-source.en.md)

本批对应锁定稿第 1602–1612、1644–1672 和 1685–1695 行。固定光滑紧支截断 $\chi$，将 $z_n=\chi(g_n-g_0)$ 零延拓，令 $u_n=\Pi z_n$，其中 $\Pi$ 沿用已登记的固定矩阵 Fourier 投影。

坐标 Ricci 恒等式将最高阶波项与降指标规范协向量的对称梯度分开。用真空条件和乘积法则移入 $\chi$ 后，波源 $Q_A z_n$ 等于一个紧支对称梯度与局部余项之和。$\Pi$ 消去该梯度，因此 $\|\Pi Q_Az_n\|_{L^2}$ 由局部余项控制。余项的统一界使用度量和逆分量的一阶数据、光滑背景的二阶数据及固定截断。

全空间负散度具有实际的 $L^2$ 代表。令 $Q_A=\sum_{a,b}A^{ab}\partial_{ab}$，代表满足

$$
-\sum_{a,b}\partial_a(A^{ab}\partial_bu_n)
=-\Pi Q_Az_n+\sum_{a,b}[\Pi,A^{ab}]\partial_{ab}z_n
-\sum_{a,b}(\partial_aA^{ab})\partial_bu_n .
$$

第二项调用同一 $\Pi$ 的矩阵交换子估计。右侧每项都在整个 $\mathbb R^4$ 的 $L^2$ 中控制，覆盖 $\operatorname{supp}\chi$ 外的投影尾部。矩阵范数是各分量 $L^2$ 范数的最大值。

开图定理接受图内实际坐标分量和坐标真空；内禀定理从原光滑真空序列在标准 $\mathrm{chartAt}$ 图中取得这些数据。最终先固定一个 $z_n$，使同一 $u_n$ 已满足有限 $L^p$ 梯度界及 $L^p$、$L^\infty$ 趋零。给定共同 Lipschitz 上界 $L$，再选择一个 $C\ge 0$，同时控制所有光滑延拓族和所有 $n$ 的全空间负散度。这些延拓逐项在 $\operatorname{tsupp}\chi$ 的邻域等于坐标真逆。本估计对延拓的控制只使用一阶 Lipschitz 界。

任意相容光滑图的内禀转移及同一原序列完整角向测度的识别仍待接入。作者确认待记录。

- `Burnett.P01.twice_coordinateRicci_eq_wave_symmetrizedGauge_remainder`
- `Burnett.P01.localizedVacuumSource_eq_symmetrizedGauge_add_remainder`
- `Burnett.P01.exists_localizedVacuumSourceRemainder_majorant`
- `Burnett.P01.exists_norm_projection_of_localizedVacuumSource_le`
- `Burnett.P01.projectedSourceDivergenceL2_ae`
- `Burnett.P01.projectedSourceDivergenceL2_eq_projected`
- `Burnett.P01.exists_projectedSourceDivergenceL2_bound`
- `Burnett.P01.projectedSourceQ_eq_localizedWaveSourceSchwartz`
- `Burnett.P01.exists_wholeSpace_projectedVacuumDivergenceL2_bound`
- `Burnett.P01.exists_projectedVacuumDivergenceL2_of_openChart`
- `Burnett.P01.exists_projectedVacuumDivergenceL2_of_intrinsic`
- `Burnett.P01.projectedSource_uniform_extension_bound`
- `Burnett.P01.exists_intrinsicChartProjectedField_norms_and_uniform_source`

[共同源码对应](projected-vacuum-source-source-bindings.json)
