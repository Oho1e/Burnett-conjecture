# 原开坐标图上的投影场范数

[English](open-chart-projected-norms.en.md)

本批对应锁定稿第 1602–1606 行的范数结论，并使用第 91–103 行中的局部一致收敛和紧集一阶导数界。

- 给定开集 $U$ 和紧集 $K\subset U$，取一个在 $K$ 的开邻域等于 $1$、紧支于 $U$ 的辅助光滑截断。它同时给整个序列与背景构造全空间光滑代表。代表在 $K$ 的邻域与原坐标分量相同，因此函数值和一阶导数都可传递。
- 对只在 $U$ 上要求光滑的坐标分量，以全空间光滑且紧支于 $U$ 的 $\chi$ 表示原稿的截断。Lean 在全空间识别同一个 Schwartz 输入 $z_n=\chi(g_n-g_0)$，它在 $U$ 外为零。若在 $\operatorname{supp}\chi$ 上满足一致收敛和分量差一阶导数的共同界，同一实际投影场 $u_n=\Pi z_n$ 全空间一致趋零并在 $L^\infty$ 中趋零，对每个 $1<p<\infty$ 在 $L^p$ 中趋零且全梯度一致有界。
- 对固定的流形坐标图 `chartAt c`，Lean 从光滑内禀张量序列、非退化的光滑背景、以辅助度量计的局部一致收敛和紧集协变导数界，推导上述坐标输入。一个构造同时给出原图的 $z_n$ 及全部范数结论。

完整 P01 还需将全空间散度源和角向测度保持接到这同一个投影场。作者确认待记录。

- `Burnett.P01.exists_projectedChartCutoff`
- `Burnett.P01.exists_openChartMetricRepresentatives`
- `Burnett.P01.exists_openChartProjectedField_norms`
- `Burnett.P01.exists_intrinsicChartProjectedField_norms`

[共同源码对应](open-chart-projected-norms-source-bindings.json)
