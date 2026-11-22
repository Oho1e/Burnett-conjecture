# Norms of the projected fields from the original open chart

[简体中文](open-chart-projected-norms.zh-CN.md)

This delivery addresses the norm conclusions at manuscript lines 1602–1606 using local uniform convergence and first derivative bounds on compact sets from lines 91–103.

- For an open set $U$ and a compact set $K\subset U$, one auxiliary smooth cutoff equals $1$ in an open neighborhood of $K$ and is compactly supported in $U$. The cutoff supplies global smooth representatives of the entire sequence and the background. Agreement near $K$ transfers values and first derivatives.
- Coordinate components are smooth on $U$. A globally smooth $\chi$ with compact support in $U$ represents the manuscript cutoff. Lean identifies the same whole-space Schwartz input $z_n=\chi(g_n-g_0)$ pointwise, including its zero value outside $U$. Given uniform convergence and a common first derivative bound for the component differences on $\operatorname{supp}\chi$, the same projected field $u_n=\Pi z_n$ tends to zero uniformly and in $L^\infty$. For every $1<p<\infty$ it tends to zero in $L^p$ and its full gradient is uniformly bounded in $L^p$.
- For a fixed manifold chart `chartAt c`, the smooth intrinsic tensor sequence, nondegenerate smooth background, local uniform convergence measured by the auxiliary metric, and compact-set covariant derivative bound supply the coordinate hypotheses. A single construction gives the actual chart fluctuation $z_n$ and all of the norm conclusions.

The full P01 proposition still requires the whole-space divergence source and preservation of the angular measure for that same projected field. Author confirmation is pending.

- `Burnett.P01.exists_projectedChartCutoff`
- `Burnett.P01.exists_openChartMetricRepresentatives`
- `Burnett.P01.exists_openChartProjectedField_norms`
- `Burnett.P01.exists_intrinsicChartProjectedField_norms`

[Shared source bindings](open-chart-projected-norms-source-bindings.json)
