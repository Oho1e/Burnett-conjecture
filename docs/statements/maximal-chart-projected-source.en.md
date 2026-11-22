# Uniform projected divergence source in any smooth chart

[简体中文](maximal-chart-projected-source.zh-CN.md)

This delivery covers lines 1602–1612 of the locked manuscript. Fix any chart $d$ in the smooth maximal atlas and a smooth compactly supported cutoff $\chi$ with support in its target. The metric sequence and background have their actual components $G_n,G_0$ in $d$, obtained by applying each original tensor to coordinate basis vectors pushed forward by the differential of the inverse chart.

The transition Jacobian and Hessian give the transformation of the metric and its first derivative. Bounds on compact chart overlaps and a finite cover transfer local uniform convergence and first-order control to the given chart. The transformation of the connection and curvature gives the naturality of the Ricci trace and hence coordinate vacuum in $d$ from the original intrinsic vacuum sequence.

The actual zero extension $z_n=\chi(G_n-G_0)$ determines one projected field $u_n=\Pi z_n$. For each $1<p<\infty$, $\partial u_n$ is uniformly bounded in $L^p$ and $u_n$ converges to zero in $L^p$ and $L^\infty$. Given a common Lipschitz bound $L$, one $C\geq 0$ gives the following estimate for all admissible smooth extensions $a_n$ that agree termwise with the true inverse metric near $\operatorname{tsupp}\chi$.

$$
\left\|-\sum_{a,b}\partial_a\bigl(a_n^{ab}\partial_bu_n\bigr)\right\|_{L^2(\mathbb R^4)}\leq C
\qquad\text{for all } n .
$$

The same $z_n$ is chosen before $L$ and the extension family. The matrix $L^2$ norm is the maximum of the component norms. The proof applies the Euclidean open-chart results and the uniform extension lemma from PR #53 in the given chart.

Identification of the projected covariance and the full physical angular measure of the same original sequence remains open. Author confirmation is pending.

- `Burnett.Geometry.MaximalChart.fixedForm_matrix_change`
- `Burnett.Geometry.MaximalChart.fixedForm_jet_change`
- `Burnett.Geometry.MaximalChart.fixedForm_connection_change`
- `Burnett.Geometry.MaximalChart.fixedForm_derivative_change`
- `Burnett.Geometry.MaximalChart.fixedForm_coordinateCurvature_change`
- `Burnett.Geometry.MaximalChart.fixedForm_coordinateVacuum_of_intrinsic`
- `Burnett.Geometry.MaximalChart.fixed_components_uniform_of_physical_C0loc`
- `Burnett.Geometry.MaximalChart.fixedJet_uniform_bound_on_compact`
- `Burnett.P01.exists_maximalChartProjectedField_norms_and_uniform_source`

[Shared source bindings](maximal-chart-projected-source-source-bindings.json)
