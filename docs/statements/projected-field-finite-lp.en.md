# Finite-exponent norms of the fixed projected fields

[简体中文](projected-field-finite-lp.zh-CN.md)

This delivery corresponds to lines 1602–1606, 1625–1642, and 1697 of the locked manuscript.

- The sixteen input entries of the same fixed Fourier multiplier assemble into an actual matrix Schwartz projection. Its radian Fourier action is the original matrix symbol. It annihilates symmetric gradients of Schwartz covectors in physical space and commutes with every coordinate derivative.
- For every finite real $p>1$, a common finite constant controls the matrix field and each coordinate derivative in $L^p$. The matrix values use the maximum norm over the coordinate entries.
- Take globally smooth real coordinate components $g_n,g_0$ and a fixed smooth compactly supported cutoff $\chi$. Assume uniform convergence of $g_n$ to $g_0$ and uniform bounds on the first derivatives of the component differences on the support of $\chi$. Lean constructs the complex Schwartz fields for the actual inputs $z_n=\chi(g_n-g_0)$ and proves their support, uniform Lipschitz bounds, and uniform smallness. For each fixed finite $p>1$, the same projected fields $u_n=\Pi z_n$ tend to zero in whole-space $L^p$ and have gradients uniformly bounded in whole-space $L^p$.

The full `prop:general-projection` still requires the intrinsic sequence on the original open chart, $L^\infty$ convergence, the whole-space divergence source, and preservation of the angular measure. Author confirmation is pending.

- `Burnett.P01.projectionFullSchwartz_radianFourier`
- `Burnett.P01.projectionFullSchwartz_symmetrizedGradient_eq_zero`
- `Burnett.P01.projectionFullSchwartz_coordinateDerivative`
- `Burnett.P01.exists_projectionFullSchwartz_finiteLp_bounds`
- `Burnett.P01.localizedMetricSchwartz_tsupport_subset`
- `Burnett.P01.localizedMetricSchwartz_uniform_inputs`
- `Burnett.P01.localizedMetricProjection_finiteLp_norms`

[Shared source bindings](projected-field-finite-lp-source-bindings.json)
