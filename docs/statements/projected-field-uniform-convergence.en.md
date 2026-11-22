# Uniform smallness of the fixed projected fields

[简体中文](projected-field-uniform-convergence.zh-CN.md)

This delivery corresponds to lines 1602–1606, 1636–1638, and 1697–1701 of the locked manuscript. It uses the same fixed infrared-regularized projection.

- Lean writes the finite shell approximation as a sum of shell convolutions and a fixed correction. For each fixed Schwartz input and spatial point, it converges to the actual multiplier. Cancellation and the first moment of the shell kernels control the high-frequency tail. Given a common Lipschitz bound and an error threshold, the proof chooses the splitting scale to control the tail, then uses uniform smallness of the input to control the finite portion.
- Fix a smooth compactly supported cutoff $\chi$ and take globally smooth real coordinate components $g_n,g_0$ with uniform convergence and uniform first derivative bounds for the component differences on $\operatorname{supp}\chi$. For the actual complex Schwartz inputs $z_n=\chi(g_n-g_0)$, the same matrix projection $u_n=\Pi z_n$ tends to zero uniformly on the whole space and in the $L^\infty$ norm induced by the maximum of its sixteen entries. This is the same input $z_n$ used in the finite-exponent estimates.

The original open-chart inputs, the bounded whole-space divergence source, and preservation of the angular measure remain to be connected. Author confirmation is pending.

- `Burnett.P01.projected_shell_convolution_bounds`
- `Burnett.P01.projectionDyadicApproximation_eq_convolution`
- `Burnett.P01.projectionDyadicApproximation_tendsto`
- `Burnett.P01.gaugeProjectionSchwartzComponent_sup_bound`
- `Burnett.P01.gaugeProjectionSchwartzComponent_uniform_small`
- `Burnett.P01.projectionFullSchwartz_uniformly_small`
- `Burnett.P01.projectionFullSchwartz_eLpNorm_top_tendsto_zero`
- `Burnett.P01.localizedMetricProjection_uniformly_small`

[Shared source bindings](projected-field-uniform-convergence-source-bindings.json)
