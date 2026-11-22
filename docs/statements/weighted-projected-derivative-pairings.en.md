# Weighted mixed derivative pairings of the actual projected field

[简体中文](weighted-projected-derivative-pairings.zh-CN.md)

This delivery concerns lines 1602–1615 and 1703–1709 of the locked manuscript. Let $z_n=\chi(G_n-G_0)$ be the zero extension of the actual cutoff coordinate metric perturbation, and let $u_n=\Pi z_n$ use the existing fixed projection. For smooth coordinate representatives with uniform convergence and a first-derivative bound on the cutoff support, the actual $\partial_s z_n$ has common compact support, uniform componentwise $L^2$ bounds, and weak convergence to zero against smooth tests.

For a real smooth compactly supported weight $d$, the product rule gives $\partial_s z_n-\chi\partial_s(G_n-G_0)=(\partial_s\chi)(G_n-G_0)$. Multiplication by $d$ makes the right-hand term converge strongly to zero in $L^2$. In a preferred chart of the original manifold, one can choose $d$ to agree on the cutoff support with the actual coordinate volume half-density and choose the same $z_n$. This relates the weighted cutoff derivative to the original sequence's volume-weighted coordinate gradient with a strongly vanishing $L^2$ error.

Commuting the half-density weight with the fixed projection also gives a strongly vanishing $L^2$ error. For independently chosen derivative directions $\alpha,\beta$, suppose the ordered angular pairing witness for the original weighted gradients has density $\xi_\alpha\xi_\beta A$. The ordered pairing of the actual $d\partial_\alpha u_n$ and $d\partial_\beta u_n$ then has limiting density

$$
\xi_\alpha\xi_\beta\bigl(P(\xi) A P(\xi)^*\bigr)_{ji}.
$$

Here \(P\) is the homogeneous principal symbol of the same \(\Pi\), and \(A\) is the original amplitude. The indices \(j,i\) are ordered with the operator applied to the second pairing slot. The result uses the same pairing parameters and cutoff field. Extraction of a common trace measure and amplitude from the original vacuum sequence and identification across charts with its global physical angular measure remain to be connected. Author confirmation is pending.

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

[Shared source bindings](weighted-projected-derivative-pairings-source-bindings.json)
