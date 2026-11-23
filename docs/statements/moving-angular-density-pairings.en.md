# Angular test pairings after a change of charts

This batch advances F05. Let \(K\) be a compact closed ball in an actual preferred-chart overlap, let \(y=\Phi(x)\) be the chart transition, and put \(L_x=(D\Phi(x)^*)^{-1}\). The source base test \(a\) is smooth with support in \(K\) and satisfies \(a=b\circ\Phi\) on \(K\), where \(b\) is the bounded target test. The angular symbol \(m\) is bounded, homogeneous of degree zero under positive scaling, and smooth away from zero frequency.

Let \(f_{n,i}\) be a Schwartz representative of the actual volume half-density weighted coordinate gradient in slot \(i\). Let \(T\) be transport by the inverse Jacobian half-density, extended by zero outside \(\Phi(K)\). On the same subsequence \(\sigma\) already represented by the source-chart matrix measure, write \(\tau\) for its trace and \(\rho_{ij}\) for the density of the ordered entry. The result is

\[
\lim_{n\to\infty}
\big\langle Tf_{\sigma(n),i},\, b\,[(1-\chi_0)m](D)\,Tf_{\sigma(n),j}\big\rangle_{L^2}
= \int_{K\times S^3} a(x)\,m(L_x\xi)\,\rho_{ij}(x,\xi)\,d\tau(x,\xi).
\]

Here \(\chi_0\) is the fixed low-frequency core and Lean's inner product is linear in the second slot. Transport preserves the actual \(L^2\) inner product. The base Fourier coefficients retain smoothness away from zero and degree-zero homogeneity. A common integrable envelope permits integration of the separated test limits on that subsequence. The transformed compact low-frequency contribution and the preceding conjugation error both vanish strongly in \(L^2\).

The remaining steps are to relate the transported slots to the actual target-chart gradient by the three-slot coordinate coefficients, prove compatibility of the measures and the local cutoffs, and glue the globally defined measure. This delivery registers supporting results for F05. Author confirmation is recorded in the project scope. [F05 slice](../formalization/slices.en.md#f05)

- `Burnett.Analysis.contDiffOn_integral_compact_parameter`
- `Burnett.Microlocal.Overlap.exists_uniform_baseDerivative_of_homogeneousAngular`
- `Burnett.Microlocal.Overlap.firstOrderAction_eq_integral_baseFourierModes`
- `Burnett.Microlocal.Overlap.firstOrderAction_pairing_eq_integral_separable_baseFourier`
- `Burnett.Microlocal.Overlap.baseFourierCoefficient_inverse`
- `Burnett.Microlocal.Overlap.exists_compactBaseAngular_leftFourier_pairing`
- `Burnett.Microlocal.Overlap.contDiffOn_baseFourierCoefficient`
- `Burnett.Microlocal.Overlap.degreeZero_baseFourierCoefficient`
- `Burnett.Microlocal.OverlapKernel.chartTransitionFrequency_eq_frozen`
- `Burnett.Microlocal.OverlapKernel.frozenChartFrequency_cotangentCoords`
- `Burnett.Microlocal.OverlapKernel.contDiffOn_chartTransitionFrequency`
- `Burnett.Microlocal.OverlapKernel.exists_frozenChartFrequency_norm_bounds`
- `Burnett.Microlocal.OverlapKernel.contDiffOn_movingChartAngularSymbol`
- `Burnett.Microlocal.OverlapKernel.movingChartAngularSymbol_degreeZero`
- `Burnett.Microlocal.OverlapKernel.movingChartNormalizedSymbol_eq_fixedCore_add`
- `Burnett.Microlocal.OverlapKernel.contDiff_movingChartInfraredRemainder`
- `Burnett.Microlocal.Overlap.exists_compactFrequency_leftAction_strongZero`
- `Burnett.Microlocal.Overlap.exists_movingChartLowAction_strongZero`
- `Burnett.Microlocal.Overlap.tendsto_compactAngularAction_pairings_of_matrixDensity`
- `Burnett.Microlocal.Overlap.integral_transportHalfDensity_pairing`
- `Burnett.Microlocal.Overlap.transportedHalfDensitySchwartz_inner_toLp`
- `Burnett.Microlocal.Overlap.tendsto_transportedAngularPairings_of_matrixDensity`
- `Burnett.Microlocal.Overlap.exists_originalVolume_transportedAngularPairings_of_matrixDensity`
- `Burnett.Microlocal.Overlap.tendsto_targetSeparablePairings_of_sourceMatrixDensity`
- `Burnett.Microlocal.Overlap.exists_originalVolume_targetSeparablePairings_of_sourceMatrixDensity`

[Shared source bindings](moving-angular-density-pairings-source-bindings.json)
