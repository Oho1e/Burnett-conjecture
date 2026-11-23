# Gradient transformation and Fourier comparison on preferred-chart overlaps

Lines 395–428 of the locked paper use local order-zero tests on the same original metric sequence. Line 428 calls for the coordinate transformation of tensor components and test operators. This batch proves the transformation of the covariant gradient and its volume half-density, and proves strong vanishing of the Fourier conjugation error for the fixed infrared normalization on an actual preferred-chart overlap.

Fix a smooth auxiliary Riemannian metric $r$, a smooth nondegenerate background $B$, and a smooth sequence $g_n$. Use the original local uniform convergence in the $r$ norm and the uniform essential bound for the covariant gradient difference on compacts. Let $\Phi$ be a preferred-chart transition. Fix a closed coordinate ball $K$ inside its open source and a smooth real cutoff $\chi$ supported in $K$. The original volume-weighted gradient multiplies each ordered coordinate partial derivative by $\chi$ and by the half-density of the background volume.

## Coordinate transformation of gradients and covectors

With the same cutoff and volume half-density, the componentwise difference between $\partial(g_n-B)$ and $D^r(g_n-B)$ tends strongly to zero in complex $L^2(dx)$. Transport the source cutoff to the target chart. The source covariant gradient is the pullback of the target gradient with $D\Phi$ in each of the three covariant slots and the half-density factor $w(x)=\sqrt{|\det D\Phi(x)|}$.

The coordinate column of the same covector transforms from source to target by $D\Phi(x)^{-\mathsf T}$. Renormalizing the transformed round direction gives a homeomorphism of the overlapping round phase spaces and obeys the three-chart composition law. The auxiliary unit covectors from either chart agree in the actual cotangent bundle. Given the corresponding congruence of ordered jet covariances, the auxiliary unit amplitudes obey congruence by the two-tensor coordinate matrix.

## Fourier comparison on the original gradient sequence

Let $m$ be bounded, smooth off zero, and homogeneous of degree zero under positive dilations. Use the fixed radial cutoff $\chi_0$ to form $m_{\mathrm{hi}}=(1-\chi_0)m$. Transport each localized original gradient component $f_n$ to the target by $g_n^{\mathrm{tr}}(\Phi(x))=f_n(x)/w(x)$ on $\Phi(K)$ and extend it by zero. This transport has a smooth compactly supported representative on the whole coordinate space.

On $K$, compare the half-density pullback of the action of $m_{\mathrm{hi}}$ on $g_n^{\mathrm{tr}}$ with the source action of the frozen symbol $m_{\mathrm{hi}}((D\Phi(x)^*)^{-1}\xi)$. The finite-cutoff difference equals the sum of the actual half-density kernel minus the frozen linear kernel on each shell. The difference on shell $j$ has the envelope

$$
\frac{C\,2^{3j}}{(1+b\,2^j|x-y|)^5},\qquad b>0,
$$

and the four-dimensional Schur integral gains $2^{-j}$. After removing the outer frequency cutoff the difference tends strongly to zero in $L^2(dx)$ along the full original gradient sequence on the source chart.

For an integrably bounded family of separated symbols, the parameter integration and the pairing limit commute on the same chart trace. The moving frozen angular symbol still needs to be realized by this parameter representation. Local defect covariance and cutoff restrictions must then be identified on overlaps for global gluing.

## Registered declarations

- `Burnett.Geometry.UnitNullCompactness.cotangentTransitionMatrix_eq_inv_transpose`
- `Burnett.Geometry.UnitNullCompactness.symbolNorm_cotangentTransitionMatrix`
- `Burnett.F05.OverlapCovectors.continuous_roundOverlapTransition`
- `Burnett.F05.OverlapCovectors.roundOverlapTransition_comp`
- `Burnett.F05.OverlapCovectors.chartAuxiliaryRay_roundOverlapTransition`
- `Burnett.F05.OverlapCovectors.auxiliaryAmplitudeCovariance_roundOverlapTransition`
- `Burnett.F05.OverlapCovariantGradient.originalGradient_sub_covariantGradient_tendsto_zero`
- `Burnett.F05.OverlapCovariantGradient.exists_originalCovariantGradient_overlap_inputs`
- `Burnett.Microlocal.OverlapKernel.transition_taylor_remainder`
- `Burnett.Microlocal.OverlapKernel.overlap_halfDensityKernel_changeVariables`
- `Burnett.Microlocal.OverlapKernel.frozenChartFrequency_inverse_adjoint`
- `Burnett.Microlocal.OverlapKernel.overlap_frozen_shellKernel_symbol`
- `Burnett.Microlocal.OverlapKernel.overlap_shellKernel_uniform_envelope`
- `Burnett.Microlocal.Overlap.overlapKernel_action_norm_le`
- `Burnett.Microlocal.Overlap.boundedKernel_action_tendsto_zero`
- `Burnett.Microlocal.Overlap.exists_actualOverlapShell_actions_tendsto_zero`
- `Burnett.Microlocal.OverlapKernel.overlap_partialAngularFourier_difference_sum_actions`
- `Burnett.Microlocal.Overlap.exists_localizedPartialAngularDifference_limit`
- `Burnett.Microlocal.Overlap.tendsto_inverseFourier_partialAngular_comp`
- `Burnett.Microlocal.OverlapKernel.transportedHalfDensity_smooth_compact_support`
- `Burnett.Microlocal.Overlap.exists_originalVolume_weakL2_representatives`
- `Burnett.Microlocal.Overlap.exists_originalVolume_overlap_fourierDifference_limit`
- `Burnett.Microlocal.Overlap.exists_originalVolume_overlap_normalizedFourierDifference_zero`
- `Burnett.Microlocal.Overlap.tendsto_integrated_separablePairings_of_matrixDensity`

[Shared source bindings](overlap-fourier-conjugation-source-bindings.json)
