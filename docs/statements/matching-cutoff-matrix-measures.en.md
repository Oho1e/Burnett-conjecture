# Overlap matrix measures with matching transported cutoffs

Fix the original metric sequence with the established local uniform convergence and compact first-derivative bound for the smooth auxiliary metric. Let $y=\Phi(x)$ be a preferred-chart transition. The source closed ball lies in the transition domain and its image lies in the target closed ball. The cutoffs satisfy $\eta(\Phi(x))=\chi(x)$ throughout the transition domain, and the target cutoff is supported in the image of the source ball. Both original volume-weighted gradient families have their chart matrix measures on the same given strict subsequence.

Each transported source slot differs strongly in $L^2$ from the finite combination of original target gradient slots. On the image window, the coefficient $w_{ik}(y)$ is the product of the three forward Jacobian entries at the reverse image point, one for each covariant slot. The coefficients admit compactly supported extensions using a single smooth target cutoff. The finite pairing expands with coefficients in both slots. The right-slot commutator and the fixed low-frequency difference vanish in the limit.

Let $T(x,\xi)=(\Phi(x),D\Phi(x)^{-*}\xi/\lVert D\Phi(x)^{-*}\xi\rVert)$ be the round phase map between the windows. Write $\tau_q,\tau_d$ for the chart traces and $\rho^q,\rho^d$ for their ordered entry densities. For a smooth base weight $\zeta$ supported in the image of the source ball and any target Borel set $S$, the result is

$$
\int_{T^{-1}(S)} \zeta(\Phi(x))\,\rho^q_{ij}\,d\tau_q
=\int_S \zeta(y)\sum_{k,l}\overline{w_{ik}(y)}\,w_{jl}(y)\,\rho^d_{kl}\,d\tau_d.
$$

When the base points of $S$ lie in a compact subset of the interior of the image window, a local weight equal to one gives the unweighted identity there. All integrals use the given common subsequence and the two given matrix measures. The result is independent of the coefficient extensions outside the weighted region. The remaining steps are compatibility with independently chosen cutoffs and gluing on the actual auxiliary cosphere bundle. [F05 slice](../formalization/slices.en.md#f05)

- `Burnett.Microlocal.Overlap.low_frequency_energy_tendsto_zero_of_supported_weakL2`
- `Burnett.Microlocal.Overlap.cutoffCommutator_tendsto_zero_of_supported_weakL2`
- `Burnett.Microlocal.Overlap.weightedSlot_sum_pairing_eq_add_error`
- `Burnett.Microlocal.Overlap.weightedSlot_sum_pairing_difference_tendsto_zero`
- `Burnett.Microlocal.Overlap.weightedTargetSlots_tendsto_density`
- `Burnett.Microlocal.Overlap.originalVolume_weightedTargetSlots_tendsto_density`
- `Burnett.F05.OverlapCovariantGradient.transportedHalfDensitySchwartz_norm_sub_toLp`
- `Burnett.F05.OverlapCovariantGradient.transportedOriginalVolumeGradient_sub_covariant_tendsto_zero`
- `Burnett.F05.OverlapCovariantGradient.overlapJetCoefficient_smoothOn`
- `Burnett.F05.OverlapCovariantGradient.exists_overlapJetCoefficient_tests`
- `Burnett.F05.OverlapCovariantGradient.transportedCovariantGradientSchwartz_eq_sum`
- `Burnett.F05.OverlapCovariantGradient.exists_originalGradient_overlap_transport`
- `Burnett.F05.OverlapCovariantGradient.transportedCovariantGradient_toLp_eq_sum`
- `Burnett.F05.OverlapCovariantGradient.transportedOriginalVolumeGradient_sub_target_sum_tendsto_zero`
- `Burnett.Microlocal.Overlap.exists_overlapBaseTest_pullback`
- `Burnett.Microlocal.Overlap.movingChartAngularSymbol_eq_roundOverlap`
- `Burnett.Microlocal.Overlap.movingChartAngularSymbol_eq_targetRoundTest`
- `Burnett.Microlocal.Overlap.tendsto_orderedPairing_sub_of_strong_replacement`
- `Burnett.Microlocal.Overlap.exists_matchingCutoff_overlap_densityPairings`
- `Burnett.Microlocal.Overlap.setIntegral_preimage_eq_of_continuous_weighted_tests`
- `Burnett.Microlocal.Overlap.setIntegral_preimage_eq_of_separable_weighted_tests`
- `Burnett.Microlocal.Overlap.setIntegral_preimage_eq_of_weightedChartTerms`
- `Burnett.Microlocal.Overlap.continuous_roundChartWindowMap`
- `Burnett.Microlocal.Overlap.weighted_setIntegral_roundChart_eq_of_overlap_tests`
- `Burnett.Microlocal.Overlap.exists_original_matchingCutoff_roundEntryMeasures`
- `Burnett.Microlocal.Overlap.setIntegral_roundChart_eq_on_compact_interior`
- `Burnett.Microlocal.Overlap.exists_original_matchingCutoff_compactInteriorEntryMeasures`

[Shared source bindings](matching-cutoff-matrix-measures-source-bindings.json)
