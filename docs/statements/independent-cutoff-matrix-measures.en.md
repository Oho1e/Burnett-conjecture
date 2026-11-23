# Overlap matrix measures for independently chosen cutoffs

Fix a smooth nondegenerate background and smooth metrics that converge locally uniformly to it, with a common first-derivative bound on compact sets. In two preferred-chart windows choose smooth real cutoffs \(\chi_q,\chi_d\) independently. Suppose both half-density-weighted original gradient sequences have matrix measure representations along the same strict subsequence. At an overlap point in the interiors of both windows where both cutoffs are nonzero, one can construct two smaller windows with the same chart centers. The two smaller cutoffs are products of the given cutoffs with smooth compact factors, transform into one another, and equal one on corresponding compact plateaus.

On nested windows in one chart, multiplying the cutoff by a real factor \(\theta\) multiplies the ordered entry measure by \(\theta^2\), with the small window identified by its natural phase inclusion. The same law permits inserting bounded measurable tests. A further strict refinement provides representations on the common smaller windows and retains the two given large-window representations. The matching-cutoff identity on the smaller windows then compares the original entries in the independently chosen large windows.

Write \(Q_0\) for the compact source plateau, \(D_0=\Phi(Q_0)\) for its target image, and \(T\) for the actual overlap map on the round phase spaces. Its direction component is \(D\Phi^{-*}\xi\) normalized to round unit length. Put \(S_d=S\cap\pi_d^{-1}(D_0)\) and \(S_q=\pi_q^{-1}(Q_0)\cap T^{-1}(S)\), where the inverse image is taken on the actual chart overlap. For every target Borel set \(S\) and every ordered entry \(i,j\),

$$
\int_{S_q} \chi_q(x)^{-2}\rho^q_{ij}(x,\xi)\,d\tau_q
=\int_{S_d} \chi_d(y)^{-2}\sum_{k,l}
\overline{w_{ik}(y)}w_{jl}(y)\rho^d_{kl}(y,\omega)\,d\tau_d.
$$

Here \(\tau_q,\tau_d\) and \(\rho^q,\rho^d\) are the traces and ordered densities of the two given chart measures. Each \(w_{ik}\) is the actual three-slot forward Jacobian coefficient evaluated at the inverse image of the target basepoint. The factors are the reciprocal cutoffs on the respective plateaus. The construction admits a countable cover of the nonzero-cutoff overlap by smaller patch interiors. The entry identity also gives the pushforward equality of the corresponding complex measures. [F05 slice](../formalization/slices.en.md#f05)

For a smooth symmetric nondegenerate background \(B\), contract the two ordered entries \(i=(\alpha,a,b)\), \(j=(\beta,c,d)\) with

$$
\frac14 r^{\alpha\beta}\left(B^{ca}B^{db}-\frac12 B^{cd}B^{ab}\right).
$$

The actual auxiliary ray identifies the same shell \(B^{-1}(\xi,\xi)=0\) in both charts. Restricted to that shell on the common plateaus, the physical weighted integrals agree for every bounded Borel test composed with the round phase change on the source side. This equality concerns complex integrals and the same pair of original chart witnesses. The Ricci constraint is needed for the positivity step, followed by global gluing and the construction of the quadratic witness. [F07 slice](../formalization/slices.en.md#f07)

- `Burnett.Microlocal.OverlapWindows.exists_testFactor_of_tsupport_subset_nonzero`
- `Burnett.Microlocal.OverlapWindows.exists_commonCutoffPatch`
- `Burnett.Microlocal.OverlapWindows.exists_countable_commonCutoffPatches`
- `Burnett.Microlocal.OverlapWindows.CommonCutoffPatch.inputs_matching_cutoffs`
- `Burnett.Microlocal.OverlapWindows.CommonCutoffPatch.isCompact_targetPlateau`
- `Burnett.Microlocal.OverlapWindows.CommonCutoffPatch.targetPlateau_subset_interior_image`
- `Burnett.Microlocal.OverlapWindows.CommonCutoffPatch.continuous_sourcePhaseToOverlap`
- `Burnett.Microlocal.OverlapWindows.CommonCutoffPatch.roundChartWindowMap_inclusion`
- `Burnett.Microlocal.Overlap.originalGradient_volumeWeightedL2_of_cutoff_mul`
- `Burnett.Microlocal.Overlap.sameChart_cutoffMul_density_integral_eq`
- `Burnett.Microlocal.Overlap.continuous_sameChartBallInclusion`
- `Burnett.Microlocal.Overlap.measurableEmbedding_sameChartBallInclusion`
- `Burnett.Microlocal.Overlap.sameChart_weighted_setIntegral_eq_of_terms`
- `Burnett.Microlocal.Overlap.sameChart_cutoffMul_entryMeasure_preimage_eq`
- `Burnett.Microlocal.CountableAuxiliaryCharts.exists_common_refinement_originalVolume_pairDensities`
- `Burnett.Microlocal.Overlap.setIntegral_mul_eq_of_setIntegral_preimage_eq`
- `Burnett.Microlocal.Overlap.sameChart_cutoffMul_setIntegral_on_image`
- `Burnett.Microlocal.OverlapWindows.CommonCutoffPatch.sourceFactor_on_halfBall`
- `Burnett.Microlocal.OverlapWindows.CommonCutoffPatch.targetFactor_on_targetPlateau`
- `Burnett.Microlocal.Overlap.exists_commonPatch_ambientEntryMeasures`
- `Burnett.Microlocal.OverlapWindows.CommonCutoffPatch.measurableSet_targetPhasePlateau`
- `Burnett.Microlocal.OverlapWindows.CommonCutoffPatch.targetPhaseInclusion_image_preimage_inter_plateau`
- `Burnett.Microlocal.OverlapWindows.CommonCutoffPatch.sourcePhaseInclusion_image_preimage_targetPlateau`
- `Burnett.Microlocal.Overlap.commonPatch_normalized_ambientEntryMeasures`
- `Burnett.Microlocal.Overlap.entryMeasure_eq_trace_withDensity`
- `Burnett.Microlocal.Overlap.map_normalizedEntry_eq_target_of_borel`
- `Burnett.Microlocal.Overlap.original_commonPatch_normalized_roundJetMeasure`
- `Burnett.Microlocal.Overlap.normalizedEntry_weightedSetIntegral`
- `Burnett.Microlocal.Overlap.chartPhysicalJetWeight_contraction_change`
- `Burnett.Microlocal.Overlap.chartAuxiliaryNull_roundTransition`
- `Burnett.Microlocal.Overlap.normalizedPhysicalPlateauTest`
- `Burnett.Microlocal.Overlap.original_commonPatch_physicalPlateauTest`

[Shared source bindings](independent-cutoff-matrix-measures-source-bindings.json)
