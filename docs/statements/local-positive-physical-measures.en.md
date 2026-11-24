# Positive physical measures on original charts

Fix the original smooth vacuum sequence, its smooth Lorentzian limit \(B\), and the auxiliary metric \(r\). The \((-+++)\) signature is expressed by a basis in each actual tangent fiber. It yields symmetry, nondegeneracy, and a Lorentz frame for the inverse limit metric in each preferred chart. The construction uses pointwise bases.

Fix a represented strict subsequence and its original chart witness \(\nu_q\). Denote its trace by \(\tau_q\), its auxiliary-unit amplitude by \(A_q\), and the actual radial map into the cotangent bundle by \(\iota_{r,q}\). The ordered jet density contracts to

$$
  \frac14 \sum_{a,b,c,d}
     \left(B^{ac}B^{bd}-\frac12 B^{ab}B^{cd}\right)(A_q)_{ab,cd}.
$$

The derivative slots contract to one at the actual auxiliary unit covector. On the background null shell the finite-dimensional Gram decomposition of the positive amplitude, its symmetric range in the Ricci kernel, and the Lorentz physical form give a nonnegative real value almost everywhere for \(\tau_q\) restricted to that shell. The chart contraction is integrable. Restricting and weighting the original trace gives a finite positive measure with the displayed density on Borel sets. Its pushforward by \(\iota_{r,q}\) is concentrated on the actual unit null covectors. The same strict refinement provides these local measures for a countable family of chart windows, using each chart's common trace for its original and projected pairings. [F07 slice](../formalization/slices.en.md#f07)

On a common plateau restrict each chart's physical measure and multiply by the reciprocal square of its own original cutoff. The resulting finite measures obey the actual round phase change and give equal measures after pushforward to the cotangent bundle. All statements retain the represented subsequence and the original witnesses. Global gluing, the Ricci and Einstein moment identities, scalar-flatness, and the weighted change of auxiliary section are subsequent parts of the quadratic theorem.

- `Burnett.Geometry.ManifoldBilinear.HasLorentzSignature.isSymmetric`
- `Burnett.Geometry.ManifoldBilinear.HasLorentzSignature.isNondegenerate`
- `Burnett.Geometry.ManifoldBilinear.chartInverse_hasLorentzFrame`
- `Burnett.Microlocal.Overlap.orderedPhysicalJetWeight_factored`
- `Burnett.Microlocal.Overlap.physicalContraction_of_null_amplitude`
- `Burnett.Microlocal.Overlap.chartAuxiliaryNull_iff_symbolNorm_eq_zero`
- `Burnett.Microlocal.Overlap.chartPhysicalJetWeight_contraction_eq_auxiliaryAmplitude`
- `Burnett.Microlocal.Overlap.ae_chartPhysicalJetWeight_contraction_nonneg_real`
- `Burnett.Microlocal.Overlap.integrable_chartPhysicalJetContraction`
- `Burnett.Microlocal.Overlap.isFiniteMeasure_chartPhysicalJetMeasure`
- `Burnett.Microlocal.Overlap.isFiniteMeasure_cotangentPhysicalJetMeasure`
- `Burnett.Microlocal.Overlap.cotangentPhysicalJetMeasure_compl_null`
- `Burnett.Microlocal.Overlap.ae_original_chartPhysicalJetContraction_nonneg_real`
- `Burnett.Microlocal.Overlap.original_cotangentPhysicalJetMeasure_apply_eq_setIntegral`
- `Burnett.Microlocal.Overlap.exists_countable_originalVolume_physicalJetMeasures`
- `Burnett.Microlocal.Overlap.sourcePhysicalPlateauMeasure_eq_invCutoff`
- `Burnett.Microlocal.Overlap.targetPhysicalPlateauMeasure_eq_invCutoff`
- `Burnett.Microlocal.Overlap.originalVacuum_commonPatch_physicalPlateauMeasure_map_eq`
- `Burnett.Microlocal.Overlap.originalVacuum_commonPatch_cotangentPhysicalMeasure_eq`

[Shared source bindings](local-positive-physical-measures-source-bindings.json)
