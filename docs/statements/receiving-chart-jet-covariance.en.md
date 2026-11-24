# Original jet covariance and classical pairings in arbitrary receiving charts

Take one strict refinement of any original vacuum subsequence. The original volume half-density gradients converge weakly to zero in every compatible chart along the original sequence. The change of coordinates acts on all three indices. The second derivatives of the coordinate transformation multiply the metric perturbation and give a remainder that converges uniformly to zero on a compact window. The receiving gradient differs by a strongly vanishing L² term from a finite sum of the original chart gradients transported as half-densities.

Each classical pairing uses the same bounded L² operator, two independent smooth cutoffs, and its actual local left Fourier representation. Near-field and far-field kernel estimates give a strongly vanishing remainder for a fixed change of coordinates. A finite square partition combines overlap limits into the limit on the whole compact receiving window. The principal symbol is evaluated at the actual auxiliary unit covector. Real symbols give the inner-product order in `eq:sigma`, and complex symbols use conjugate linearity in the second slot.

Insert the actual auxiliary unit covector into both derivative slots of the amplitude covariance to define the six-linear jet covariance. Its ordered matrix in each real tangent basis is positive semidefinite almost everywhere. Covector insertion is an isometry for the auxiliary Gram inner product, and its Gram adjoint is a left inverse. Multiplication by the corresponding Gram matrix gives the covariance operator. On each compact chart window, all ordered entries of the jet covariance operator are integrable against the same control and define one matrix-valued measure.

The same strict refinement, global amplitude, and physical measure given by its null contraction satisfy the original classical pairings, the implemented Einstein moments, zero scalar curvature, and fixed-chart naturality. Independent comparison with the frozen T02 statement covers the classical operators with the formalized local representation. The full geometric test class, global bundle-valued measure representation, general first-order localization, acceptance of the quadratic theorem, and transport remain open. Author confirmation for the new support results is pending.

## Registered supporting theorems

- `Burnett.Microlocal.AtlasVolumeGradient.fixedVolumeGradient_weak_and_uniform_L2`
- `Burnett.Microlocal.AtlasOverlapKernel.overlap_halfDensityKernel_changeVariables`
- `Burnett.Microlocal.AtlasOverlapKernel.frozenChartFrequency_inverse_adjoint`
- `Burnett.Microlocal.AtlasOverlapKernel.overlap_partialAngularFourier_difference_sum_actions`
- `Burnett.Microlocal.AtlasOverlapKernel.exists_localizedNormalizedAngularDifference_strongZero`
- `Burnett.Microlocal.AtlasOverlapKernel.tendsto_receivingSeparablePairing_sub_sourceAngularAction`
- `Burnett.Microlocal.Overlap.tendsto_originalVolume_receivingClassicalPairing_on_compact`
- `Burnett.Microlocal.Overlap.exists_receiving_square_partition_on_sameSubsequence`
- `Burnett.Microlocal.Overlap.tendsto_receivingClassicalPairing_of_originalPlateauLimits`
- `Burnett.Microlocal.Overlap.atlasChartUnitCovector_change`
- `Burnett.Microlocal.Overlap.atlasAngularPhaseCode_measurable`
- `Burnett.Microlocal.Overlap.atlasOrderedJetEntry_change`
- `Burnett.Microlocal.Overlap.original_receivingAtlasJetEntry_angularMeasure_on_compact`
- `Burnett.Microlocal.Overlap.original_globalAmplitude_integrable_receivingAtlasJet_on_compact`
- `Burnett.Microlocal.AtlasVolumeGradient.fixedPerturbation_jet_change`
- `Burnett.Microlocal.AtlasVolumeGradient.bothCharts_rawJet_error_uniform`
- `Burnett.Microlocal.AtlasOverlapKernel.integral_transportHalfDensity_pairing`
- `Burnett.Microlocal.AtlasVolumeGradient.exists_receivingSourceCutoffs_of_originalVolume`
- `Burnett.Microlocal.Overlap.jetAmplitudeComponents_insertJetCovectors`
- `Burnett.Microlocal.Overlap.jetAmplitudeComponents_posSemidef`
- `Burnett.Microlocal.Overlap.atlasOrderedJetEntry_eq_intrinsicJetComponents`
- `Burnett.Microlocal.Overlap.original_intrinsicJetAmplitude_positive_and_integrable`
- `Burnett.Microlocal.Overlap.unitCosphereCovectorGram_norm`
- `Burnett.Microlocal.Overlap.unitCosphere_gradientEmbedding_gram`
- `Burnett.Microlocal.Overlap.unitCosphere_gradientEmbedding_adjoint_mul`
- `Burnett.Microlocal.Overlap.unitCosphere_jetCovariance_operator`
- `Burnett.Microlocal.Overlap.tendsto_receivingPaperPairing_of_weight`
- `Burnett.Microlocal.Overlap.atlasAngularPhaseCode_symbol_eq_unitCovector`
- `Burnett.Microlocal.Overlap.tendsto_originalVolume_receivingClassicalPairing_globalAmplitude`
- `Burnett.Microlocal.Overlap.hasOriginalReceivingPaperPairings_of_intrinsicAmplitude`
- `Burnett.Microlocal.Overlap.exists_originalVacuum_intrinsicAmplitude_receivingPairings_and_EinsteinMoments`
- `Burnett.Microlocal.Overlap.atlasJetCovarianceOperator_in_fiber`
- `Burnett.Microlocal.Overlap.integrable_atlasJetCovarianceOperator_on_compact`
- `Burnett.Microlocal.Overlap.original_atlasJetCovarianceOperator_matrixMeasure_on_compact`

[Shared source bindings](receiving-chart-jet-covariance-source-bindings.json)
