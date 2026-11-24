# Global Einstein moments and change of auxiliary unit section

[中文](global-cosphere-einstein-moments.zh-CN.md)

Let the original smooth vacuum metrics converge locally uniformly and satisfy the compact first-derivative bound in the auxiliary metric. Each strict subsequence has a further strict refinement. The resulting positive measure is defined on the actual auxiliary unit cosphere. It is regular, locally finite, finite over each compact base set, and carried by the zero set of the limit Hamiltonian. For every smooth compactly supported symmetric contravariant two-tensor, the Einstein tensor integral against the geometric volume equals the covector second moment of this same measure. Both integrands are integrable, and the scalar curvature vanishes pointwise. On any pair of compatible fixed smooth charts, the two pushforwards of the measure restricted to the overlap satisfy the cotangent change of coordinates.

A finite smooth decomposition of the compact support reduces the arbitrary tensor test to the represented chart Ricci component identities. Testing with the inverse limit metric times a scalar test gives a weak scalar curvature identity by concentration on the null shell. Smoothness and positivity of the geometric volume on nonempty open sets imply pointwise scalar-flatness. The resulting Einstein identity is integrated on the actual unit cosphere.

For two smooth auxiliary Riemannian metrics, the original amplitude, the local physical measure, and the inverse-cutoff-square normalization use the same subsequence and chart witnesses. The new physical measure is obtained by weighting the old measure by the square of the new covector norm and pushing it along positive radial normalization. Both the integrability and the signed integral of a compactly supported quadratic tensor test are preserved. The empty base case uses the zero measure.

These supporting declarations cover the global geometric conclusions of `thm:quadratic`, scalar measure chart naturality, and the change of physical measure under auxiliary normalization. The remaining construction assembles the full amplitude covariance on one control measure and verifies its original angular defect representation, its chart overlap laws, and its own transformation under change of auxiliary section.

## Registered Lean declarations

- `Burnett.Geometry.CotangentTests.exists_finite_smooth_cutoffs_on_compact`
- `Burnett.Geometry.CotangentTests.integral_eq_of_compact_base_local_tests`
- `Burnett.Geometry.ContravariantTensor.intrinsicTensorBase_eq_components`
- `Burnett.Geometry.ContravariantTensor.intrinsicTensorPhase_eq_components`
- `Burnett.Geometry.IntrinsicScalarEinstein.inverseMetricTensor_components`
- `Burnett.Geometry.IntrinsicScalarEinstein.intrinsicScalar_chart`
- `Burnett.Geometry.IntrinsicScalarEinstein.einsteinPair_eq_components`
- `Burnett.Geometry.FixedCotangentChart.fixedPhaseTransition_fixedChartPhase`
- `Burnett.Geometry.FixedCotangentChart.fixedChart_pushforwards`
- `Burnett.Geometry.UnitCosphere.fixedChartNaturality`
- `Burnett.Analysis.ChartTensorRicciTests.local_intrinsicTensor_moment_of_coordinateMoments`
- `Burnett.Microlocal.Overlap.hasRicciMoments_of_nonzero_chartMoments`
- `Burnett.Analysis.ScalarCurvatureFromMoments.scalarCurvature_eq_zero_of_null_RicciMoments`
- `Burnett.Analysis.ScalarCurvatureFromMoments.scalarFlat_and_EinsteinMoments_of_null_RicciMoments`
- `Burnett.Microlocal.Overlap.exists_originalVacuum_cosphereEinsteinMoments`
- `Burnett.Microlocal.Overlap.chartAuxiliaryRay_changeWeight_eq_ratio`
- `Burnett.Microlocal.Overlap.chartAuxiliaryNull_changeAuxiliary`
- `Burnett.Microlocal.Overlap.ae_original_chartPhysicalJetContraction_changeAuxiliary`
- `Burnett.Microlocal.Overlap.chartAuxiliaryRay_changeAuxiliary`
- `Burnett.Microlocal.Overlap.original_chartPhysicalJetMeasure_changeAuxiliary`
- `Burnett.Microlocal.Overlap.original_normalizedCotangentPhysicalMeasure_changeAuxiliary`
- `Burnett.Microlocal.Overlap.original_globalPhysicalMeasure_changeAuxiliary_of_chartLaws`
- `Burnett.Microlocal.Overlap.exists_originalVacuum_globalPhysicalMeasure_changeAuxiliary_sameWitnesses`
- `Burnett.Microlocal.Overlap.exists_originalVacuum_globalPhysicalMeasures_changeAuxiliary`
- `Burnett.Microlocal.Overlap.fromAmbient_changeAuxiliary`
- `Burnett.Microlocal.Overlap.cosphereTensorPhase_of_auxiliaryRescaling`
- `Burnett.Microlocal.Overlap.cosphereEinsteinMoments_of_auxiliaryRescaling`

[Shared source bindings](global-cosphere-einstein-moments-source-bindings.json)
