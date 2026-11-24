# 全局 Einstein 矩与辅助余球面换截面

[English](global-cosphere-einstein-moments.en.md)

对满足局部一致收敛和紧集一阶辅助导数界的原光滑真空度量列，从任意严格子列再作一次严格细化。所得正测度位于实际辅助单位余球丛，正则、局部有限、在任意紧底集上有限，并集中在极限度量的 Hamiltonian 零壳。对每个紧支撑光滑对称反变二阶张量，Einstein 张量的几何体积积分等于同一测度上的二阶余向量矩，两侧均可积。极限度量的标量曲率逐点为零。对任意相容固定光滑图，重叠域上的两个坐标测度由同一测度推前，满足标准余切换图律。

证明从已表示图的 Ricci 分量等式出发。紧支集上的有限光滑分解把任意张量测试送回这些图。随后使用逆极限度量乘以标量测试，借零壳集中性得标量曲率的弱等式，再以光滑性与几何体积在非空开集上的正性得逐点消失。所得 Einstein 矩直接写在实际余球丛的测度上。

给定两个光滑辅助黎曼度量，原幅度、局部物理测度及倒截断平方归一化沿用同一子列和逐图见证。把每个旧单位余向量除以它的新范数，并在推前前按该范数的平方加权，得到新余球面上的物理测度。任意紧支张量的二次矩积分及可积性在这一换截面下保持。空底流形对应零测度。

本文登记支持声明，覆盖 `thm:quadratic` 的全局几何结论、标量测度换图及物理测度换截面。继续在同一共同控制测度上装配完整振幅协方差，证明其原始角向缺陷表示、跨图相容性及振幅协方差本身的辅助换截面。

## 登记的 Lean 声明

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

[共同源码对应](global-cosphere-einstein-moments-source-bindings.json)
