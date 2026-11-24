# 原图上的正物理测度

固定原光滑真空度量列、其光滑 Lorentz 极限 \(B\) 和辅助度量 \(r\)。在每个实际切空间用一组基表达 \((-+++)\) 签名。由此得到对称性、非退化性，以及每张首选图中极限逆度量的 Lorentz 标架。这里使用逐点的基。

固定一个已有原图表示的严格子列及测度见证 \(\nu_q\)，记其迹为 \(\tau_q\)、辅助单位方向的振幅为 \(A_q\)，实际射线到余切丛的映射为 \(\iota_{r,q}\)。有序梯度条目的缩并等于

$$
  \frac14 \sum_{a,b,c,d}
     \left(B^{ac}B^{bd}-\frac12 B^{ab}B^{cd}\right)(A_q)_{ab,cd}.
$$

实际辅助单位余向量使两个导数槽的缩并等于一。在背景零壳上，结合正振幅的有限维 Gram 分解、对称像空间上的 Ricci 核约束与 Lorentz 物理二次型，可知上式相对于零壳上的原迹测度几乎处处为实且非负。原图缩并可积，因而限制原迹并按此加权给出有限正测度，其 Borel 集值由该密度积分确定。经 \(\iota_{r,q}\) 推前后，测度集中在实际辅助单位零余向量上。对可数图窗族，可在一个共同严格细化子列上同时得到这些局部测度。每张图的原配对和投影配对仍共用同一迹测度。 [F07 切片](../formalization/slices.md#f07)

在公共平台上限制两张原图的物理测度，各自乘原截断的倒数平方，所得有限测度满足实际圆相位换图律，而且推到余切丛上得到同一个测度。每个结论都使用给定子列和原测度见证。全局拼接、Ricci 与 Einstein 矩等式、标量曲率为零以及辅助截面的加权变换仍是二次定理的后续义务。

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

[共同源码对应](local-positive-physical-measures-source-bindings.json)
