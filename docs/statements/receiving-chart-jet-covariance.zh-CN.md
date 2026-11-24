# 任意接收图中的原梯度协方差与经典算子配对

从任意原真空严格子列作一次严格细化。任意相容坐标图中的原体积半密度梯度沿原序列弱收敛到零。换图对三个指标同时作用，坐标变换的二阶导数乘以度量扰动给出在紧窗口上一致趋零的余项。接收图梯度与有限个原图梯度的真实半密度换图之和相差一个强零 L² 项。

经典算子配对使用同一个有界 L² 算子、两个独立的光滑截断和其实际局部左 Fourier 表示。近场和远场核估计给出固定换图后的强零余项。有限平方分割将原图重叠窗口上的极限合成整个接收图紧窗口的极限。主符号在实际辅助单位余向量上取值。实符号给出原文 `eq:sigma` 的内积顺序，复符号按第二槽的共轭线性处理。

在实际辅助单位余球上，将余向量插入原振幅协方差的两个导数槽，从而定义六线性的梯度协方差。其在任意实切基中的有序矩阵几乎处处半正定。余向量插入对辅助 Gram 内积等距，其 Gram 伴随是左逆。协方差乘以对应的 Gram 矩阵给出协方差算子。任意紧图窗上，梯度协方差算子的各个有序条目都在同一控制测度下可积，并构成一个矩阵值测度。

同一严格细化、同一全局振幅和同一零壳收缩的物理测度同时满足这里的原经典配对、已实现的 Einstein 矩、零标量曲率及固定图自然性。冻结 T02 题面的独立对接覆盖具有已形式化局部表示的经典算子。完整几何算子测试类、束值测度的全局表示、一般一阶定位、论文二次定理的整体验收及输运仍待完成。本批新支持结果的作者语义确认待记录。

## 登记的支持定理

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

[共同源码对应](receiving-chart-jet-covariance-source-bindings.json)
