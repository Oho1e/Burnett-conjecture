# 真实协变梯度上的一阶定位与内蕴对称 jet 测度

本批对应锁定论文第 390–428 行和第 467–479 行。它沿用原协方差 \(A\)、原控制测度和同一个严格子序列。内蕴 jet 的底层纤维是 \(T_xM\) 上以复数为值的实三线性形式，末两槽对称。每个辅助单位余向量上的算子作用在这个真实纤维中。算子矩阵用辅助度量升起输入指标，图重叠处按实际张量基变换作相似变换。

点态正性用真实 jet Gram 矩阵 \(H\) 表达。若 \(O\) 是协方差算子，\(HO\) 半正定，且 \(O^*H=HO\)。末两槽的对称投影保留协方差算子的全部有序条目。每个紧图窗上，同一个内蕴密度给出可数可加的矩阵值测度，实迹在所有 Borel 集上等于限制后的原控制测度。重叠图上用同一个控制测度积分实际变换系数。

论文中的实际 \(Dh_n\) 与局部坐标导数乘同一截断和背景体积半密度后，差在 \(L^2\) 中强趋于零。新的定位把固定一阶行在原局部 \(Dh_n\) 上的强 \(H^{-1}\) 零转成同一协方差的主符号核约束。对实际 Levi-Civita 旋度行，Lean 已从原序列的局部界证明了所需强收敛。协方差算子像的每个 jet 都是 \(\xi\otimes k\)，其中 \(k\) 对称并满足实际内蕴 Ricci 符号方程。Ricci 端使用已由真空方程建立的原振幅核。

对具有真实局部全符号的经典零阶算子，已证明如何由高频负一阶余项得到原配对极限，覆盖复主符号和同一个有限矩阵算子的总配对。分离位置与角变量的乘子可沿实际半密度在任意相容图的紧凸交叠窗口中传递。该换图给出逆伴随频率的主符号，并产生作用在整个 \(L^2\) 上的紧余项。一般联合位置与频率的符号及完整内蕴几何算子类仍需进一步核验。

全局装配沿用同一 \(A\) 和同一 \(\mu\)。它同时给出已有真实局部表示的经典测试在原 \(Dh_n\) 上的配对、对称 jet 测度、Ricci 核和物理收缩的 Einstein 矩。登记为论文二次定理的支持结果。论文级二次定理、基底边际推论和输运各按原验收范围继续推进。

- Burnett.Microlocal.Overlap.atlasCovectorGram_transition
- Burnett.Microlocal.Overlap.tendsto_originalVolume_receivingSeparablePairing
- Burnett.Microlocal.Overlap.ae_receivingJetOperator_kernel_of_scaled_ordered_rows
- Burnett.Microlocal.BesselLocalization.negativeEnergy_firstOrderRow_tendsto_zero_of_strongL2_replacement
- Burnett.Geometry.MaximalChart.fixedCovariantJet_intrinsic_components
- Burnett.Microlocal.BesselLocalization.bessel_firstOrderRow_cutoff_sub_tendsto_zero
- Burnett.Microlocal.Overlap.hasLocalClassicalRepresentation_of_fullSymbolPairing
- Burnett.Microlocal.Overlap.exists_compact_windowKernel_schur
- Burnett.Microlocal.Overlap.atlasJetGram_transition
- Burnett.Microlocal.Overlap.atlasJetCovarianceOperator_change
- Burnett.Microlocal.Overlap.original_receiving_separableRow_kernel
- Burnett.Microlocal.AtlasVolumeGradient.fixedVolumeCovariantGradientSchwartz_intrinsic
- Burnett.Microlocal.AtlasVolumeGradient.fixedVolumeCovariantGradient_sub_partial_tendsto_zero
- Burnett.Microlocal.Overlap.hasLocalClassicalRepresentation_of_leftCutoff_fullSymbolPairing
- Burnett.Microlocal.Overlap.exists_classicalFullSymbolOperator
- Burnett.Microlocal.Overlap.exists_infraredAngularPrincipalOperator
- Burnett.Microlocal.AtlasOverlapKernel.exists_compact_localizedNormalizedAngularDifference
- Burnett.Microlocal.Overlap.original_atlasJetCovarianceOperator_matrixMeasure_overlap
- Burnett.Microlocal.Overlap.fixedVolumeRowPrincipal_tendsto_zero_of_negativeEnergy
- Burnett.Microlocal.Overlap.receivingPrincipalRow_eq_firstOrderSymbol
- Burnett.Microlocal.Overlap.ae_original_atlasJetCovarianceOperator_gramPositive_unitTrace
- Burnett.Microlocal.Overlap.intrinsicJetCovarianceEndomorphism_coordinates
- Burnett.Microlocal.Overlap.hasOriginalReceivingCovariantPaperPairings_of_intrinsicAmplitude
- Burnett.Microlocal.Overlap.tendsto_originalVolume_receivingLocalFullPairing_of_puncturedPrincipal
- Burnett.Microlocal.AtlasOverlapKernel.exists_classical_transportedSeparableOperator_on_compactInterior
- Burnett.Microlocal.Overlap.original_receiving_firstOrderSystem_kernel_of_negativeEnergy
- Burnett.Microlocal.Overlap.original_atlasJetCovarianceOperator_matrixMeasure_trace
- Burnett.Microlocal.Overlap.ae_original_intrinsicJetCovarianceEndomorphism_mem_symmetric
- Burnett.Microlocal.Overlap.intrinsicJetCovarianceEndomorphism_range_gradientRicci
- Burnett.Microlocal.Overlap.tendsto_originalVolume_receivingClassicalFullMatrixPairing
- Burnett.Microlocal.Overlap.original_receiving_covariant_firstOrderSystem_kernel_of_negativeEnergy
- Burnett.Microlocal.Overlap.intrinsicSymmetricJetCovariance_extension
- Burnett.Microlocal.Overlap.original_hasIntrinsicSymmetricJetMeasure
- Burnett.Microlocal.Overlap.original_atlasSymmetricJetEntries_overlap
- Burnett.Microlocal.Overlap.receivingCurlSymbol_eq
- Burnett.Microlocal.Overlap.exists_originalVacuum_symmetricJetMeasure_covariantPairings_and_EinsteinMoments
- Burnett.Microlocal.Overlap.receivingGeometricCurlRow_apply
- Burnett.Microlocal.Overlap.fixedVolumeGeometricCurl_negativeEnergy_tendsto_zero
- Burnett.Microlocal.Overlap.original_receiving_geometricCurl_kernel

[源绑定](symmetric-jet-localization-source-bindings.json)
