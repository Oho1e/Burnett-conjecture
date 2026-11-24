# 独立截断下的重叠域矩阵测度

固定光滑非退化背景及局部一致收敛于该背景的光滑度量列，其一阶导数在每个紧集上有公共界。取两张首选坐标图中的紧窗口，各自选取光滑实截断 \(\chi_q,\chi_d\)。假设沿同一个严格子列，两图实际体积半密度加权的原始梯度都有矩阵测度表示。若重叠点位于两窗口内部且两截断在该点均非零，可在保留原图中心的两个小窗中构造互相搬运的公共截断。小窗截断各是原截断与一个光滑紧支撑因子的乘积，并在对应的紧平台上等于一。

同一图中，在嵌套窗口上把截断乘以实因子 \(\theta\) 时，有序分量测度按相空间包含映射对应，并乘上 \(\theta^2\)。这个重加权恒等式也允许插入有界可测测试。进一步细化严格子列后取得公共小窗的测度表示，并保留两图原窗给定的测度表示。再用小窗上搬运截断的换图等式比较两个原窗。

记 \(Q_0\) 为源紧平台、\(D_0=\Phi(Q_0)\) 为其目标图像，\(T\) 为实际重叠域圆相位变换。方向由 \(D\Phi^{-*}\xi\) 按圆范数归一化给出。对任意目标 Borel 集 \(S\)，令 \(S_d=S\cap\pi_d^{-1}(D_0)\)，令 \(S_q=\pi_q^{-1}(Q_0)\cap T^{-1}(S)\)，其中逆像取在真实图重叠上。对每对有序槽 \(i,j\)，有

$$
\int_{S_q} \chi_q(x)^{-2}\rho^q_{ij}(x,\xi)\,d\tau_q
=\int_{S_d} \chi_d(y)^{-2}\sum_{k,l}
\overline{w_{ik}(y)}w_{jl}(y)\rho^d_{kl}(y,\omega)\,d\tau_d.
$$

其中 \(\tau_q,\tau_d\) 和 \(\rho^q,\rho^d\) 是两份给定图内测度的迹与有序条目密度。\(w_{ik}\) 是在目标基点的反向像处取值的实际前向 Jacobian 三槽系数。重加权因子在对应平台上就是原截断的倒数。非零截断重叠域还有由小窗平台内部组成的可数覆盖。条目等式也给出相应复测度的推前等式。 [F05 切片](../formalization/slices.md#f05)

当光滑非退化背景 \(B\) 对称时，以

$$
\frac14 r^{\alpha\beta}\left(B^{ca}B^{db}-\frac12 B^{cd}B^{ab}\right)
$$

缩并两个有序槽 \(i=(\alpha,a,b)\)、\(j=(\beta,c,d)\)。实际辅助单位射线在两图中识别同一个零壳 \(B^{-1}(\xi,\xi)=0\)。将公共平台限制到该零壳后，目标图上任意有界 Borel 测试及其经圆相位换图拉回的源图测试，所得物理加权积分相等。这里的结论是同一对原图见证上的复积分等式。接续使用 Ricci 核约束证明正性，再完成全局拼接和二次定理的见证构造。 [F07 切片](../formalization/slices.md#f07)

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

[共同源码对应](independent-cutoff-matrix-measures-source-bindings.json)
