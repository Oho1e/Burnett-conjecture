# 相互搬运截断下的重叠域矩阵测度

取同一实际原度量序列，沿用相对于光滑辅助度量的局部一致收敛与紧集上的一阶界。设 $y=\Phi(x)$ 是首选坐标图的变换。源图闭球位于换图开域内，其像包含在目标图闭球内。两个截断在整个换图开域中按 $\eta(\Phi(x))=\chi(x)$ 对应，目标截断的支撑也包含在源闭球的像内。沿同一个给定的严格子列，两组实际体积加权梯度均已有各自的图内矩阵测度表示。

源槽 $i$ 的搬运与目标图原梯度槽的有限加权和之差在 $L^2$ 中强趋于零。系数 $w_{ik}(y)$ 在源闭球的像上等于实际前向 Jacobian 在反向像点处的三个协变指标乘积。系数的紧支撑延拓可用同一个目标图光滑截断。两个配对槽分别插入这些系数，右槽乘法交换子和固定低频差在极限中消失。

记 $T(x,\xi)=(\Phi(x),D\Phi(x)^{-*}\xi/\lVert D\Phi(x)^{-*}\xi\rVert)$ 为闭球窗口间的圆余球坐标映射。设 $\tau_q,\tau_d$ 为两组矩阵测度的迹，$\rho^q,\rho^d$ 为对应的有序分量密度。对支撑在源闭球图像中的光滑基点权 $\zeta$ 及目标图中的任意 Borel 集 $S$，得到

$$
\int_{T^{-1}(S)} \zeta(\Phi(x))\,\rho^q_{ij}\,d\tau_q
=\int_S \zeta(y)\sum_{k,l}\overline{w_{ik}(y)}\,w_{jl}(y)\,\rho^d_{kl}\,d\tau_d.
$$

若 $S$ 的基点位于源闭球图像内部的任意紧子集，取等于一的局部权即可得到该集合上的无权等式。所有积分使用已经给定的同一子列及两份矩阵测度；结论不依赖系数在支撑以外的延拓取值。下一步须把不同的独立局部截断接到共同搬运截断，再在实际辅助余球丛上拼接。 [F05 切片](../formalization/slices.md#f05)

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

[共同源码对应](matching-cutoff-matrix-measures-source-bindings.json)
