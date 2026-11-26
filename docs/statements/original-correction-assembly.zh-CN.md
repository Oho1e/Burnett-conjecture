# 原规范修正与远角修正的装配

本批形式化论文 V08、V11、C02–C04 的支持引理。两项校正使用同一个原投影场、同一组空间截断及同一个子列。共同宽屏在后选薄屏前固定。固定正补丁尺度和薄屏后，角展开及上频率截断已在两个实际 Fourier 配对中按原顺序移除。

原投影补丁族同时提供薄屏三次替换、薄屏梯度差和归一化相位梯度的估计。原规范与物理远角修正都消费该补丁族所用的投影源。固定尺度下，对每个补丁分别取两项 Fourier 积分的绝对值再求和，在同一子列的尾部得到与尺度成正比的界和任意正误差。C04 的固定尺度极限使用相同的补丁与 Fourier 权重，把两项修正各以因子 3 加入残差上界。

联合 Lean 核验覆盖 24 条声明，公理使用限于 `propext`、`Classical.choice`、`Quot.sound`。源码与原文范围见 [绑定清单](original-correction-assembly-source-bindings.json)。`thm:variational-transport` 仍需接入原变分残差的极限、实际三次局部化和冻结、近角和相位控制。作者的语义确认待记录。

| 论文切片 | Lean 声明 |
| --- | --- |
| `V08` | `Burnett.V11.originalGaugeTestedOperator_eq_orderedEntries` |
| `V11` | `Burnett.V10.OriginalGaugeCompatibility.exists_actualFar_cutoff_recovery` |
| `V11` | `Burnett.V11.exists_actualGauge_cutoff_recovery` |
| `V11` | `Burnett.V11.originalPatchSource_fullIdentity` |
| `V11` | `Burnett.V11.exists_actualCorrections_consume_sameProjectedPatch` |
| `V11` | `Burnett.V11.exists_intrinsicCorrection_jets_of_jointWideScreen` |
| `C02` | `Burnett.C02.exists_originalWideL3_cubicWindow_withJointScreen` |
| `C02` | `Burnett.C02.exists_uniform_originalThinCubicC03Replacement_withFixedJointScreen` |
| `C02` | `Burnett.V11.exists_uniform_originalFrequencyTest_jets` |
| `C02` | `Burnett.C02.exists_uniform_originalThinCubicC03Replacement_withFixedJointScreen_andGradientPair` |
| `C02` | `Burnett.C02.exists_originalThinCubicReceivingFamily_withFixedJointScreen_andGradientPair` |
| `C03` | `Burnett.V11.exists_receivingPatchFields_of_originalCutoffs` |
| `C03` | `Burnett.V11.originalCorrectionFourierSum_of_sharedBudget` |
| `C03` | `Burnett.V11.exists_originalCorrectionPatchFourierTail` |
| `C04` | `Burnett.C04.fixed_patch_summed_residual_bound_of_actualCorrectionSum` |
