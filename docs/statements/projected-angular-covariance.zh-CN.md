# 固定投影的角向协方差与物理测度

[English](projected-angular-covariance.en.md)

本批对应锁定稿第 1636–1638 及 1703–1709 行。记 $\Pi$ 为原固定红外正则矩阵投影，$P(\xi)$ 为它在非零余向量上的齐次主符号，写在有序矩阵分量上。

给定一个光滑、共同紧支、分量 $L^2$ 一致有界且对光滑紧支函数弱趋零的实矩阵场序列。对固定的实值光滑紧支空间测试，若原序列的所有有序分量对已给出协方差 $N$ 的角向配对极限，则对同一序列施用实际 $\Pi$ 后，配对极限的矩阵为 $PNP^*$。角测试在非零频率上光滑并且零次齐次。证明将实际 Schwartz 投影的各分量认作 $L^2$ Fourier 乘子。两侧的固定低频差在这些配对中趋零，经过有限求和得到完整矩阵极限。

另给一个振幅矩阵 $A$，其像在原 Ricci 符号核中。对非零余向量，$PAP^*$ 在零锥外为零；在零锥上，对称振幅的投影像满足 Lorenz 极化。对给定的同一迹测度 $\tau$，若可测零锥壳上几乎处处满足背景对称、频率非零、振幅半正定及像的对称 Ricci 核条件，则 $A$ 和 $PAP^*$ 给出相等的完整物理测度。该测度先将 $\tau$ 限制到零锥壳，再用四分之一实物理收缩的非负部分加权。证明在加权之前建立实收缩所来自的复物理收缩恒等式。

$N$ 是分析配对的协方差，$A$ 是物理收缩所用的振幅。导数配对中携带的频率因子可从两槽投影中提出。原真空序列的共同见证提取、两个实际导数槽的识别和同一全局测度的跨图相容性属于后续接入。作者确认待记录。

- `Burnett.P01.regularizedComplexGaugeProjection_eq_principal`
- `Burnett.P01.principalGaugeProjection_eq_zero_off_null`
- `Burnett.P01.principalGaugeProjection_null_contracted`
- `Burnett.P01.principalGaugeProjection_preserves_hermitianPhysicalPairing`
- `Burnett.Microlocal.PhysicalDensity.physicalContraction_gram`
- `Burnett.P01.nullPhysicalMeasure_principalGaugeProjection_eq`
- `Burnett.P01.projectedCoordinateCovariance_eq_zero_off_null`
- `Burnett.P01.projectedCoordinateCovariance_null_contracted`
- `Burnett.P01.nullPhysicalMeasure_projectedAmplitudeCovariance_eq`
- `Burnett.P01.projectedDefectScalarPairing_sub_tendsto_zero`
- `Burnett.P01.gaugeProjectionComponent_toLp_eq_multiplier`
- `Burnett.P01.projectedDefectActualComponent_sub_tendsto_zero`
- `Burnett.P01.projectionFullSchwartz_defectPairing_tendsto`

[共同源码对应](projected-angular-covariance-source-bindings.json)
