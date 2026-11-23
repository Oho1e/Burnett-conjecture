# 换图后的角向测试配对

本批推进 F05。在首选图的实际重叠域取一个紧闭球 \(K\)，记坐标变换为 \(y=\Phi(x)\)，频率变换为 \(L_x=(D\Phi(x)^*)^{-1}\)。源图中的基点测试 \(a\) 光滑且支撑于 \(K\)，并在 \(K\) 上满足 \(a=b\circ\Phi\)，其中 \(b\) 是目标图的有界测试。角符号 \(m\) 有界、沿正伸缩零次齐次，并在非零频率处光滑。

令 \(f_{n,i}\) 为体积半密度加权的实际原坐标梯度第 \(i\) 槽的 Schwartz 代表。记 \(T\) 为带逆 Jacobian 半密度的搬运，搬运后在 \(\Phi(K)\) 外取零。沿已由源图矩阵测度表示的同一子列 \(\sigma\)，设 \(\tau\) 为其迹测度，\(\rho_{ij}\) 为有序矩阵分量的密度。本批证明

\[
\lim_{n\to\infty}
\big\langle Tf_{\sigma(n),i},\, b\,[(1-\chi_0)m](D)\,Tf_{\sigma(n),j}\big\rangle_{L^2}
= \int_{K\times S^3} a(x)\,m(L_x\xi)\,\rho_{ij}(x,\xi)\,d\tau(x,\xi).
\]

这里 \(\chi_0\) 是固定低频核，Lean 的内积对第二槽线性。搬运保留实际 \(L^2\) 内积。对基点作 Fourier 变换得到的角系数，在非零频率处仍光滑并保持零次齐次。其一致可积包络允许在同一子列上对分离测试取积分。频率变换产生的紧低频贡献和上一批的共轭误差均在 \(L^2\) 中强趋于零。

后续需要把搬运后的槽与目标图实际梯度的三槽坐标系数相接，证明重叠域测度相容、局部截断相容和全局拼接。此处登记的是 F05 的支持结果，作者确认由工程范围清单记录。 [F05 切片](../formalization/slices.md#f05)

- `Burnett.Analysis.contDiffOn_integral_compact_parameter`
- `Burnett.Microlocal.Overlap.exists_uniform_baseDerivative_of_homogeneousAngular`
- `Burnett.Microlocal.Overlap.firstOrderAction_eq_integral_baseFourierModes`
- `Burnett.Microlocal.Overlap.firstOrderAction_pairing_eq_integral_separable_baseFourier`
- `Burnett.Microlocal.Overlap.baseFourierCoefficient_inverse`
- `Burnett.Microlocal.Overlap.exists_compactBaseAngular_leftFourier_pairing`
- `Burnett.Microlocal.Overlap.contDiffOn_baseFourierCoefficient`
- `Burnett.Microlocal.Overlap.degreeZero_baseFourierCoefficient`
- `Burnett.Microlocal.OverlapKernel.chartTransitionFrequency_eq_frozen`
- `Burnett.Microlocal.OverlapKernel.frozenChartFrequency_cotangentCoords`
- `Burnett.Microlocal.OverlapKernel.contDiffOn_chartTransitionFrequency`
- `Burnett.Microlocal.OverlapKernel.exists_frozenChartFrequency_norm_bounds`
- `Burnett.Microlocal.OverlapKernel.contDiffOn_movingChartAngularSymbol`
- `Burnett.Microlocal.OverlapKernel.movingChartAngularSymbol_degreeZero`
- `Burnett.Microlocal.OverlapKernel.movingChartNormalizedSymbol_eq_fixedCore_add`
- `Burnett.Microlocal.OverlapKernel.contDiff_movingChartInfraredRemainder`
- `Burnett.Microlocal.Overlap.exists_compactFrequency_leftAction_strongZero`
- `Burnett.Microlocal.Overlap.exists_movingChartLowAction_strongZero`
- `Burnett.Microlocal.Overlap.tendsto_compactAngularAction_pairings_of_matrixDensity`
- `Burnett.Microlocal.Overlap.integral_transportHalfDensity_pairing`
- `Burnett.Microlocal.Overlap.transportedHalfDensitySchwartz_inner_toLp`
- `Burnett.Microlocal.Overlap.tendsto_transportedAngularPairings_of_matrixDensity`
- `Burnett.Microlocal.Overlap.exists_originalVolume_transportedAngularPairings_of_matrixDensity`
- `Burnett.Microlocal.Overlap.tendsto_targetSeparablePairings_of_sourceMatrixDensity`
- `Burnett.Microlocal.Overlap.exists_originalVolume_targetSeparablePairings_of_sourceMatrixDensity`

[共同源码对应](moving-angular-density-pairings-source-bindings.json)
