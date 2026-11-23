# 原始度量梯度的局部正半定矩阵测度

锁定原稿第 390–429 行的 F05 使用同一个子列构造微局部缺陷。本批证明了第 398–407 行所需的局部测度构造，测试对象是固定体积半密度加权的原始坐标梯度。

## 原始序列、截断和子列

设光滑度量序列 $g_n$ 局部一致收敛到光滑非退化背景 $B$，且其相对于辅助度量的协变梯度差有紧集上的一致本质有界估计，估计使用 $B$ 的体积测度。在预先指定的每张首选图中固定一个含于图像的坐标闭球 $K$，以及支撑落在 $K$ 内的实光滑截断 $\chi$。把导数方向和两个有序张量指标合成 $i=(\alpha,a,b)$。真实的 Lebesgue $L^2$ 输入为

$$
w_{n,i}=|\det B|^{1/4}\chi\,\partial_\alpha(g_n-B)_{ab}.
$$

对任给的可数图族和任意严格递增子列 $s$，存在同一个严格递增 $t$，使下面的表示对各图均沿 $s\circ t$ 成立。取 $s=\mathrm{id}$ 即可从原序列开始。

## 测度与全部有限可分配对

每图在 $K\times S^3$ 上得到正则有限正压缩测度族。矩阵条目由极化给出，每个 Borel 集上的矩阵均正半定。所有条目绝对连续于同一个有限迹测度 $\tau$，其 Radon–Nikodym 密度矩阵 $J$ 在 $\tau$ 几乎处处正半定且迹为一。

对于任意有限和 $T=\sum_m a_m(x)b_m(D)$，允许复值的 $a_m$ 有界连续，$b_m$ 有界、离零光滑并在正伸缩下零次齐次。同一 $s\circ t$ 对所有这些测试及全部 $64\times64$ 个有序配对给出

$$
\lim_{n\to\infty}\langle w_{s(t(n)),i},T w_{s(t(n)),j}\rangle_{L^2}
= \int_{K\times S^3}\bigl(\sum_m a_m(x)b_m(\omega)\bigr)J_{ij}(x,\omega)\,d\tau.
$$

Lean 的内积对第二槽线性。若下游按第 56 批方式把同一配对写成协方差的 $N_{ji}$，则取 $N=J^{\mathsf T}$。数值极限定理在同一进一步子列上把先前选出的有理角模式极限逐项识别为积分，保留各图在空间乘子之前选出的常数及细化前子列的收敛。积分识别要求空间乘子连续。

本批范围为上述局部可分测试。后续将在同一密度上施加坐标 curl 与真空 Ricci 核约束，取得两导数方向因子和度量振幅，再处理辅助余球面及跨图相容。

## 登记声明

- `Burnett.F05.OriginalCoordinateCurl.exists_originalGradient_sourceSchwartz_inputs`
- `Burnett.F05.ChartVolumeAmplitude.originalGradient_volumeWeightedL2_ae`
- `Burnett.Microlocal.CountableAuxiliaryCharts.exists_countable_originalVolume_rational_pairing_limits`
- `Burnett.Microlocal.CompactOrderedFunctional.exists_commonCompactMatrixFunctional_positive`
- `Burnett.Microlocal.CompactChartMatrixMeasure.exists_compactChartMatrixMeasure_of_localized_weak_zero`
- `Burnett.Microlocal.CompactChartDensity.exists_compactChartMatrixDensity_of_localized_weak_zero`
- `Burnett.Microlocal.FixedSubsequenceSeparableExtension.exists_compactChartMatrixDensity_allFiniteSmoothPairings`
- `Burnett.Microlocal.CountableAuxiliaryCharts.exists_countable_originalVolume_matrixDensities`
- `Burnett.Microlocal.CountableAuxiliaryCharts.exists_originalVolume_measures_realizing_rational_limits`

[共同源码对应](original-gradient-matrix-measures-source-bindings.json)
