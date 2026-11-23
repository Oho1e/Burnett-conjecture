# 原始度量梯度的 curl 分解与投影配对

锁定原稿第 412–428 行先使用坐标旋度约束，再把缺陷分解为两个导数方向因子和度量振幅。本批将这一步接到第 57 批的局部矩阵测度，并给出第 1703–1709 行所用投影在首选图中的混合导数配对。

固定光滑、对称、非退化背景 $B$ 和光滑对称序列 $g_n$。假设序列局部一致收敛到 $B$，以及相对于辅助度量的协变梯度差在每个紧集上有一致本质有界估计。每张指定首选图使用一个坐标闭球 $K$ 和支撑在其中的实光滑截断 $\chi$。原始体积加权导数的配对数据为 $J$ 与其有限迹测度 $\tau$，载体为 $K\times S^3$。

## 同一密度上的旋度约束

设 $N=J^{\mathsf T}$，其中 Lean 的内积对第二槽是复线性的。对圆单位余向量 $\xi$，令 $E_\xi k=\xi\otimes k$。实际原始梯度上角向 Bessel curl 行的强零极限给出 $\operatorname{curl}(\xi)N=0$，原度量分量的对称性也传给 $N$。沿同一 $\tau$ 几乎处处有

$$
A=E_\xi^* N E_\xi\succeq0,\qquad N=E_\xi A E_\xi^*,\qquad
J_{(\alpha,i),(\beta,j)}=\xi_\alpha\xi_\beta A_{ji}.
$$

因此原有全部有限可分配对都能用这两个因子与正半定振幅表示。加权振幅条目由原迹密度逐项给出可积性。

## 实际投影场的配对

对任意指定的可数图族和任意严格子列 $s$，存在同一个严格细化 $t$，每张图上的原始配对和投影配对共用 $s\circ t$ 以及该图同一个 $\tau$。设 $z_n=\chi(g_{s(t(n))}-B)$ 为实际坐标分量的零延拓。选一个实光滑紧支乘子 $d$，在 $\operatorname{tsupp}\chi$ 上等于背景体积半密度，并使用同一个固定投影 $\Pi$ 及 $P(\xi)$。

取实光滑紧支空间符号 $a$ 和有界、离零光滑且在正伸缩下零次齐次的角符号 $m$。对加权投影导数 $d\,\partial_\alpha(\Pi z_n)_i$ 与 $d\,\partial_\beta(\Pi z_n)_j$，左槽在前的复内积趋于

$$
\int_{K\times S^3} a(x)m(\xi)\,\xi_\alpha\xi_\beta
   (P(\xi)A(x,\xi)P(\xi)^*)_{ji}\,d\tau.
$$

这些声明给出首选图圆余球面上的混合配对。实际真空 Ricci 核约束、辅助度量余球面的变换与跨图物理角测度识别仍待接续。

## 登记声明

- `Burnett.Microlocal.RowKernelDensity.rowPrincipal_density_kernel_of_strong_zero`
- `Burnett.Microlocal.CurlDensity.positive_factorCovariance_of_curl_compression`
- `Burnett.Microlocal.FixedChartGeometricDensity.ae_chartPhysicalCovariance_symmetry_of_same_pairings`
- `Burnett.F05.ActualCoordinateCurlDensity.ae_originalVolume_curlRows_same_density`
- `Burnett.F05.ActualCoordinateCurlDensity.ae_originalVolume_round_covariance_factor`
- `Burnett.F05.ActualCoordinateCurlDensity.originalVolume_pairing_tendsto_roundAmplitude`
- `Burnett.F05.ActualCoordinateCurlDensity.originalVolume_round_mixedPairing_witness`
- `Burnett.P01.representsVolumeProjectedPairings_of_matrixDensity`
- `Burnett.P01.exists_countable_originalVolume_projected_mixedPairings`

[共同源码对应](original-volume-curl-amplitudes-source-bindings.json)
