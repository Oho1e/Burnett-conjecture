# 原体积梯度的真空 Ricci 核与辅助单位余球面振幅

锁定原稿第 412–428 行用一阶 Ricci 约束限制梯度缺陷振幅的像。第 1703–1709 行将这一约束用于固定规范补投影。本批从原始真空序列证明这些结论在首选坐标图中的局部形式，并构造同一振幅在实际辅助单位余球面上的分量测度。

固定光滑辅助黎曼度量 $r$、光滑对称非退化背景 $B$ 和光滑对称非退化的内禀真空序列 $g_n$。使用 $g_n$ 到 $B$ 的 $r$ 范数局部一致收敛和相对于背景体积的紧集协变梯度差一致本质有界条件。每张指定首选图携带一个落在图内的坐标闭球 $K$ 和支撑在该球内的实光滑截断。对任意原序列的严格子列，存在同一个进一步的严格子列，使每张图中的原始体积加权梯度与实际固定投影导数配对使用该图同一份迹测度 $\tau$。

## 真空 Ricci 核与投影

将在同一截断和背景逆度规下从内禀真空得到的坐标 Ricci 主行作 Bessel 正则化。这些行在复 $L^2$ 中强趋于零。其角向主系数给出原迹密度上的 Ricci 行约束。写 $G=B^{-1}$，令 $\xi$ 为圆球方向，$A$ 为同一局部协方差的圆单位振幅，则在一个 $\tau$ 余零集上，$A\succeq0$，且对每个复有序二指标向量 $v$，$Av$ 对称并满足 $\mathcal R_{G,\xi}(Av)=0$。

用已有的固定规范补投影符号 $P(\xi)$ 压缩同一振幅得到 $PAP^*$。投影振幅为正半定，在 $G^{ab}\xi_a\xi_b\ne0$ 时为零，在零锥上满足 Lorenz 收缩 $q_b=\xi_b t/2$。将原始振幅与投影振幅分别作零壳限制和同一个四分之一物理收缩，得到 $K\times S^3$ 上相等的测度，等式适用于每个 Borel 集。

## 实际辅助单位余球面

令 $s_r(x,\xi)=\sqrt{r^{ab}(x)\xi_a\xi_b}>0$。用首选图的余切平凡化将 $(x,\xi/s_r)$ 组装为实际余切丛中的协向量 $F_r(x,\xi)$。其 $r$ 对偶能量为 $1$。在同一个迹测度上，辅助单位振幅为 $S_r=s_r^2 A$，两个导数因子换成 $(\xi/s_r)_\alpha(\xi/s_r)_\beta$。$S_r$ 的像满足在该单位方向的 Ricci 核约束。

对余切丛的任一 Borel 集 $E$，有序协方差分量为

$$
\Sigma^K_{r,ij}(E)=\int_{F_r^{-1}(E)}s_r(x,\xi)^2 A_{ij}(x,\xi)\,d\tau .
$$

这些分量组成正半定矩阵，且分量测度集中在辅助单位余球面。构造与原始及投影配对使用同一个细化子列，各取其所对应首选图的迹测度。跨图协方差、重叠域截断相容、全局测度拼接和原定理的矩等式仍待完成。

## 登记声明

- `Burnett.Microlocal.RicciRemainder.chartRicciPrincipal_tendsto_zero_of_intrinsicVacuum`
- `Burnett.Microlocal.RicciRow.roundBesselCoefficient_eq_ricciJetMatrix_of_cutoff_eq_one`
- `Burnett.Microlocal.CurlDensity.factoredAmplitude_in_complexRicciKernel`
- `Burnett.F05.ActualCoordinateRicciDensity.ae_originalVolume_ricciRows_same_density`
- `Burnett.F05.ActualCoordinateRicciDensity.ae_originalVolume_roundAmplitude_in_ricciKernel`
- `Burnett.F05.ActualCoordinateRicciDensity.exists_countable_originalVolume_RicciKernel_projected_pairings`
- `Burnett.F05.ActualChartAuxiliarySection.chartAuxiliaryRay_unit`
- `Burnett.F05.OriginalVolumeAuxiliaryAmplitude.ae_originalVolume_auxiliaryAmplitude`
- `Burnett.F05.ChartCotangentAmplitudeMeasure.cotangentAmplitudeMeasure_apply_round`
- `Burnett.F05.ChartCotangentAmplitudeMeasure.cotangentAmplitudeMeasure_positive`
- `Burnett.F05.ChartCotangentAmplitudeMeasure.cotangentAmplitudeMeasure_zero_off_unit`
- `Burnett.F05.ChartCotangentAmplitudeMeasure.exists_countable_originalVolume_cotangentAmplitudes`
- `Burnett.P01.ae_originalVolume_projectedCovariance_ricciPolarization`
- `Burnett.P01.originalVolume_roundNullMeasure_projected_eq`

[共同源码对应](original-volume-ricci-amplitudes-source-bindings.json)
