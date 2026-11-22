# 固定矩阵投影的梯度交换子

[English](projection-hodge-commutator.en.md)

本批接续锁定稿第 1636–1642、1674–1684 行，使用此前定义的固定投影。在非零弧度频率下，令 $P_\xi=I-\xi\xi^{\mathsf T}/|\xi|^2$，$J$ 为原红外高通截断。矩阵 $L^2$ 乘子依次作用于两个指标并乘以 $J$，在 Schwartz 矩阵场上与原来的 $\Pi$ 符号 $J P_\xi(\,\cdot\,)P_\xi$ 一致。

对单槽 $P$，取 $A=Pw$，令 $S_{jk}=\delta_{jb}A_k-\delta_{kb}A_j$。横向条件给出 $\sum_j\partial_j S_{jk}=\partial_b A_k$。乘积法则和对称 Hessian 与反对称张量的消去给出

$$
  [P,f]\partial_b w
   =-P\bigl((\nabla f)(w-A)_b\bigr)
     +(I-P)\Bigl(\bigl(\textstyle\sum_j(\partial_j f)S_{jk}\bigr)_k\Bigr).
$$

Schwartz 输入的弧度 Fourier 支撑共同包含在避开原点的紧集时，Lean 构造给出 Schwartz 见证 $A$。单槽 $L^2$ 界的常数可先于方向、系数、输入和频率紧集选定。将左右两槽与同一个 $J$ 组合，得到实际矩阵交换子。环域逼近同时控制输入及一阶导数的 $L^2$ 收敛，移除了对输入频谱的限制。

对任意全局 $L$-Lipschitz 的复值标量系数 $f$，最终给出连续复线性算子 $T_{b,f}$ 在整个矩阵 $L^2$ 上的界

$$
  \|T_{b,f}w\|_2\le C L\,\|w\|_2 .
$$

在 Schwartz 矩阵场上，$T_{b,f}w=\Pi(f\partial_b w)-f\Pi(\partial_b w)$，两个系数乘积都是实际的 $L^2$ 元素。矩阵空间使用固定有限个分量 $L^2$ 范数的最大值。先减去 $f(0)$ 再做紧支截断以处理光滑系数的线性增长。归一化平滑卷积保留 Lipschitz 界，并一致逼近任意 Lipschitz 系数。最后用 Schwartz 场的稠密性延拓，常数对四个方向、全部系数及输入统一。

完整 P01 仍需把坐标真空余项、全空间散度源及角向测度保持接到同一投影场。作者确认待记录。

- `Burnett.P01.skew_symmetric_contraction_zero`
- `Burnett.P01.hodgeCommutator_spectrum`
- `Burnett.P01.hodgeCommutator_action`
- `Burnett.P01.exists_hodgeCommutator_action_l2_bound`
- `Burnett.P01.exists_hodgeTransverseSchwartz_of_compactSpectrum`
- `Burnett.P01.projectionFullL2_eq_schwartz`
- `Burnett.P01.projectionFullCommutatorL2_eq_actual`
- `Burnett.P01.exists_projectionFullCommutatorL2_bound_on_annularCore`
- `Burnett.P01.projectionMatrixAnnularApproximation_tendsto`
- `Burnett.P01.projectionMatrixAnnularApproximation_derivative_tendsto`
- `Burnett.P01.exists_projectionFullCommutatorL2_bound`
- `Burnett.P01.projectionCoefficientCutoff_lipschitz`
- `Burnett.P01.projectionLipschitzCoefficientProductL2_ae`
- `Burnett.P01.projectionCoefficientCutoff_product_tendsto`
- `Burnett.P01.exists_projectionLipschitzCommutatorL2_bound`
- `Burnett.P01.exists_smooth_lipschitz_approximation`
- `Burnett.P01.exists_projectionGeneralLipschitzCommutatorL2_bound`
- `Burnett.P01.exists_projectionLipschitzCommutatorL2_extension`

[共同源码对应](projection-hodge-commutator-source-bindings.json)
