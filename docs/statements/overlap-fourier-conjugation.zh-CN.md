# 首选图重叠域的梯度换图与 Fourier 比较

锁定原稿第 395–428 行使用同一原度量序列的局部零阶测试。第 428 行要求核对张量分量与测试算子的换图。本批证明真实首选图重叠域中的两项输入。第一项是协变梯度及其参考体积半密度的变换，第二项是固定红外归一化角乘子的 Fourier 换图误差强趋于零。

固定光滑辅助黎曼度量 $r$、光滑非退化背景 $B$ 和光滑序列 $g_n$。沿用原序列相对于 $r$ 的局部一致收敛和紧集上的协变梯度差一致本质有界条件。取首选图变换 $\Phi$，以及包含在换图开域内的闭坐标球 $K$ 和支撑在该球内的实光滑截断 $\chi$。实际体积加权原梯度用 $B$ 的体积半密度与 $\chi$ 乘在各有序坐标偏导分量上。

## 梯度与余向量的几何换图

在同一截断和体积半密度下，$\partial(g_n-B)$ 与 $D^r(g_n-B)$ 的各分量之差在复 $L^2(dx)$ 中强趋于零。把源图的截断搬到目标图时，两组协变梯度满足逐点三槽关系。源图的系数是目标梯度拉回后在三个协变槽分别乘以 $D\Phi$，再乘 $w(x)=\sqrt{|\det D\Phi(x)|}$。

同一协向量的列坐标按 $D\Phi(x)^{-\mathsf T}$ 从源图变到目标图。将变换后的圆方向重新归一化给出圆球相空间重叠域的同胚，并满足三图复合律。两图构造的辅助单位协向量在实际余切丛中相等。给定有序梯度协方差的相应矩阵合同，辅助单位振幅也按二张量坐标矩阵合同变换。

## 原梯度序列上的 Fourier 比较

取有界、离零光滑且对正伸缩零次齐次的角符号 $m$，用固定径向截断 $\chi_0$ 构造归一化符号 $m_{\mathrm{hi}}=(1-\chi_0)m$。将截断原梯度分量 $f_n$ 搬到目标图时，在 $\Phi(K)$ 内采用 $g_n^{\mathrm{tr}}(\Phi(x))=f_n(x)/w(x)$，并在窗口外作零延拓。该运输有全空间光滑紧支见证。

在 $K$ 上，比较作用于 $g_n^{\mathrm{tr}}$ 的 Fourier 乘子 $m_{\mathrm{hi}}$ 经半密度拉回后的结果，与作用于源输入的冻结符号 $m_{\mathrm{hi}}((D\Phi(x)^*)^{-1}\xi)$。有限截断的差恰等于实际半密度核与冻结线性核的逐壳差之和。第 $j$ 壳的核差由

$$
\frac{C\,2^{3j}}{(1+b\,2^j|x-y|)^5},\qquad b>0,
$$

控制，四维 Schur 积分给出 $2^{-j}$ 的增益。移除外层频率截断后，二者之差沿源图实际原度量梯度的整个序列在 $L^2(dx)$ 中强趋于零。

可积支配的分离符号族已有在同一图内迹测度上交换极限与参数积分的证明。接续需要把实际随基点变化的冻结角符号放入该参数表示，识别两个图的局部缺陷协方差及其截断限制，并进行全局拼接。

## 登记声明

- `Burnett.Geometry.UnitNullCompactness.cotangentTransitionMatrix_eq_inv_transpose`
- `Burnett.Geometry.UnitNullCompactness.symbolNorm_cotangentTransitionMatrix`
- `Burnett.F05.OverlapCovectors.continuous_roundOverlapTransition`
- `Burnett.F05.OverlapCovectors.roundOverlapTransition_comp`
- `Burnett.F05.OverlapCovectors.chartAuxiliaryRay_roundOverlapTransition`
- `Burnett.F05.OverlapCovectors.auxiliaryAmplitudeCovariance_roundOverlapTransition`
- `Burnett.F05.OverlapCovariantGradient.originalGradient_sub_covariantGradient_tendsto_zero`
- `Burnett.F05.OverlapCovariantGradient.exists_originalCovariantGradient_overlap_inputs`
- `Burnett.Microlocal.OverlapKernel.transition_taylor_remainder`
- `Burnett.Microlocal.OverlapKernel.overlap_halfDensityKernel_changeVariables`
- `Burnett.Microlocal.OverlapKernel.frozenChartFrequency_inverse_adjoint`
- `Burnett.Microlocal.OverlapKernel.overlap_frozen_shellKernel_symbol`
- `Burnett.Microlocal.OverlapKernel.overlap_shellKernel_uniform_envelope`
- `Burnett.Microlocal.Overlap.overlapKernel_action_norm_le`
- `Burnett.Microlocal.Overlap.boundedKernel_action_tendsto_zero`
- `Burnett.Microlocal.Overlap.exists_actualOverlapShell_actions_tendsto_zero`
- `Burnett.Microlocal.OverlapKernel.overlap_partialAngularFourier_difference_sum_actions`
- `Burnett.Microlocal.Overlap.exists_localizedPartialAngularDifference_limit`
- `Burnett.Microlocal.Overlap.tendsto_inverseFourier_partialAngular_comp`
- `Burnett.Microlocal.OverlapKernel.transportedHalfDensity_smooth_compact_support`
- `Burnett.Microlocal.Overlap.exists_originalVolume_weakL2_representatives`
- `Burnett.Microlocal.Overlap.exists_originalVolume_overlap_fourierDifference_limit`
- `Burnett.Microlocal.Overlap.exists_originalVolume_overlap_normalizedFourierDifference_zero`
- `Burnett.Microlocal.Overlap.tendsto_integrated_separablePairings_of_matrixDensity`

[共同源码对应](overlap-fourier-conjugation-source-bindings.json)
