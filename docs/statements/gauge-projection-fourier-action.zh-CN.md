# 固定规范补投影的 Fourier 作用

[English](gauge-projection-fourier-action.en.md)

本批对应锁定稿第 1619–1642、1697 和 2036–2042 行，使用同一个固定红外截断。

- 对矩阵符号的每个系数，构造 Schwartz 空间上的连续复线性 Fourier 乘子。其弧度制 Fourier 变换及物理空间积分与原符号一致。
- 复矩阵的点态作用等于这些系数的双重求和，并逐频消去纯规范振幅。坐标导数的弧度 Fourier 公式给出 Schwartz 势的对称梯度在该投影下的频率消去。
- 对 Schwartz 空间的复连续线性对偶，定义实际的逐分量投影并证明任意温和分布协向量的对称梯度被它消去。对偶配对通过预合成实现。原文紧支坐标分布与此对偶模型的识别另行接入。
- 对每组固定分量和每个有限实数 $p>1$，实际正则化乘子在标量 Schwartz 输入上有 $L^p$ 界。证明用一次固定高通接齐次乘子，并核对弧度符号。

完整命题 `prop:general-projection` 的后续工作包括原度规序列的投影场及范数、全空间有界散度源和完整角向测度保持。作者确认待记录。

- `Burnett.A07.radianFourier_coordinateDerivative`
- `Burnett.P01.gaugeProjectionSchwartzComponent_radianFourier`
- `Burnett.P01.gaugeProjectionSchwartzComponent_eq_radianAction`
- `Burnett.P01.regularizedComplexGaugeProjection_apply`
- `Burnett.P01.regularizedComplexGaugeProjection_kills`
- `Burnett.P01.regularizedComplexGaugeProjection_symmetrizedGradient`
- `Burnett.P01.temperedGaugeProjection_symmetrizedGradient`
- `Burnett.P01.radianFourier_projectionInfraredAction`
- `Burnett.P01.radianAction_regularizedGaugeProjectionSymbol`
- `Burnett.P01.exists_regularizedGaugeProjectionSymbol_Schwartz_Lp_bound`

[共同源码对应](gauge-projection-fourier-action-source-bindings.json)
