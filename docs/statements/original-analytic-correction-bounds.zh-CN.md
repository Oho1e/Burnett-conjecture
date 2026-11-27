# 解析修正算子及其粗交换子的估计

[English](original-analytic-correction-bounds.en.md)

`Burnett.A08.exists_paperAnalyticCorrectionBounds` 是论文第 1380–1394 行
`lem:analytic-correction-bounds` 的入口。输入符号沿用第 1248–1266 行的独立变量，
定义在低高频归一化紧域的邻域上。比例截断在 $|p|\geq\rho|\xi|$ 时为零，其中
$\rho<1/2$ 固定。高频红外截断保留在符号中，固定的低因子绝对频率截断放在 $H$ 上。
有限导数阶数 $K$ 与常数 $C$ 先于光滑延拓及其导数界 $M$ 选定。

结论中的两个算子给出实际的标量傅里叶配对。高频伴随的符号为
$b^\dagger(p,\xi)=\overline{b(-p,\xi+p)}$，低因子为 $\overline H$。
配对沿用弧度频率的归一化 $(2\pi)^{-8}$。正向算子及其高频伴随均满足

$$
\begin{aligned}
\|T_Hu\|_2 &\le CM\,\|H\|_4\,\|\partial u\|_4,\\
\|[\partial_a,T_H]u\|_2 &\le CM\,\|\partial_aH\|_4\,\|\partial u\|_4,\\
\|[d,T_H]v\|_2 &\le CM\,\|\partial d\|_\infty\,\|H\|_4\,\|v\|_4.
\end{aligned}
$$

坐标交换子经 Schwartz 测试识别为 $T_{\partial_aH}$。粗交换子覆盖所有实值全局
Lipschitz 系数 $d$，允许线性增长。先减去零点值再逼近系数，两项傅里叶积分取极限，
得到的有界泛函由 $L^2$ 输出表示。伴随估计使用第二组指数 $(4,2,4/3)$。
由 Mathlib 的 Rademacher 定理和平滑卷积，几乎处处梯度范数的本质上界是可用的
Lipschitz 常数。

`Burnett.A08.exists_paperFiniteMatrixAnalyticCorrectionBounds` 给出低频、输入和输出均为有限分量的三条估计。正向 Fourier 作用对低频和输入分量求和。真高频伴随共轭低频场，并对低频和输出分量求和。值与导数估计使用分量范数之和，粗交换子配对保留系数梯度界。

`Burnett.A08.exists_paperRadialInhomogeneousAnalyticCorrectionBounds` 允许固定光滑径向权重在充分高频处等于频率半径。值和坐标导数估计使用高频测试场的 L⁴ 范数与梯度范数之和。该类包括固定径向窗口上的非齐次权重，并沿用同一个粗交换子梯度估计。

标量入口与两个补充入口均通过具名原生核验。工程审计和作者确认分别记录。 [源码与验证记录](original-analytic-correction-bounds-source-bindings.json)
