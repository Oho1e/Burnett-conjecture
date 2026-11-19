# 角向 Fourier 乘子与紧支撑截断

[English](angular-cutoff-commutator.en.md)

构造二次缺陷测度时，需要截断与算子的交换子作用于原序列后消失（F05，原文第 395–412 行）。对 $\mathbb R^4$ 上一个固定角向 Fourier 乘子 $m(D)$ 和一个光滑紧支撑复函数 $\chi$ 的乘法算子，Lean 证明

$$
\big\|m(D)(\chi u_n)-\chi m(D)u_n\big\|_{L^2}\longrightarrow 0.
$$

实值光滑输入的支撑位于同一固定紧截断等于一的区域，序列具有统一 $L^2$ 界，且对每个实值光滑紧支撑测试弱趋零。上式取这些输入的复 Schwartz 代表元。乘子符号有界，在原点以外光滑，对正伸缩零次齐次。换成在某个固定频率球外与原符号一致的有界符号，结论仍成立。

Fourier 侧的积分核含有因子 $m(\xi)-m(\eta)$。角向差分估计与截断 Fourier 变换的可积一阶矩共同控制高输入频率。序列假设推出每个固定频率球中的 Fourier 能量趋零。用同一高低频分解还可以证明，符号在无穷远一致趋零的有界频率乘子作用于该序列后强趋零。

Lean 命名空间为 `Burnett.Microlocal.AngularCommutator`。齐次情形的定理是 `cutoffCommutator_tendsto_zero_of_localized_weak_zero`，固定低频修改由 `cutoffCommutator_tendsto_zero_of_infrared_regularization` 处理。F05 所需的变系数算子、两图的坐标比较及共同张量测度另有相应的证明义务。
