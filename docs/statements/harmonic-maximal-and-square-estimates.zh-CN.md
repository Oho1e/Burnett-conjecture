# 四维极大函数与环带平方估计

[English](harmonic-maximal-and-square-estimates.en.md)

原文第 626–685 行在三次能量证明中使用有限指数乘子界。以下解析引理用于该证明。

- `centeredMax_weak_type` — 四维中心极大算子对所有正半径的闭球取上确界，其弱 (1,1) 分布估计常数为 256。

- `centeredMax_complex_Lp` — 对每个复值可测输入和每个实指数 p > 1，输入绝对值的极大函数的 Lᵖ 半范数至多为输入半范数的 (256 · 2ᵖ · p/(p−1))^(1/p) 倍。

- `annular_square_L2` — 若有界符号在 1/2 < |ξ| < 2 之外为零，则任意有限组二进尺度乘子的 L² 范数平方和至多为符号界平方、输入范数平方乘积的两倍，起始尺度可为任意正实数。

- `shifted_annular_square_L2` — 对乘上 Fourier 调制因子的光滑环带窗，L² 范数平方和估计的常数为 2，适用于所有调制向量、正起始尺度和有限尺度集。

已证明四维中心极大函数的弱型、强型界和环带平方和的 L² 界。继续构造交换子，建立有限指数的跨尺度双线性估计，再接入三次能量的连续性与系数差结论。 [源码对应](harmonic-maximal-and-square-estimates-source-bindings.json)
