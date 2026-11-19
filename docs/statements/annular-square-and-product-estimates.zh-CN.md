# 四维环带平方函数与乘积估计

[English](annular-square-and-product-estimates.en.md)

这些声明给出原文第 660–671 行 Fourier 乘子论证所需的有限指数估计。空间变量均取自 $\mathbb R^4$。

- 对每个 $1<p<\infty$，有限有符号环带卷积具有 $L^p$ 界。频率窗是紧支撑 Schwartz 函数，在 $1/2<|\xi|<2$ 之外为零。界适用于任意复 $L^p$ 输入，并对初始尺度 $t>0$、有限指标集和模不大于一的复系数一致，移位因子为 $1+|q|$。
- 同一组环带卷积核的平方函数具有相应的 $L^p$ 界和移位因子，尺度为有限个互异的 $2^k t$，其中 $k\in\mathbb N$，初始尺度 $t>0$ 共用。对 Schwartz 输入，Lean 逐点识别该平方函数与原移位 Fourier 窗算子给出的平方函数。
- 若三个指数 $p,s,z$ 都在 $(1,\infty)$ 内并满足目标指数为一的 Hölder 关系，有限个三因子绝对乘积之和的积分由三个输入的 $L^p,L^s,L^z$ 范数乘积控制。两个环带因子在各自尺度族内使用互异二进尺度，初始尺度分别为 $t$ 和 $u$。第三个因子是任意正尺度下作用于 Schwartz 输入的移位 Schwartz 窗，用作低频因子。移位因子为 $(1+|q|)(1+|v|)(1+|l|)^5$。

全尺度联合乘子的三线性估计已得到，继续接入论文中的三次能量证明。 [定量联合 Fourier 乘子估计](joint-fourier-multiplier-estimates.zh-CN.md)本组支持引理的对应关系待作者确认。[源码对应](annular-square-and-product-estimates-source-bindings.json)
