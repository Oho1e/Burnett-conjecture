# 四维有符号 Fourier 窗估计

[English](signed-fourier-window-estimates.en.md)

令 $s_k=2^kt$，其中 $t>0$，并取 $q\in\mathbb R^4$、一个有限指标集以及满足 $|c_k|\leq1$ 的复系数。这些估计用于原文第 660–671 行双线性乘子证明的环带算子。

- `signed_annular_sum_L2` 对任意复 $L^2$ 输入，证明符号为 $c_km(s_k\xi)$ 的 Fourier 乘子有限和具有界 $2\,\mathrm{bound}(m)\|u\|_2$。有界符号 $m$ 在开环带 $1/2<|\xi|<2$ 之外为零。
- `dyadic_kernel_hormander` 对任意 Schwartz 函数 $\phi$，证明核 $K(z)=\sum_k c_k s_k^{-4}\phi(z/s_k+q)$ 在 $2|h|\leq |z|$ 区域的积分差界 $C_\phi(1+|q|)$。界对初始尺度、有限指标集、系数和位移 $h$ 一致。
- `signed_window_operator_estimates` 取 $\phi=\mathcal F^{-1}a$，其中频率窗 $a$ 是紧支撑 Schwartz 函数，在开环带之外为零。同一个 $K$ 对每个 Schwartz 输入定义卷积及几乎处处相等的 $L^2$ 代表。其 $L^2$ 范数不超过输入范数乘以 $2\,\mathrm{seminorm}_{0,0}(a)$。

有限指数的环带平方估计及联合乘子界将在后续接入。本组支持引理的原文对应仍待作者确认。[源码对应](signed-fourier-window-estimates-source-bindings.json)
