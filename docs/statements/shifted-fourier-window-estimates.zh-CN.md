# 四维移位 Fourier 窗估计

[English](shifted-fourier-window-estimates.en.md)

原文第 626–685 行使用双线性 Coifman–Meyer 估计。形式化证明估计两个环带因子和一个低频因子的乘积。以下声明给出四维欧氏空间 Schwartz 输入的低频因子卷积公式和估计。

- `shifted_window_physical` 把符号为 $e^{2πi\langle sξ,q\rangle}a(sξ)$、$s>0$ 的 Fourier 乘子写成用核 $s^{-4}(\mathcal F^{-1} a)((x-y)/s+q)$ 的卷积。
- `maximalShiftedWindow_Lp` 对全部实数 $s>0$ 的乘子输出取绝对值的逐点上确界，估计其 $L^p$ 半范数。对每个实指数 $p>1$ 和每个移位 $q$，上界为输入半范数乘以窗函数常数、$(1+\lVert q\rVert)^5$ 和强型中心极大函数界。`maximalShiftedWindow_measurable` 证明该上确界可测。

交换子还需有限指数的环带平方估计及联合乘子论证。论文对应关系的作者确认待记录。[源码对应](shifted-fourier-window-estimates-source-bindings.json)
