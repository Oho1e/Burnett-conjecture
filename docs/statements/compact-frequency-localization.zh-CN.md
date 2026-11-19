# 双侧空间截断的紧 Fourier 乘子

[English](compact-frequency-localization.en.md)

在四维欧氏空间中，令 $M_a,M_b$ 为乘以实值光滑紧支撑函数的算子，$p$ 为有界连续复值符号。按工程的 Fourier 约定，$M_a p(D) M_b$ 作用在复 $L^2$ 上。

- `compact_spatial_cutoffs_truncated_multiplier` 证明把 $p$ 截到任意闭频率球所得的算子是紧的。证明把算子写成秩一平面波算子的 Bochner 积分，再使用紧算子空间在算子范数下闭合的性质。
- `compact_spatial_cutoffs_decaying_multiplier` 在 $|ξ|$ 趋于无穷时 $p(ξ)$ 一致趋于零的条件下，证明完整符号所得算子的紧性。有限频率截断在算子范数下收敛。

这组引理用于原文第 403–404 行局部化余项中每个固定基底 Fourier 频率。一般变系数符号还需构造范数可积的算子族，并识别为原量子化。此处支持引理对应关系的作者确认待记录。[源码对应](compact-frequency-localization-source-bindings.json)
