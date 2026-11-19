# 三次能量交换子的 Fourier 符号

[English](cubic-energy-fourier-symbols.en.md)

原文第 626–677 行取一个在非零频率上光滑的实一次齐次符号。以下结果覆盖原文符号分解及其 Schwartz 测试配对。

- `segment_norm_lower` — 低频截断非零时，整个积分线段上各点的范数至少为第二输入频率范数的四分之三，线段避开原点。

- `commutator_symbol_decomposition` — 由同一实一次齐次符号得到四维精确分解、三个联合符号及单频因子的各阶导数界。恒等式包括合频为零的情形。

- `pieces_integrable` — 用三个 Schwartz 函数的 Fourier 变换测试时，三类项中的每个分量都在联合频率空间上绝对可积。

- `fourier_trilinear_identity` — Lebesgue 配对在合频处取第三个 Fourier 变换的共轭，等式保留两个单频乘子的符号和位置。

八份正式模块的 38 项公开声明已与独立编译的类型及其公理逐项核对。

已证明全局符号分解及 Schwartz 测试下的绝对可积频率配对。下一步识别物理空间交换子、证明有限指数乘子范数界，再接入对称极化、连续性与系数差结论。 [源码对应](cubic-energy-fourier-symbols-source-bindings.json)
