# 固定规范补投影及其零阶符号

[English](fixed-gauge-projection.en.md)

这批实现锁定稿第 1603–1604、1621–1638 行用到的投影代数和符号估计。

- 对非零频率 $\xi$，以 Euclidean 坐标内积定义 $P_\xi=I-\xi\xi^{\mathsf T}/|\xi|^2$ 和 $\Pi_E(\xi)H=P_\xi H P_\xi$。Lean 证明幂等性、对纯规范张量的消去以及像空间的横向性。对于对称 $H$，证明了原文的显式规范差公式和该差与投影像的正交性。
- 未截断的实系数符号满足有限指数的逐系数 Mikhlin 界。固定径向截断后的系数光滑且为偶函数，在 $|\xi|\le 1$ 时为零，在 $|\xi|\ge 2$ 时与未截断系数一致。每个系数、每个非负整数阶 $n$ 都有独立于频率的常数 $C$，使 $(\max(1,|\xi|))^n\|D^n\Pi(\xi)_{abcd}\|\le C$，并有缓增性。

完整命题 `prop:general-projection` 的后续工作包括实际 Fourier 算子对紧支分布对称梯度的消去、投影场的范数与散度源，以及角向测度的保持。作者确认待记录。

- `Burnett.P01.euclideanGaugeProjection_idempotent`
- `Burnett.P01.euclideanGaugeProjection_kills_gauge`
- `Burnett.P01.euclideanGaugeProjection_range_kills_covector`
- `Burnett.P01.euclideanGaugeProjection_sub_eq`
- `Burnett.P01.euclideanGaugeProjection_orthogonal`
- `Burnett.P01.gaugeProjectionSymbol_mikhlin`
- `Burnett.P01.regularizedGaugeProjectionSymbol_even`
- `Burnett.P01.regularizedGaugeProjectionSymbol_zero`
- `Burnett.P01.regularizedGaugeProjectionSymbol_high`
- `Burnett.P01.regularizedGaugeProjectionSymbol_contDiff`
- `Burnett.P01.regularizedGaugeProjectionSymbol_hasTemperateGrowth`
- `Burnett.P01.regularizedGaugeProjectionSymbol_orderZero_weighted`

[共同源码对应](fixed-gauge-projection-source-bindings.json)
