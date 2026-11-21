# 角帽与有符号相位下界

[English](angular-cap-geometry.en.md)

本批对应锁定稿第 893–1025 行。

- 对三个非零频率之和为零的三元组，循环低槽权重和可比权重构成非负分割。薄锥内可比三元组的射影夹角满足统一界。
- 对固定的紧 Lorentz 形式族，构造带有两个有符号提升的有限射影零帽覆盖、光滑基本帽和放大帽。覆盖重叠数一致有界，帽数至多为常数乘以 $\delta^{-2}$。抛物重标度后的基本帽和放大帽都满足统一导数界。
- 固定有限维场的纤维后，对于每个有限实数 $p>1$，基本帽和放大帽都有统一的单帽 $L^p$ 界。对每个固定的有限 $p_*>3$，角帽族的场 $L^3$ 求和具有计数因子 $N_\delta^{1/(3(p_*-2))}$。这些界的常数在紧族和允许的帽宽上统一。
- 有符号精确相位 $q_m(p+q)-q_m(q)$ 的绝对值在低槽远角区下界为 $b\delta^2|p||q|$。Lean 假设保留三个频率的薄锥条件和低槽远角权重非零条件。

以下九个支持声明供近角和远角论证调用。原稿中的近角和远角母引理仍待完成，作者确认待记录。

- `Burnett.Analysis.ProjectiveNullCaps.triad_cutoff_partition_nonnegative`
- `Burnett.Analysis.ProjectiveNullCaps.exists_uniform_comparable_nearNull_wedge`
- `Burnett.Analysis.ProjectiveNullCaps.exists_uniform_lowFar_signedQuadraticPhase_gap`
- `Burnett.Analysis.ProjectiveNullCaps.exists_uniform_projective_null_caps`
- `Burnett.Analysis.ProjectiveNullCaps.exists_smooth_thinCone_capMultipliers`
- `Burnett.Analysis.ProjectiveNullCaps.actual_capMultiplier_parabolic_jets`
- `Burnett.Analysis.ProjectiveNullCaps.actual_enlargedCapMultiplier_parabolic_jets`
- `Burnett.Analysis.CapFourier.exists_uniform_actual_capMultiplier_fieldLp`
- `Burnett.Analysis.CapFourier.exists_uniform_actual_capMultipliers_field_angular_L3`

[共同源码对应](angular-cap-geometry-source-bindings.json)
