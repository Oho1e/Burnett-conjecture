# 一般双极化 Rosen 命题

[English](rosen-two-polarization.en.md) · [锁定原文](../../paper/burnett.tex#L3305)

`Burnett.RosenPlaneWave.two_polarization_rosen_closure` 对应锁定论文第 3305–3359 行的 `prop:rosen`。坐标域是实 $u$ 轴上的开集与 $\mathbb R^3$ 的乘积，涵盖原文光滑乘积时空所用的开区间。屏矩阵 $\gamma$ 是实对称正定 $2\times2$ 矩阵。证明允许非对角极化，使用局部一阶导数界。

| 原文行 | Lean 对应 |
| --- | --- |
| 3307–3312 | `ScreenPhysicalSequence` 规定序列及极限屏矩阵光滑正定、Ricci 真空方程，以及任意正定辅助度规下的局部收敛和一阶协变导数界。`screen_local_controls_of_physical_admissible` 从中推出全序列在每个 $u$ 紧集上的逐点屏导数界。 |
| 3313–3324 | `screenBilinear_computedConnection` 和 `screenBilinear_coordinateRicci` 对固定乘积坐标中的双线性度规求导，得到 $L=\gamma^{-1}\gamma'/2$、$\tau=\operatorname{tr} L$ 及 $uu$ 分量的 $-\tau'-\operatorname{tr}(L^2)$。 |
| 3325–3342 | `screenShear` 使用正定逆平方根定义 $S=\gamma^{-1/2}\gamma'\gamma^{-1/2}/2$。在每个紧子区间上，归一化剪切矩阵 $S_n$ 的各个分量对任意实 $L^1$ 测试弱星收敛到 $S$ 的对应分量，平方 Frobenius 能量 $\sum_{A,B}(S_n)_{AB}^2$ 弱星收敛到 $-\tau'$。真空迹恒等式与局部弱下半连续性给出光滑非负密度 $\rho=-\tau'-\sum_{A,B}S_{AB}^2$。 |
| 3343–3358 | `screenHamilton_canonical_du` 使用逆度规及半二次 Hamilton 量。在 $du$ 处，$P$ 的底变量导数为零，且 $H_P=-\partial_v$。测度集中于 $du$，相对于坐标 Lebesgue 测度的权重为 $\rho\sqrt{\det\gamma}$。 |

同一见证 `phaseMeasure I (screenKineticWeight γ)` 有去零相空间中的相对闭载集，载集包含于零锥。Einstein 恒等式用全部张量分量与实际 Einstein 张量和实际度规体积密度配对。对底空间内蕴光滑紧支撑张量测试，两侧 Bochner 积分均存在。完整相空间输运适用于所有内蕴光滑紧支撑标量测试，也使用同一测度。相空间在任一底空间紧集上方的部分，对任意连续正定辅助度规的协向量长度平方可积。

若密度恒为零，结论允许零测度。显式非零的多尺度例子见 X06。一般命题采用乘积坐标，并对 $v$ 直接积分。
