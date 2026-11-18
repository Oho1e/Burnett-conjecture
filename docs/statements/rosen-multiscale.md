# 多尺度 Rosen 真空序列

[English](rosen-multiscale.en.md) · [锁定原文](../../paper/burnett.tex#L3360)

Lean 的序号从零开始，取正频率参数 $a_n=n+1$，快频率为 $e^{a_n}$。局部常微分方程采用原文的初值 $B_n(0)=1$、$B'_n(0)=0$。系数 $(\psi_n')^2$ 在 $I=(-1/4,1/4)$ 上有统一 $L^\infty$ 界，对任意实 $L^1(I)$ 测试收敛到常数 $1$。对同一组光滑解，$B_n\geq\cos(2u)>0$，一阶和二阶导数一致有界，$B_n$ 及 $B'_n$ 在闭区间上分别一致收敛到 $\cos u$ 和 $-\sin u$。后两项收敛由振荡原函数估计直接得到。

| 原文行 | Lean 中的实际对象 |
| --- | --- |
| 3360–3367 | `phase`、`rosen_phase_LInfinity_weakStar`、`exists_smooth_rosen_sequence_c1`。 |
| 3367–3371 | `exists_rosen_multiscale_vacuum_geometry` 中采用同一组 $B_n$ 的原坐标与拉回坐标实际 Ricci 方程。两个极限的 Ricci 张量均为 $2\,du^2$。 |
| 3373–3374 | `rosen_full_metric_essential_lower_bounds` 给出全度规及其二阶导数阵列在四维乘积盒上的本质上确界下界。下界分别为 $\cos^2(1/2)/(2a_n)$ 与 $2e^{-4}\cos^2(1/2)e^{a_n}-42e^4$。`rosen_no_common_full_metric_scale` 排除共同尺度。 |
| 3376–3386 | `rosenCoordinates_inverses_on_slab`、`rosenCoordinates_smooth_on_slab`、`pulledRosenField_eq_jacobian_pullback`、`pulledRosen_contractedSource_zero`。实际变换为 $v=B_n(u)V$，源由密度加权逆度规的散度计算。 |
| 3371、3386 | `rosen_full_kinetic_limit` 使用沿 $du$ 构造的正 Radon 图测度，权重为实际体积密度的两倍。`Transport.BaseTestClass.intrinsic_tensor_einstein_moment` 给出底空间内蕴光滑紧支撑张量测试的二阶矩恒等式。`Transport.TestClass.intrinsic_compact_test_transport` 给出去零相空间内蕴光滑紧支撑测试的全 Hamilton 输运。每套坐标下的两个恒等式使用同一测度。 |
| 3385–3386 | `RosenMultiscaleSequence.euclideanDh_eLpNorm_on_compact` 使用同一组 $B_n$，在每套坐标下取固定欧氏辅助度规及 $g_n-g$ 的实际协变导数。在开条带的每个紧子集上，导数的 Hilbert 范数有对 $n$ 一致的本质上确界。 |

原度规在 $u\in[-1/4,1/4]$ 的条带上一致收敛。拉回度规在条带内每个固定的 $V$ 有界区域一致收敛，并有对该区域统一的一阶坐标导数界。两套坐标的度规在实际坐标域内光滑，具有一负三正的 Lorentz 号差及光滑类时方向。

`Burnett.RosenMultiscale.rosen_multiscale_full_example` 汇合序列及两项动力学恒等式。本例在固定乘积坐标中直接证明曲率和输运。一般 Rosen 命题 `prop:rosen` 与主输运定理仍是独立义务。
