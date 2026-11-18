# 容许的平直度量序列具有平直的光滑极限

[English](flat-rigidity.en.md) · [陈述 T17](main.md#t17)

锁定原文为命题 D.2（`prop:flat-rigidity`，第 3390–3392 行），证明位于第 3393–3421 行。容许序列的假设位于第 91–104 行。

Lean 总定理为 `Burnett.FlatRigidity.isFlat_of_original_flat_sequence`。它使用由辅助 Riemann 度量 $r$ 度量的局部一致收敛，以及 $\nabla^r(g_n-g_0)$ 在每个紧集上的统一 $L^\infty$ 界。工程采用极限度量的体积 $dV_{g_0}$ 作为本质上确界的参考测度。假设和结论使用同一个内禀全曲率谓词 `Burnett.Geometry.FlatRigidity.IsFlat`，即每一点的完整 `CurvatureFiberTensor.tensor` 都为零。光滑、对称、非退化的条件已足够，涵盖原文的 Lorentz 度量。全平直也推出真空条件。[内禀导数陈述](intrinsic-dh-geometry.md)

证明用原始导数界选取一个共同的坐标球，构造中心值为单位矩阵的径向积分解。对位移求导并使用曲率为零，得到所有坐标方向上的平行方程。较小闭球上的紧性为标架和逆矩阵给出同一个严格递增子列。同一子列的 Christoffel 系数对局部 $L^1$ 测试函数弱收敛。弱平行方程和分布导数交换给出坐标曲率为零，内禀曲率桥接把这个结论传到流形的每一点。

冻结的合成证明通过了信任方案 A 下 18 项实际类型和传递公理检查，回执 SHA256 为 `18b0a4a806d27af29b6ff237c3eb7e54bfe0274cceb114e7c3c332377623de5c`。独立复跑逐字节重现了原生日志，并核对了原文假设、标架构造和内禀结论。独立回执 SHA256 为 `b3331ff99e6ee273291f016325cf0bfa5f7da0fbc40c3d45e7ad09a698540286`。这些回执对应合成证明快照。工程检查涵盖范围清单登记的模块。作者确认仍待记录。
