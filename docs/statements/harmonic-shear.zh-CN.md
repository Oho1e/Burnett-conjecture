# 背景波源的 L² 估计失效

[English](harmonic-shear.en.md) · [陈述 T13](main.md#t13)

Lean 总定理 `Burnett.HarmonicShear.Bounds.harmonic_coordinate_source_counterexample` 对应命题 A.1（`prop:shear`，第 3121–3123 行，证明见第 3124–3169 行）。Lean 从零开始的指标 `n` 对应原文的正指标 $n+1$。

两个互逆的剪切映射是全局光滑微分同胚。实际的 Minkowski 拉回度量具有 Minkowski 符号，内禀 Riemann 全曲率及 Ricci 张量为零。同一组度量精确满足缩并 Christoffel 方程 $H(g_n)=H(m)=0$，物理局部一致收敛到 Minkowski，且实际辅助协变导数有局部统一 $L^\infty$ 界。辅助度量取欧氏度量。

行列式为一的坐标 $(t,x^2,p,q)$ 给出同一个固定紧平行六面体。实际 $(\Box_m h_n)_{21}$ 分量的平方积分为 $4\pi^2(n+1)^4$。关于 Minkowski 几何体积，张量源的欧氏 $L^2$ 范数对每个指标都是有限的，并在同一紧集上趋于无穷。

合成证明快照通过信任方案 A 下 38 项实际类型和传递公理检查，回执 SHA256 为 `bfb6aff7101fd8e719d2f804f23e44a82a57a88c76594ac91457ffa6fa7cb518`。总定理的独立复核核对了原文对应，并逐字节重现原生日志。复跑回执 SHA256 为 `4f6e792cf1b49b3819fb952c3864bb34d51dc4f1b8d8a3719e0c6e825fbea416`。候选使用 X07 的内禀曲率桥接。独立复核证词回执的 SHA256 为 `9baf8197f2e932835368a9b5ea515a4b14dbda2613b6b22209ccf7d4047463d6`。仓库登记源码另经常规模块和工程检查。作者确认仍待记录。
