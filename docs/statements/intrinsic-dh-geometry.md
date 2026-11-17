# 内禀 Dh、物理三张量范数与原条件的坐标控制

本批支持原文333–369行的几何与局部估计，不关闭 `thm:quadratic`、F04/F05或全文。文章及信任A保持锁定；源码、全部声明和独立回读身份见[绑定](intrinsic-dh-geometry-source-bindings.json)及[复核](intrinsic-dh-geometry-review.md)。新增解释的作者确认尚未记录。完整Lorentz/时间定向/真空数据包装仍按后续消费者实例化。

## 真实诱导导数及图无关性

对原四维光滑流形、辅助Riemannian度量r和光滑双线性Hom丛截面H，由已证全局连接构造

    (∇ʳH)(V,U,W) = V[H(U,W)] − H(∇ʳ_VU,W) − H(U,∇ʳ_VW)。

标量求导实际使用mfderiv。涉及求导的U/W光滑，V只需要点值；H无需对称。构造得到真实切纤维上的连续三线性张量。任意preferred图之间，实际Jacobian/Hessian变换中的两项Hessian相消，再由三槽基展开得到对全部fiber向量的图无关性。没有假设全局光滑标架，也没有以未经证明的全局光滑延拓代替任意点向量。

同一r与H=gₙ−g₀的张量在任意包含该点的preferred图中，三个真实frame基向量上的值精确等于既有 `auxiliaryPerturbationJet(r,g₀,gₙ)`。第一槽是求导方向，后两槽是双线性张量槽；raw偏导与协变导数始终分别处理。

## 物理长度与原局部 L∞ 假设

物理长度为实际逆r的全部有序收缩：

    |T|²_r = Σ r^{ia} r^{jb} r^{kc} T_ijk T_abc。

它与所选preferred图无关，等于真实64维正定Gram空间的Hilbert范数，零空间恰为T=0。此长度不同于连续三线性映射的算子范数；没有改动切空间原Norm实例。固定r、图和target内紧K，有共同A>0控制任意T的组件sup≤A|T|r；A不依赖T或n。

由实际r逆、连接和H的一阶jet，证明 `normScalar r H=|∇ʳH|r` 在全M连续且Borel可测。无需先证明整个张量丛截面的高阶光滑性，也不宣称长度在零点可微。

原假设明确展开为：对每个紧S⊂M，存在有限D_S≥0，对所有n，同一背景几何体积μ₀=dV_g₀下的 `eLpNorm(normScalar r(gₙ−g₀),∞,μ₀|S)≤ofReal D_S`。g₀光滑非退化给出真实μ₀的开集正性。

给定固定图的紧K，先取其真实逆图紧像J，再构造一个共同紧S使J⊂interior S，随后才考虑所有n。较大μ₀|S上的ae界经连续性成为J逐点界，再得辅助坐标jet统一界。没有从可能零测的K自身ae界推出每点界；同一S、D_S和比较常数对所有n有效。

## 原条件的实际连接误差消费者

再由原r物理C⁰loc收敛和上述Dh界，固定Γ(r)·H修正给出raw坐标∂H的最终统一界。实际连接误差为

    Eₙ = Γ(gₙ) − Γ(g₀) − Christoffel(g₀⁻¹, D^{g₀}(gₙ−g₀))。

这里线性项使用背景g₀连接，不是辅助r或裸偏导。由真实光滑、对称、非退化字段及既有连接差恒等式，得到Eₙ在每个固定图紧集一致趋零；并在同一g₀的实际坐标测度上，为每个n内部构造MemLp∞代表，其toLp范数趋零。没有把rawJet界、MemLp或E收敛结论作为额外调用者假设。

四模块共64项完整声明，选择16个语义消费者登记；辅助定义和移项也包含在全部源码/类型/公理独审中。生产模块是 `IntrinsicCov2`、`ManifoldCov3Norm`、`IntrinsicDhMeasure`、`OriginalAdmissibleLocalControl`。

后继[局部弱导数](local-weak-derivative.md)与[连接误差测试](local-weak-ricci.md)消费这些真实对象。完整全局mixed E物理模型、全部定量eq:E、弱Ricci总式、H⁻¹紧性及相空间缺陷测度仍须按实际消费者完成；本批不要求额外uniform D²gₙ、通用丛Lp同构或全局标架。
