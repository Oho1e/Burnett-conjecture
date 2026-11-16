# 局部逆度规、连接误差与正泛函界

2026-11-16；从用户已合并且main CI通过的PR7提交`d5c3d06e55c39776716f1fc2e4baddebd032ab00`接续。原文、依赖锁、数学标准1.2及信任A不变。当前交付是F04/F05的必要支持结果，不能据此称完整二次极限定理或整篇已证。

## 实际逆及统一控制

`InversePerturbation`在真实`Tensor2 = Fin 4 → Fin 4 → ℝ`的分量sup范数上，明确以有限求和定义矩阵复合，从左右逆恒等式证明
\[
g_1^{-1}-g_0^{-1}=g_1^{-1}(g_0-g_1)g_0^{-1}.
\]
乘积范数常数为4，逆差估计常数16。条件`16‖g₁−g₀‖‖g₀⁻¹‖≤1/2`通过吸收推出新逆界`‖g₁⁻¹‖≤2‖g₀⁻¹‖`，继而逆差不超过`32‖g₀⁻¹‖²‖g₁−g₀‖`。新逆界不是输入。真实对称非退化双线性形式及给定基的`FiberMetric.contravariant`实际供给逆律。

`InverseField`显式使用矩阵的逆实例，未把Tensor2的逐项倒数当矩阵逆。从仅K内非退化、背景分量在K连续及K紧，实际推出背景逆连续及统一B>0。真实矩阵场的一致收敛给同一B下的最终小量、统一新逆界和逆场一致收敛。`InverseSequence`将其接到实际双线性度规的contravariant字段，保留同一参数和序列。K外不要求非退化。

## 背景正则性及真实误差

`BackgroundConnection`只用开集U上背景分量C¹、K⊂U及K内对称非退化，证明实际Fréchet坐标一阶jet连续，进而显式矩阵逆与Christoffel公式计算的连接连续，并在K等于真实`metricConnection`。紧性实际给Γ(g₀)的统一界G>0；没有假设所求Γ连续或界。

`ConnectionError`定义的是两幅真实连接之差减去背景线性主部：
\[
E=(\Gamma(g_1)-\Gamma(g_0))-L_{g_0}(\nabla^{g_0}(g_1-g_0)).
\]
它证明E恰为将逆差代入同一真实协变扰动jet的Christoffel构造。实际分量sup范数有`‖Christoffel(A,J)‖≤6‖A‖‖J‖`，小扰动下得到
\[
\|E\|\le192\|g_0^{-1}\|^2\|g_1-g_0\|\|J\|.
\]
`PerturbationJet`以真实协变导数的两个收缩证明`‖J‖≤‖rawJet‖+8‖Γ₀‖‖h‖`；一致收敛给最终`‖h‖≤1`，从而以真实raw一阶界构造同一H。

最终声明`Burnett.Geometry.ConnectionErrorSequence.metricConnectionError_uniform_of_coordinate_bounds`将上述接口实际组合：从局部C¹背景、紧K、仅局部对称/非退化、实际序列在K可微、坐标rawJet最终统一界及原度规分量的一致收敛，推出**实际E在K一致趋零**。该类型没有另列B、G、J界、逆的小扰动或E收敛作为前提。反向`rawJet≤covariantJet+8Γh`也已证明，供未来辅助连接桥使用。

## L∞与F05的两个一般工具

`UniformLInfinity`对任意测度证明从真实a.e.界到实际Lp∞范数界，以及可测固定K上一致趋零到限制测度上的真实Lp∞趋零。不要求总测度有限；每个函数的`MemLp ∞`仍是显式输入。没有通过`ENNReal.toReal ∞=0`制造伪界，也没有证明原E的可测性或物理r范数。

`PositiveFunctional`对真实C_c子空间中的实线性L，在显式正性条件下，以实际非负order-unit截断e将固定支撑测试的真实C₀范数传到`|L f|≤‖f‖∞L(e)`。全C_c正泛函版及LCH/T2紧集上实际Urysohn截断给非负有限局部常数。该工具不假设有限总质量，也不把原PDO正性、C_c延拓、RMK或测度存在当作已证。

## 与原文之间仍须闭合的接口

原文91–105行给的是`D=∇ʳ`下的`‖D h_n‖L∞(K;r)`界及流形上的C⁰局部收敛。**本轮最终入口使用坐标范数及raw坐标一阶界，两者没有被改名成原假设。** 辅助r连接、物理r与坐标范数的实际紧集比较、a.e.导数界到所需点态局部条件、流形图及dV对应仍需后续证明。本轮统一误差及一般Lp∞桥不能据此提升为原admissible下完整物理E结论。

原真空条件到弱Ricci矩、分布积分分部、H⁻¹紧性，F05真实PDO界/趋零误差正性/共同测度及全局自然性均仍开放。无gn的统一高阶导数或全域非退化假设被新增。新数学解释的作者确认待记录，整篇继续development/verified=false。
