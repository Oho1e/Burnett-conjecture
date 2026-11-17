# 原条件下的连接误差测试

模块 `Burnett.Analysis.LocalWeakRicci` 新增8项支持定理，选择4个实际消费者登记，对应原文358–381行。源码/独审身份见[绑定](intrinsic-dh-geometry-source-bindings.json)及[复核](local-weak-ricci-review.md)。这一步没有关闭完整弱Ricci、H⁻¹、F04/F05或全文；新解释的作者确认尚未记录。

保留精确分解Cₙ=Γ(gₙ)−Γ(g₀)=L(D^{g₀}Hₙ)+Eₙ，其中Hₙ=gₙ−g₀，L是背景g₀逆矩阵的Christoffel收缩。线性项始终是D^{g₀}Hₙ。

从真实字段的光滑性和非退化性，逐项证明Eₙ分量在chart.target内C∞，包括实际computedΓ、matrix inverse、真实一阶Fréchet jet及辅助协变jet。E的光滑性不是调用者输入。再消费原物理C⁰loc及同一μ₀下Dh局部统一L∞，得到Eₙ分量紧集一致趋零。

对固定全空间C∞紧支撑ψ（tsupportψ⊆该chart.target）、固定图内C∞系数A和固定方向v，逐项可积并实际证明

    ∫ ψ A Eₙ → 0，   ∫ ψ A D_v Eₙ → 0，
    ∫ ψ ρ₀ A D_v Eₙ → 0，   ∫ ψ ρ₀ Γ₀ Eₙ → 0。

ρ₀和Γ₀均为同一g₀的真实密度和连接。最后将偏导及三类Γ₀E项装配为实际 `CurvatureDifference.covariantDerivative`，其jet正是 `coordinateConnectionJet`，证明每个真实∇^{g₀}Eₙ分量的ρ₀测试积分趋零。积分与有限和交换前，全部项的可积性均已导出。

上述积分是带ρ₀系数的Lebesgue积分，测试与系数先于n固定。没有额外uniform D²gₙ、全局frame或隐藏的小误差假设。

既有精确Ricci差式包含Q(C)=Σ(Cᵃ_ae Cᵉ_bc−Cᵃ_ce Cᵉ_ba)。既有rank-one符号识别给Q=−旧B；不能把该符号专用定理不经证明用于任意jet。本批保留其负号，不宣称已取得一般二次极限或缺陷测度表达。

下一消费者须将这些分量收缩、装配L(D^{g₀}Hₙ)线性项的测试消失，证明C=L+E的二次误差替换，并从真实Ricci-flat几何数据取得完整弱Ricci总式。相空间测度、H⁻¹紧性和输运仍另行推进。
