# 固定测试下的局部弱导数

对应原文376–388行的线性弱消失支持。模块 `Burnett.Analysis.LocalWeakDerivative` 保留完整19项声明，选择6个语义端点登记。父结果、F04/F05及全文仍OPEN；作者确认待记录。输入身份与独审见[共同绑定](intrinsic-dh-geometry-source-bindings.json)及[复核](local-weak-derivative-review.md)。

U是实际四维坐标开放域，ψ固定、全空间C∞且紧支撑，tsupportψ⊂U。序列fₙ和固定系数a只需在U内C∞，图外总函数取值任意。ψ、a、方向v/w和图均先于n固定。

通过U外ψ的零germ，实际证明ψf、ψa的全空间光滑和紧支撑；逐项证明可积后，作一次或两次积分分部。如果fₙ在U内每个固定紧集一致趋零，则

    ∫ ψ a D_v fₙ → 0，   ∫ ψ a D_v D_w fₙ → 0。

二阶积分分部将D_vD_w移为测试上的D_wD_v，没有额外使用未证的导数交换或统一二阶导数界。

原几何实例从同一r物理C⁰loc收敛及实际光滑字段，导出真实图分量gₙ−g₀的一、二阶测试积分趋零；调用者无需另供坐标收敛。这一线性步骤本身不需要Dh界。

同一g₀的ρ₀=√|detG₀|在图内的C∞由真实非零行列式证明；Γ₀是同一g₀的实际computedConnection。在原对称非退化背景中由既有识别将其读为Levi-Civita系数。最终取得ρ₀Γ₀∂hₙ及ρ₀a∂²hₙ的固定测试消失。

这些实际Lean类型写作带ρ₀系数的Lebesgue积分；此处没有新增withDensity积分等式。不能把n依赖的gₙ逆系数直接代入固定a，不能据此宣称全weak*L∞、weakL²或H⁻¹强收敛。原真空Ricci总测试式、非线性二次项及精确−旧B修正仍需实际装配。
