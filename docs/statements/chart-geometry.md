# 真实流形图、张量范数与几何坐标体积

本批继续原文91–105、333–340、352–389行的必要依赖。原文第34行宏和第337行明确`dV=dV_g=√|det g| dx`；`|·|r`是辅助正定度量的张量长度。两者分别建模，不能将Lorentz g代入旧`√det R`正定密度。本批均为支持结果，不关闭F04或`thm:quadratic`，新增人类数学确认待记录。

## 张量长度和实际误差

`MixedTensorNorm`对一个上指标、两个下指标的数组E实际定义

\[
 |E|_r^2=\sum_{a,b,c,d,e,f}R_{ad}(R^{-1})_{be}(R^{-1})_{cf}
 E^a{}_{bc}E^d{}_{ef}.
\]

Gram矩阵为`(R⊗R⁻¹)⊗R⁻¹`，正定性、逆、真实Hilbert范数对应、变系数连续性及双向紧集比较有证明。比较常数从实际R、R⁻¹和有限收缩系数的连续性与紧性导出，不是额外的范数等价字段。R=4I时纯分量的此范数为1/2，全协变三阶范数为1/8；不得混用。

`TensorCoordinateChange`对可逆A（行old/列new）实际构造`Rnew=AᵀRA`和协变二、三张量的全槽拉回，证明能量及norm2/norm3严格不变。实际Kronecker、flatten、逆消去及一般Gram等式均在证明中完成。这里T是协变张量，不将raw偏导在非线性图下直接视为张量；没有使用Hom的opNorm替代Hilbert张量长度。

`MixedConnectionError`把已有真实连接误差E的一致趋零接到物理(1,2)范数，实际构造标量`|E|r`的限制测度Lp∞元素并证明范数趋零。它不假设尚未构造的bundle-valued normed Lp空间。`LorentzConnectionError`进一步使用固定背景g₀的真实`√|det g₀| dx`；从g₀在U内非退化通过实际BilinForm.toMatrix推出密度非零，局部物理Dʳh界、E结论及实际Lp元素都使用同一g₀测度，不随n改变。

## 从真正切丛到一个图

`ManifoldMetric`输入实际四维smooth manifold及mathlib的`Bundle.ContMDiffRiemannianMetric`。模型/度量两个abbrev也已核签。`tangentFrame`使用首选切丛平凡化的逆线性映射，底点由同一`chart.symm`给出，未利用TangentSpace与模型空间的defeq冒用恒等映射。它被证明等于真实逆图的mfderivWithin。

r.inner在该frame两向量上的求值实际是光滑标量截面；沿真实逆图复合得到chart.target上分量ContDiffOn∞，并给出C1接口。注入性来自实际连续线性等价，故正定、对称和非退化也在真实图内推出。没有注册toCore/RiemannianBundle重选现有范数，没有要求域外总延拓非退化或光滑。`ManifoldConnectionError`真实消费此r图内数据，消除单独输入r的C1与PosDef前提；其g₀/gₙ及物理导数假设仍明确是坐标数据。

## 同一字段的两张图

`ManifoldMetricTransition`令φ为实际`chart_c.symm.trans chart_d`。由真实切丛cocycle得到frame_c=frame_d∘Dφ，再识别同一个底点，证明任意实际纤维连续双线性字段B的两套坐标满足

\[
 G_c(x)=A(x)^T G_d(\phi(x))A(x),\qquad A=D\phi.
\]

B不必正定、对称或在底点方向光滑；这些是点态代数身份。矩阵law使用真实canonical basis和BilinForm.toMatrix_comp，不把该law作为假设。r.inner是实际实例，得到同一r的两图测度相容。

`ChartVolume`从真实矩阵拉回证明正定辅助密度的Jacobian公式，再用实际HasFDerivWithinAt、InjOn和限制测度证明推前；实际图版本的C1由atlas提供。其computed-pullback版本无hR假设；任意已有R/S的消费者仍显式需要已建立的tensor关系，不能混称。

`LorentzVolume`独立定义真正`√|det G|`密度、局部可测和非零性、ae滤子及∞半范数转移，以及同样的Jacobian推前。`ManifoldLorentzVolume`将上述同B的已证矩阵law用于绝对行列式密度，在真实chart overlap证明`φ_*(μc|source)=μd|target`，不要求B正定、不假设ρ或measure等式。因此本批已包含原dV_g形式的**局部**图相容性，不只是辅助r的版本。

## 准确的剩余任务

尚未构造全局M上的几何volume及其chart推前识别；局部相容并不自动给出该构造。原内在Levi-Civita D与computedΓ的自然性、原全局Lorentz g₀/gₙ及其C⁰/导数假设到当前坐标接口的全部实例化也未完成。没有把D=∇r改名为raw jet或把当前局部消费者称为原admissible已闭合。

之后继续固定测试积分分部、弱Ricci识别、H⁻¹紧性及F05真实PDO/正性/共同测度；精确二次修正=−旧B的符号保留。无新增统一D²gₙ界，不要求全局光滑标架。实际版本与注册目标见[源码绑定](chart-geometry-source-bindings.json)，独立回读与角色见[复核](chart-geometry-review.md)。全篇verified仍为false。
