# 辅助度量、物理张量范数与局部 L∞ 控制

本批服务锁定原文91–105和352–389行。它构造局部坐标中的实际辅助连接、物理协变张量范数、正密度测度及连接误差的真实L∞模型；原流形图拉回、混合型误差张量的物理范数和完整F04仍须另证。父命题`thm:quadratic`不因本批支持结果而关闭，整篇仍为development。

## 真实范数与指标

`GramCoordinateBound`定义实际能量`gramEnergy G x = xᵀGx`及其平方根，证明与由正定矩阵构造的Hilbert范数相等，并用该内积中的Cauchy–Schwarz证明

\[
 |x_i|^2\le (G^{-1})_{ii}\,x^TGx.
\]

`CovariantTensorNorm`令R为**协变**辅助度量矩阵，S为其实际矩阵逆。二、三阶协变张量的能量分别为

\[
 Q_2(H)=\sum_{i,j,a,b}S_{ia}S_{jb}H_{ij}H_{ab},\qquad
 Q_3(T)=\sum_{i,j,k,a,b,c}S_{ia}S_{jb}S_{kc}T_{ijk}T_{abc}.
\]

模块实际证明Gram矩阵为S⊗S及(S⊗S)⊗S，正定性和逆也有证明。`flatten2/3`明确使用行优先指标；mathlib的`Matrix.vec`需要转置，不能省掉。范数是`Real.sqrt Q₂/₃`，不是原有Pi sup范数的改名。坐标界使用R的对角：

\[
 |T_{ijk}|\le\sqrt{R_{ii}R_{jj}R_{kk}}\,|T|_r.
\]

R对角在固定紧集上连续，实际导出统一常数C>0，使所有张量满足`‖T‖Pi ≤ C * norm3 R T`；C不随序列编号n或T变化。二阶版本同样已实现。反向的物理范数控制、基变换自然性不包含在这个比较结论中。

## 实际辅助导数与较大邻域

`AuxiliaryConnection.auxiliaryPerturbationJet r g₀ g₁`实际计算

\[
 (D^r h)_{bcd}=\partial_bh_{cd}
  -\Gamma(r)^e{}_{bc}h_{ed}-\Gamma(r)^e{}_{bd}h_{ce},\qquad h=g_1-g_0.
\]

Γ(r)由r的实际逆与Fréchet分量一阶导数构造。r的C¹分量和紧性给统一连接界，负同一Γ的代入反解raw一阶jet；不把Dᵣ直接等同于坐标偏导，也不把Γ界作为额外原文前提。

`LocalAeBound`在开O和K⊆O⊆S下，将S限制测度上的a.e.界提升为K逐点界，前提是范数在O连续且O内非空开集正测。特别地，K本身可以是零测集。不能只用μ.restrict K上的a.e.界推K每点界。真正F值的连续函数在可测紧集上属于L∞，不要求μ(K)有限；另一个任意p结论只处理标量范数并显式要求有限质量，两者没有混用。

## 局部连接误差的实际组合

`AuxiliaryPhysicalBound`先由R正定推实际双线性r的非退化及对称。对每个紧S⊆U，假设同一序列的物理`norm3(Dʳhₙ)`在μ.restrict S上的实际`eLpNorm ... ∞`有统一界。μ只需对U内非空开集正测，不要求域外支撑条件。

最终组合定理从K⊆U及K紧**构造**S，使K⊆interior S⊆S⊆U，然后依次得到物理到坐标界、K上逐点辅助导数界、raw jet的一致界和真实连接误差Eₙ的一致趋零。它也实际构造每个Eₙ在μ.restrict K上的`MemLp ... ∞`与`toLp`类，证明这些真实L∞元素的范数趋零；调用者无需另给MemLp或指定代表。`ConnectionErrorLInfinity`实现了所需连续性与L∞构造。

所用gₙ、g₀、r的局部分量C¹来自原文光滑性；没有加入统一二阶导数估计。gₙ的非退化、邻域对称以及分量的一致收敛仍显式来自原几何数据。输出L∞目前使用连接数组的Pi sup范数；混合(1,2)张量的物理r范数尚需识别。

## 正密度与坐标体积

`PositiveDensity`针对实际`μ.withDensity w`建立限制测度的零集、a.e.和L∞比较；局部可测及正性须由实际密度给出，不以假设互相绝对连续来代替该构造。`RiemannianVolume`用实际

\[
 \rho_R(x)=\sqrt{\det R(x)},\qquad d\mu_R=\rho_R\,dx
\]

构造正定R的坐标测度，给出局部可测、正性和正开集性质，再将上述物理组合实例化到R=metricComponents r。这里的测度由明确密度定义，不宣称已经证明原流形体积在图下的推前就是它。

## 证明与完成的范围

实际声明及冻结输入见[源码绑定](auxiliary-r-control-source-bindings.json)，独立回读见[复核记录](auxiliary-r-control-review.md)。机器检查绑定实际候选及日志；开发合并不产生作者确认或整篇标签。

后续从原流形上的r、D=∇r和体积构造其图内表示，补张量范数/局部C⁰的自然性及混合误差物理范数，再推进固定测试积分分部、弱Ricci识别和H⁻¹紧性。F05的实际PDO一致界、趋零误差正性及共同测度构造仍开放；已证的局部范数工具不能代替它们。
