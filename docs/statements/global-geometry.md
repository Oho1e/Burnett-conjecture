# 全局几何体积、物理收敛与实际坐标协变导数

本批补原文91–108、333–345及358–369行的必要依赖，均为支持结果，不关闭F04、F05或thm:quadratic。原文身份不变，新增解释的作者确认尚未记录。

## 底流形上的几何体积

MeasureGluing在一般可测空间上实际定义

\[
 \mu=\sum_n \nu_n|_{\operatorname{disjointed}(U)_n}.
\]

可数可测覆盖及局部交集相容推出每个覆盖成员上的限制公式；任意另一个与全覆盖相容的可测局部域也有同一公式。唯一性与存在性实际证明，不要求有限总质量或sigma有限。一般引理的相容性是显式输入。

ManifoldVolume随后在真实流形的Borel结构中消去这些中间输入：将真实chart.source/target homeomorphism转为measurableEquiv，在target外以c延拓逆图为可测总函数；运输前先限制真实坐标密度到target。由已证same-B Jacobian定理推出同一真实纤维双线性字段B的局部测度相容，从原SecondCountable抽出可数图覆盖，再实际拼接。空流形单独处理，没有新增Nonempty假设。

最终geometricMeasure B满足所有c:M的首选图chartAt c的公式

\[
 (\mathrm{chart}_c)_*(\mathrm{geometricMeasure}(B)|_{\mathrm{source}_c})
 =\bigl(\sqrt{|\det G_c|}\,dx\bigr)|_{\mathrm{target}_c}.
\]

调用者不提供覆盖、局部相容性、全局测度或最终图公式。该公式唯一确定测度，且可数子覆盖的选择不影响结果。这里“所有图”严格限于既有preferred chartAt(c:M)族，尚未给任意maximal-atlas成员的独立扩展定理。没有宣称局部有限、Radon或非零性；一般B也不要求非退化。后续需要时从真实光滑非退化字段另证这些性质。

这是底流形上的几何体积dV_g。相空间S_r^*M上的缺陷测度mu及其输运仍是F05后续任务。

## 真正的全局字段与物理C0loc

ManifoldBilinear的Field在每个实际切纤维上是连续双线性映射；IsSmooth是该字段作为嵌套Hom丛total-space section的ContMDiff。由真实光滑切丛frame求值和逆图复合，实际推出各图分量C∞/C1。纤维对称性及左非退化也通过真实frame双射推出图内属性，没有加入坐标正则或非退化结论字段。辅助r.inner是该smooth类型的真实实例。

ManifoldTensorNorm以m自身的preferred frame定义physicalNorm2 r B m。实际chart导数矩阵的可逆性由frame注入性推出，再使用同B矩阵law与完整逆r收缩，证明此长度等于任意包含m的固定preferred图中的物理norm2。它还等于inverseR⊗inverseR Gram上的实际Hilbert范数，不使用curried Hom opNorm，也不要求全局光滑frame。

ManifoldMetricSequence的LocallyUniformlyConverges明确表示：对M上的每个紧集，真实标量physicalNorm2 r (B_n-B_0)一致趋零。将固定chart.target内紧K经真实逆图送到M紧集，结合同一r在K上的统一范数比较常数C>0，实际推出全部坐标分量的一致收敛。chart_conditions_of_global将global smooth/symmetric/nondegenerate字段和该收敛条件组合成所需C1、非退化、邻域对称及分量收敛条件；没有调用者坐标hconv前提。

本批只证明这一明确物理范数C0loc表述到坐标条件的方向，没有声称与另一个尚未定义的bundle compact-open拓扑双向等价。完整Lorentz signature、时间定向及原intrinsic Dh条件的全部实例化仍未完成。

## 实际坐标协变导数

CoordinateCovariantDerivative从真实向量场定义

\[
 \nabla^\Gamma_VW(x)=DW(x)[V(x)]+\Gamma(x)(V(x),W(x)).
\]

实际证明第一槽对标量函数线性、第二槽Leibniz法则，以及用mathlib真实LieBracket表示的零挠关系；可微条件在实际求导处显式保留。对cov2张量的诱导操作从真实标量配对及两个连接扣除项定义，其基向量分量等于既有covariantJet及同一r/g1-g0的auxiliaryPerturbationJet。

AffineConnection进一步构造真正的三线性cov2Differential，证明变向量U/W配对的三项求导和两项消去，取得诱导导数的张量性、computed metric连接的真实度量相容和零挠，以及同一扰动的辅助jet恒等式。它们是实际局部coordinate affine operator；尚未构造原文全局D=Levi-Civita(r)，也未证明输出光滑截面的全局闭包。

LeviCivitaUniqueness从真实非退化纤维形式的逆推出：对同一g/dg，零挠且metric-compatible的系数必等于实际computedConnection。唯一性不替代存在性或图间相容性。

## 保留非线性二阶项的代数变换

ConnectionCoordinateChange取A的行为old、列为new，H有一个old上指标及两个new下指标。令Gamma_p为旧连接矩阵、J_p为旧度量一阶jet，按显式公式构造

\[
 K_b=\sum_p A_{pb}\Gamma_p,\quad
 \widetilde\Gamma_b=A^{-1}(K_bA+H_b),
\]
\[
 \widetilde J_b=H_b^TGA+A^T(\sum_p A_{pb}J_p)A+A^TGH_b.
\]

实际证明A可逆时度量相容性保持、H下槽对称时零挠保持，并由上述唯一性取得真实逆矩阵下的Christoffel恒等式。H项没有被省略。此处是显式affine二阶jet代数；A/H/新jet与实际chart Jacobian/Hessian/Fréchet导数的识别仍OPEN，不能将此代数定理直接称为全局自然性。

## 当前剩余

后续须补实际图二阶链式法则、全局LC及其诱导cov2导数与当前computed jet的同一性，再接原intrinsic Dh物理界与真实几何volume。按消费者需要补体积局部有限性及更广图族；保持较大紧邻域上ae到点态的已有论证。没有新增uniform D²g_n界或global smooth frame。

此后继续固定测试积分分部、弱Ricci识别、H⁻¹紧性及F05真实PDO/正性/共同缺陷测度。精确二次修正=−旧B符号保持。全部123声明及31项登记的来源与独审身份见[复核](global-geometry-review.md)和[冻结绑定](global-geometry-source-bindings.json)。整篇verified=false。
