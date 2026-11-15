# F06：原Ricci二次式的实混合极化

原文位置：`paper/burnett.tex`第432–463行，尤其450、452和454–457行。固定四维实坐标指标；全部收缩均对有序指标求和。使用原[实二次代数定义与对角结果](quadratic-real-algebra.md)，并在`Burnett/Algebra/RealPolarization.lean`补实混合形式。本文不把实结论称作复Hermitian扩展。

## 定义及归一化

固定实逆度量分量G、实协向量ξ。记原连接符号为c(k)，原二次式为Q_bc(k)=B_bc(k,k)。定义

\[
C_{bc}(k,l)=\sum_{a,e}\big(c(k)^a{}_{ce}c(l)^e{}_{ba}
-c(k)^a{}_{ae}c(l)^e{}_{bc}\big),\qquad
M_{bc}(k,l)=\frac{C_{bc}(k,l)+C_{bc}(l,k)}2.
\]

这里M是原B的实对称混合形式；源码先用原连接交叉积定义它，再证明与极化公式一致，没有把目标右侧作为新定义。对任意实G、ξ和实二张量k、l，固定b、c有

\[
M(k,l)=M(l,k),\qquad M(k,k)=Q(k),\qquad
M(k,l)=\frac{Q(k+l)-Q(k)-Q(l)}2.
\]

M在每一幅度槽对加法和任意实标量均线性。这些代数性质不要求ξ非零、G非退化、Lorentz签名或幅度对称。“对称”在这里交换k与l，不能误读为交换b与c。未除以2的交叉和是2M。

## 两类核上的结论

沿用s=G^{ab}ξ_aξ_b和原Ricci符号R_ξ。

1. **非特征核。** 若s≠0，且R_ξ(k)=R_ξ(l)=0，则对所有b、c，M_bc(k,l)=0。k、l分别任意量化，不只证明l=k。此结果也不需G或幅度对称。
2. **零锥核。** 若G、k、l均为实对称分量，ξ≠0、s=0，且R_ξ(k)=R_ξ(l)=0，则

\[
M_{bc}(k,l)=\frac14\xi_b\xi_c F(k,l),\qquad
F(k,l)=\sum_{a,b,c,d}G^{ac}G^{bd}k_{ab}l_{cd}
-\frac12\operatorname{tr}_G(k)\operatorname{tr}_G(l).
\]

F仍是原有有序收缩，并未换成屏幕范数。零锥结果保留原对称性与非零ξ条件，不声称任意张量/协向量上F非负。Ricci符号及F的实标量线性接口也已实际实现和审计。

## 注册与实际声明

本次登记9项主要支持目标和3项独立标量接口审计目标；它们不是新增12条原文正式结果。

| 清单ID后缀（均以polarization:开头） | 实际声明（均在Burnett.RicciSymbol） |
| --- | --- |
| real-symmetry | mixedQuadraticSymbol_comm |
| real-add-left / real-add-right | mixedQuadraticSymbol_add_left / mixedQuadraticSymbol_add_right |
| real-smul-left / real-smul-right | mixedQuadraticSymbol_smul_left / mixedQuadraticSymbol_smul_right |
| real-diagonal | mixedQuadraticSymbol_diag |
| real-polarization | mixedQuadraticSymbol_polarization |
| real-noncharacteristic-mixed | mixedQuadraticSymbol_eq_zero_of_noncharacteristic_kernel |
| real-null-mixed | mixedQuadraticSymbol_eq_physicalPairing_of_null_kernel |
| ricci-real-smul | ricciSymbol_smul |
| physical-real-smul-left / physical-real-smul-right | physicalPairing_smul_left / physicalPairing_smul_right |

中央实际类型查询覆盖新模块全部29个公共声明（2定义、27定理）；不只查看名字。源码SHA256为5993bc6169017387715a3a3e926aa4202ffff3e45ab080414e11f2ef993b7dd4。机器、独立语义核验及作者确认分别记录于[独立回读](real-polarization-review.md)和[实测报告](../formalization/f06-workflow-test.md)。

F06父项仍部分完成。复Hermitian、零标架与物理商正性、几何/测度桥接及17个编号结果的全局闭合不在本轮完成范围。作者确认与最终信任选择不由编译、代理同意或PR合并代替。
