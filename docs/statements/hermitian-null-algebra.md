# F06：复Hermitian代数与零锥物理正性

原文位置：`paper/burnett.tex:338,430–465`。本文件说明本轮新增实际声明；中央目标审计、独立反向核验和新数学解释确认分别记录，不以本说明代替这些证据。

## 对象与约定

指标为四个有序坐标指标。逆度量G和协向量ξ取实数，复振幅k满足转置对称k_ab=k_ba；这不是把振幅本身要求为Hermitian矩阵。配对按原文338行对第一槽线性、第二槽共轭线性。

原连接符号实际复化后形成有序交叉积C，定义H_B(k,l)=[C(k,conj(l))+C(conj(l),k)]/2。物理形式直接取

\[
H_F(k,l)=\sum_{a,b,c,d}G^{ac}G^{bd}k_{ab}\overline{l_{cd}}
 -\tfrac12\operatorname{tr}_G(k)\overline{\operatorname{tr}_G(l)}.
\]

代码证明这些原定义与实/虚部的实配对之间的桥接，并非把所需结论定义成新形式。`ComplexPolarization.lean`中的加法、复标量及共轭对称声明给出实际Hermitian形式；嵌入实振幅时恢复已有实混合形式及原B的对角。

## 已实现的数学内容

1. 复Ricci符号为零当且仅当振幅实部和虚部各属于原实Ricci核。
2. s≠0时，同一复Ricci核中任意两振幅的H_B为零。
3. ξ≠0、s=0，G、k、l 对称且 k、l 均属于该 ξ 的同一复 Ricci 核时，H_B,bc(k,l)=ξ_bξ_c H_F(k,l)/4。H_F 在该核内的振幅与实际规范张量之间的交叉配对为零。
4. 实/复纯规范张量均实际属于Ricci核；在零锥核中，对两个振幅分别加任意规范张量不改变物理配对。
5. 标准逆度量η=diag(-1,1,1,1)、ξ=(-1,1,0,0)下，核幅度有明确的“规范＋无迹屏幕”分解；H_F(k,k)=2(|k_22|²+|k_23|²)，零物理范数恰对应规范张量。任意两个复屏幕参数确实产生对称核幅度。
6. 对标准η的任意非零零协向量，先由零条件推出ξ_0≠0，再以显式规范变换清零振幅的时间行；核约束使迹为零，原实F成为剩余分量平方和。因此正性和零空间判别不需要先假设指定零方向。
7. 对实际基变换E，证明G=EηEᵀ、ξ'=Eᵀξ、k'=EᵀkE之间的迹、全有序收缩、Ricci核和物理配对变换；基的注入/满射真正用于将规范向量拉回原坐标。
8. 在仅含基双射和逆度量正常形的`TensorFrame.LorentzFrame G`证书下，一般G的零锥核上H_F(k,k)虚部为零、实部非负，而且H_F(k,k)=0当且仅当k为实际复纯规范张量。证书不含正性或核结论。

## 模块与主要实际声明

| 模块 | 主要声明或作用 |
| --- | --- |
| `ComplexPolarization.lean` | `hermitianQuadraticSymbol_eq_zero_of_noncharacteristic_kernel`、`hermitianQuadraticSymbol_eq_physicalPairing_of_null_kernel`及原定义桥接 |
| `NullScreen.lean` | `NullScreen.kernel_decomposition`、`physicalPairing_eq_screen` |
| `HermitianScreen.lean` | 通用规范核成员性、双槽代表不变及标准屏幕的复分解 |
| `MinkowskiNull.lean` | 任意非零η-null ξ的`physicalPairing_self_nonneg`和`physicalPairing_self_eq_zero_iff_pureGauge` |
| `TensorFrame.lean` | 实收缩及核协变、真实基证书 |
| `ComplexFrame.lean` | 复收缩及核协变、复基变换的注入/满射 |
| `LorentzPhysical.lean` | 一般证书下实物理正性及实际规范零空间 |
| `LorentzHermitian.lean` | 一般证书下复物理正性、实对角和实际复规范零空间 |

所有实际名字以中央目标清单及独立类型查询为准。上述支持结果仍不等于17项论文正式结果中的任意一项已完成。

## 两参数分类与归一化

`MinkowskiNormalize.exists_normalizing_frame`由实际Lorentz反射构造标准η任意非零零方向的归一化标架，分母非零均已从零条件和非零条件推出。`NullFrame.exists_normalized_frame`再将它与给定的一般Lorentz基复合，不把归一化当作新的最终假设。

`PhysicalQuotient.coordinates`选择只依赖G、原基及ξ的同一标架，对所有振幅使用同一复线性映射到ℂ×ℂ。实际证明同坐标当且仅当两幅度相差纯规范；任意两个复参数都由原坐标中的真实对称Ricci核振幅实现；并且

\[
H_F(k,l)=2(a\overline c+b\overline d).
\]

这些双向、满射及线性合同表达物理类的两个自由复参数，没有只证明维数上界，也不需要预先假设某个商对象已存在。代码未额外声明某种未构造的商类型的finrank定理。

## 当前衔接边界

二维分类、实际点态归一化与全部两参数的原坐标实现已按上述双向合同证明。一般Lorentz几何对象应在后续数据建模中实际提供或推导点态标架证书；本轮不将任意实对称G误当Lorentz签名。当前点态选择不声称关于位置、频率的全局光滑性或一致估计，V06等消费者仍需自己的合同。

测度、正Hermitian协方差的测度配对、子列、二次定理装配及输运主线仍待推进。2026-11-16用户针对上述点态复代数及二维分类明确选择“委托你和独立代理确认（推荐）”。主代理结合实际声明与独立冻结源码/真实类型回读确认该局部对应；这不是用户或作者本人逐行审阅Lean。确认版本和源码绑定见本轮复核记录。用户选择A另行确认最终数学依赖闭合和三基础公理政策。
