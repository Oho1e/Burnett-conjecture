# 并行实代数片段的独立回读

日期：2026-11-15。原文SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`。本记录只覆盖原文432–463行的四项新增实代数交付，不覆盖整个F06、论文结果或人类确认。

## 冻结输入

| 源码 | SHA256 |
| --- | --- |
| `RicciSymbol.lean` | `f9cfae66918e599d0fb1fc9380118ca6f3a0c96449dc194d69bbca79fb736bf8` |
| `QuadraticDefs.lean` | `f6261b4f7d3a926ce44aa07fec7b6b367fa6e376f61ccce52c99b6a65e4e4e09` |
| `QuadraticExpansion.lean` | `fbb166ba88ed619083c283ef4c43650d9e406d199b2d65c538e244cceeca622c` |
| `NullKernel.lean`最终v2 | `972856c53a3f4c61c1f3dccb63c91ffa119b76b2a6e2dd8861af03975cd86b7d` |
| `NullQuadratic.lean` | `3dad381221de18430c5f7127fb496065b5bbcf2f06e43c5c5d2d0be91bbc78e7` |

`parallel_null_reverse`先从冻结v1实际类型和定义回读，再与原文核对；分支继续实现后，独立检查v2新增声明，并验证v1正文不变。`parallel_b_reverse`未读实现者说明，先冻结B模块数学回读，再核对原文，并额外核对主代理的NullQuadratic拼接。实现者的直接编译没有替代独立回读。

## 实际数学解释与边界

G、k均是四维实系数数组；对称性为明示分量假设，不是隐藏的度量结构字段。所有求和均遍历完整有序指标。共享收缩为 `k_ab l^{ab}`，F为该实双线性收缩减去二分之一的迹乘积；不是Euclidean正内积或复Hermitian形式。

- 完整4B展开只需G、k对称，不需Ricci核、s=0、签名或非退化。取G为原文真实逆度量分量可直接实例化，公式中的两个符号乘积、负号、系数与原文447–448一致。
- 非零ξ、s=0时，Ricci核等价q=tξ/2；原文单位余球保证ξ非零。证明选择一个存在的非零分量，未固定为某个坐标分量。它不要求G、k对称。
- 实物理/规范交叉消去要求G、k对称及前述零锥核条件，任意实v；对称性仅在相应收缩和迹公式中使用，不能从最终定理中直接删除。它证明F(k,ξ⊗v+v⊗ξ)=0，而非仅规范张量自身配对为零。
- 合并公式从实际已证B展开和实际已证核约束代入，得到B=ξ_bξ_cF(k,k)/4；未把零锥B公式作为任一分支输入。

零锥回读者还独立重建6组精确边界例。去掉s=0后核等价一般为假；去掉交叉消去中的对称性可得到F非零。ξ=0时该特定等价也成立，但保留ξ非零忠实于论文对象，未为项目增加无关泛化工作。

## 检查与裁决

零锥v1/v2的独立源编译、实际类型和全部5个公共声明的传递公理探针均退出0，仅依赖 `propext`、`Classical.choice`、`Quot.sound`。原始回读、冻结副本差异、类型、公理及反例记录见 `.project-verification/parallel-pilot/reverse-null/`，正式报告为 `REVERSE_REVIEW.md`。

B模块及合并公式的独立回读与隔离探针均通过。五份生产源码、两个实际类型/展开探针及SDK版本调用全部退出0，编译前后输入哈希一致；涉及的公共定理公理集均仅为上述三项。首次自有探针因pp.width选项错误退出1，改为format.width后完整重跑通过，失败日志保留。正式裁决为 `.project-verification/parallel-pilot/reverse-b/review-result.txt`，机器绑定为同目录 `machine-evidence.json`，类型/定义输出见 `ReverseAudit.log` 与 `ReverseNullAudit.log`。

主代理合并版本完整库构建及四个新增目标的实际类型/传递公理探针也已通过。没有 `sorry`、新增数学公理或native_decide。登记后的9个支持目标已完成统一存在性、来源及公理审计，实际退出0；[持久机器记录](../formalization/parallel-machine-evidence.json)保存对应输入。远程CI另按实际提交观察，作者数学确认仍待定，不能以本记录替代。

保留未完成项：一般极化/复Hermitian扩展、零锥物理商正性及一般Lorentz零标架桥接、协方差/测度应用和F04/F05/F07闭合。两条并行分支及合并公式不等于F06全部完成。
