# 全局几何支持结果的独立反向核验

本批9源123公开声明（26定义、2abbrev、92theorem、3lemma）已分别独立回读完整源码、实际类型和传递公理输出，全部实际exit0，仅三基础公理。计数包括同一行带属性的声明。独审者未参与所审新源的正向证明；库依赖的早期作者身份不冒称对该新源的独审缺席。

| 模块 | 声明数 | 独立报告SHA256 |
| --- | --- | --- |
| LeviCivitaUniqueness | 4 | `245bf25d2c1f73e6f882d17f430f63dd9c5835629640fcef9c22397282169b3b` |
| MeasureGluing | 5 | `16c106b31ad7134d3d2c5362bf75ee236be9a083bbd426848065341146768242` |
| CoordinateCovariantDerivative | 20 | `0e97c52bc369153f7e73a1d940e769dfd3cf9378afce44fef25c046e29426022` |
| AffineConnection | 23 | `49a84c2fc94e60379184e3bf26214b0175f1a8eb28a196bcc4d2b387cabb2050` |
| ManifoldBilinear | 14 | `a460343aaa6f6843847923a96f56be722d5ddfa703653775c312f02da0007f59` |
| ManifoldVolume | 26 | `6bd87159c9f05101407cd70ff7e34ad2471861a70c8300b0f9031bb6d2670dcf` |
| ConnectionCoordinateChange | 15 | `8688147f170de923cda545eadd6857b331b5690cdaea6d3fe6034d5755b0b486` |
| ManifoldTensorNorm | 12 | `3d5f44b0cab6919bfcc21915087f0e96a3b8c5010d23b4beb2c68a9f022098eb` |
| ManifoldMetricSequence | 4 | `b6c39e315d52c034d6be8db3a6ac5ab1671c33b0c06397af6dfcdc3c170bdce4` |

准确数学范围见[数学说明](global-geometry.md)，source/report/receipt字节绑定见[JSON](global-geometry-source-bindings.json)。

复核重点包含：empty M及图外默认值、真实same-B相容链、可数覆盖的实际存在与选择无关；真实向量场配对导数/两扣除项/LieBracket符号；物理Hilbert范数及actualframe可逆性；M紧集C0loc到固定图分量收敛中同一r和不依赖n的常数。

非线性变换额外以G=[1,1;1,2]⊕I区分真正矩阵逆与逐项倒数，并检验A=I/J=0/H011=1时非零连接项及新jet项。最终生产源码的Christoffel逆明确带Matrix类型；早期私有类型/自动化失败保留历史身份，未混入接受回执。

这些核验不宣称任意maximal-atlas公式、Radon性、actualchart二阶导数识别、globalLC或原完整admissible条件闭合。体积对象是底流形dV_g，缺陷mu仍未构造。新作者确认待记录；整篇、F04/F05保持OPEN。

完整285目标/93源候选的机器检查、实际main组合CI和工件独审在最终版本另取新回执；不沿用旧254绿色。中央工程复核与每源数学独审、同账号GitHub操作与跨账号Approve分别记录。
