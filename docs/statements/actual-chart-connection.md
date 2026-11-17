# 实际坐标二阶导数、全局度量连接与体积正则性

本批实现原文91–108、333–345及358–369行的必要几何依赖。文章与信任A不变；所有新增结论均为支持结果，不关闭F04、F05或主定理。新数学解释的作者确认尚未记录。

## 从实际图求导到连接自然性

ActualChartSecondJet使用真实preferred chartAt的重叠映射φ，证明其C∞性，并把H定义为实际二次Fréchet导数的基分量。H的两个下标对称由真实二阶求导定理推出；C∞在实际类型中不是解析阶Cω。

MetricJetNaturality对同一个真实切纤维双线性字段B的坐标law求导。证明只在开重叠上的函数芽使用相等，没有对图外总函数作几何解释。新jet的三项为H_bᵀGA、Aᵀ(Σp A_pb J_p)A及AᵀGH_b。ConnectionTermNaturality由真实矩阵逆与非退化性消去中间逆矩阵，取得

\[
 D\phi\,[\Gamma_{\rm new}(v,w)]
 =\Gamma_{\rm old}(D\phi\,v,D\phi\,w)+D^2\phi[v,w].
\]

A的行是旧坐标、列是新坐标。Matrix逆是矩阵逆，不是函数数组的逐项倒数。H项完整保留；调用者无须提供jet或连接变换law。

ChartVectorField的Field是真实Πm T_mM，IsSmooth是真实切丛total-space section的ContMDiff。由实际trivialization定义坐标，证明重构、变换及双向光滑刻画。对真实向量场变换law求导后，D²φ项与上述连接变换项配合，ChartConnectionNaturality证明同一纤维中的图导数一致。没有使用全局光滑标架，也没有凭TangentSpace的底层类型相等识别不同坐标。

## 全局光滑仿射度量连接

GlobalCovariantDerivative在m处取以m为中心的首选图定义实际向量∇_V W(m)。已证图间自然性保证它等于任何包含m的preferred图中的计算值。该构造不是结构中的待证结论字段。

SmoothMetricConnection从实际矩阵的det、adjugate及det⁻¹证明局部逆矩阵光滑；从开集上的实际一阶导数证明jet光滑，再证明computed Christoffel字段光滑。非退化只在有关开集内要求。GlobalCovariantDerivative据此消去中间“Γ光滑”输入，证明光滑V、W的输出是真实光滑截面。

GlobalConnectionLaws单独证明第一槽加法和函数线性、第二槽加法和常数线性、函数Leibniz法则。相关求导条件在实际点明确保留，函数求导使用真实mfderiv。坐标函数的加法、乘法只通过图内相等和开集函数芽用于求导。

ChartDifferential把真实mfderiv f作用于切向量的值与图中的Fréchet方向导数连接。ChartLieBracket通过mathlib实际mpullback_mlieBracket定理取得真实流形Lie bracket的坐标公式，没有另定义一个交换子代替它。

GlobalLeviCivita由真实Hom丛双线性求值证明B(U,W)光滑，结合标量微分桥及实际坐标相容性证明

\[
 V(B(U,W))=B(\nabla_V U,W)+B(U,\nabla_V W),\qquad
 \nabla_VW-\nabla_WV=[V,W].
\]

前式只需U/W光滑，方向V不必光滑；后式的V/W光滑条件用于实际bracket坐标运输。B的假设是全局光滑、对称、非退化，允许不定号。原文辅助Riemannian r由真实光滑、对称、正定性质实例化；得到它的全局光滑连接、度量相容及无挠性。

这里构造了具有这些性质的实际全局连接；没有另行声称已证明关于一切抽象全局连接算子的唯一性。原有系数唯一性仍按其准确范围复用。完整Lorentz signature、时间定向模型和原intrinsic cov2 Dh及物理三张量范数尚未接入。

## 底流形体积的正则性

ManifoldVolumeRegularity复用同一B的实际geometricMeasure及其首选图公式。光滑B使sqrt(abs(det G))在图内紧集有界，取得坐标紧集有限；再从真实图内紧邻域证明全局测度局部有限及M紧集质量有限。这里使用原Hausdorff、第二可数及Borel结构，不添加有限总质量条件。

B非退化时，非空开集质量严格为正；局部有限性本身不需非退化或对称性。没有把局部有限或正性作为调用者字段。仍不宣称任意maximal-atlas成员的公式或Radon性质。这是底流形dV_g，F05相空间缺陷测度μ尚未构造。

下一步是原intrinsic cov2导数与现有auxiliaryPerturbationJet的同一性、物理三张量范数、原假设到坐标一阶界，再接积分分部、弱Ricci与H⁻¹紧性。不增加uniform D²g_n假设。精确Ricci二次修正等于−旧B的符号保持。

来源、声明和独审绑定见[独立回读](actual-chart-connection-review.md)与[字节绑定](actual-chart-connection-source-bindings.json)。目标数不是完成率，整篇verified=false。PR就绪后的独立后继工作按[GOAL](../formalization/GOAL.zh-CN.md)自动推进，main最终合并仍由人类执行。
