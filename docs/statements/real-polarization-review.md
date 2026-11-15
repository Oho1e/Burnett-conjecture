# F06 实混合极化：冻结源码独立反向核验

日期：2026-11-15。角色：未参与正向构造的独立反向核验代理。

最终结论：**冻结版本的局部独立语义核验通过。** 已从实际源码及中央重要定义 `#print`、全部公共声明 `#check @` 输出独立回读，未发现本轮实混合交付的系数、指标、量词或假设缺陷。中央实际类型/公理查询退出0，29项公共声明齐全且各自传递公理均仅标准三项。本代理没有亲自运行 Lean、公共 Lake 或CI；以下明确区分独立读取的机器输出和本代理的数学语义判断。

## 1. 独立性与实际操作

先从锁定原文430–466行及核约定414–428行独立写出 `source-specification.md`，再收到本轮冻结路径和SHA。随后先对工作源码与冻结快照分别计算SHA，均一致，才完整读取实际327行代码及重要导入定义；没有阅读正向自审、forward 输出结论或实现摘要。新声明的普通数学含义来自实际定义与签名，随后与自己先存的原文规格比较。

未改正式源码、scope、目标注册、Git、原文、工具链或依赖；只写本 `reverse/` 目录的数学规格与复核记录。未运行 Lean。随后读取协调者独立生成的中央实际类型/公理输出及查询源码，核实重要定义、全部类型与公理集合；未以正向实现者概括代替。先完成类型级判断，最后才读取中央普通数学说明，检查其是否准确表达已独立读出的命题。

## 2. 输入绑定

以下SHA256均由本代理在第二阶段实际本地计算，原文身份也与第一阶段一致：

| 输入 | SHA256 |
| --- | --- |
| `paper/burnett.tex` | `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e` |
| `Burnett/Algebra/RealPolarization.lean` | `5993bc6169017387715a3a3e926aa4202ffff3e45ab080414e11f2ef993b7dd4` |
| `.project-verification/slice-workflow-test/forward/frozen-v1/RealPolarization.lean` | `5993bc6169017387715a3a3e926aa4202ffff3e45ab080414e11f2ef993b7dd4` |
| `Burnett/Algebra/RicciSymbol.lean` | `f9cfae66918e599d0fb1fc9380118ca6f3a0c96449dc194d69bbca79fb736bf8` |
| `Burnett/Algebra/QuadraticDefs.lean` | `f6261b4f7d3a926ce44aa07fec7b6b367fa6e376f61ccce52c99b6a65e4e4e09` |
| `Burnett/Algebra/QuadraticExpansion.lean` | `fbb166ba88ed619083c283ef4c43650d9e406d199b2d65c538e244cceeca622c` |
| `Burnett/Algebra/NullKernel.lean` | `972856c53a3f4c61c1f3dccb63c91ffa119b76b2a6e2dd8861af03975cd86b7d` |
| `Burnett/Algebra/NullQuadratic.lean` | `3dad381221de18430c5f7127fb496065b5bbcf2f06e43c5c5d2d0be91bbc78e7` |
| `lean-toolchain` | `42779d67b81608af8a12aa4328d2ab47ca201925b3b2bd68369587b5340bb434` |
| `lake-manifest.json` | `9de3b9d4ed07859ef9b086b79a49884daffcea2db2340514eb013242fca7aeaa` |
| `lakefile.toml` | `89aa753ae1715bf8d34bd31b94480fa2776fc22e85a802d2743f6ef92ded3e9e` |
| `.project-verification/slice-workflow-test/central/ActualTypes.lean` | `93198c1f3697c0ef06b6562d5bec71d05a7c028ec6e5f280aed62036bddb6eb4` |
| `.project-verification/slice-workflow-test/central/actual-types-and-axioms.log` | `7e0217ebe02a221f984824db990c3e2a9397aab32895aa22569f5df0c7095de2` |
| `.project-verification/slice-workflow-test/central/actual-types-receipt.json` | `4eb035a28887350522cd559c2472b0fdeb261ab764a85a06b6ab83bf734f4ce0` |
| `docs/statements/real-polarization.md`（待用户/作者确认的解释版本） | `de1ca6bda24b85980fe45968869841696bac314187c83ddd8eeb63ad60d19edc` |

第一阶段原文规格路径 `.project-verification/slice-workflow-test/reverse/source-specification.md`，SHA256 `ab7be3fcc1ca84fb623dbea75cada47f31e010cbc72a594ebedfb9014f10a01a`。本核验覆盖指定局部交付，不是全论文或全部F06的独立范围清点。

## 3. 从实际定义独立读出的对象

`RicciSymbol.lean:14–18` 将 Index 固定为 `Fin 4`，Covector 为四个实分量，Tensor2 为四乘四实分量函数。矩阵不是自带对称性/非退化性的结构；要用对称性时定理必须显式列出。`r • k` 和 `k+l` 是实函数空间逐分量运算，没有复标量或复共轭。

`raiseCovector`、`raiseSecond` 确实以给定 gInv 收缩升指标；`metricTrace`、`contracted` 与 `symbolNorm` 分别就是原文 t、q、s。`ricciSymbol` 是原文416行的 `1/2(sk+ξξt−ξq−qξ)`，`connectionSymbol` 是原文434行的 `c(k)`。`quadraticSymbol` 保留全部有序 a、e 取值及两个原乘积的相减顺序，见 `RicciSymbol.lean:65–76`。

新 `connectionCrossSymbol`（11–15行）独立读出为

\[
C_{bc}(k,\ell)=\sum_{a,e}\left(c(k)^a{}_{ce}c(\ell)^e{}_{ba}-c(k)^a{}_{ae}c(\ell)^e{}_{bc}\right).
\]

原文435的四个连接符号的每个指标位置逐一相同；没有把第一乘积错成另一种缩并，也没有颠倒第二乘积的符号。`mixedQuadraticSymbol`（19–22行）独立读出为

\[
B^{\rm mix}_{bc}(k,\ell)=\frac{C_{bc}(k,\ell)+C_{bc}(\ell,k)}2.
\]

这是由原连接符号构造的对称混合形式。既没有直接把期望零锥结论定义为新B，也没有以一个无关的二次形式替代原B。

`QuadraticDefs.lean:13–22` 中 `tensorPairing=Σabcd g^{ac}g^{bd}k_ab ℓ_cd`，`physicalPairing= tensorPairing−tr_g(k)tr_g(ℓ)/2`，故真实F正是原文457的实双线性延伸。全部有序指标保留；没有只求和 a≤b，没有少掉对称张量非对角重数。

## 4. 逐组声明的普通数学含义与核对

| 实际源码声明/行 | 反向读出的数学命题 | 与独立原文规格比较 |
| --- | --- | --- |
| `mixedQuadraticSymbol_comm`，118–122 | 固定 g、ξ、b、c，交换任意两幅度不变 | 符合。这里交换的是幅度，不是宣称交换b、c；不需核条件或对称性 |
| `mixedQuadraticSymbol_add_left/right`，124–138 | 对每个幅度槽分别可加 | 符合。对所有实矩阵与实幅度成立 |
| `mixedQuadraticSymbol_smul_left/right`，140–154 | 每个幅度槽分别满足 B(rk,ℓ)=rB(k,ℓ)、B(k,rℓ)=rB(k,ℓ) | 符合。r显式为实数，不需核条件 |
| `mixedQuadraticSymbol_diag`，157–161 | Bmix(k,k)=原quadraticSymbol(k) | 完整对角桥接，符合原文Q；并非只核中特例 |
| `mixedQuadraticSymbol_polarization`，165–174 | Bmix(k,ℓ)=[Q(k+ℓ)−Q(k)−Q(ℓ)]/2 | 符合，二倍交叉的系数正确；这是已陈述的桥接命题，不是第二个任意定义 |
| `ricciSymbol_add/smul`，178–189 | 原Ricci符号对幅度实线性 | 符合；源层未把“k+ℓ在核”藏成额外消费者假设 |
| `mixedQuadraticSymbol_eq_zero_of_noncharacteristic_kernel`，193–206 | 同一g、ξ有s≠0；任意k、ℓ各自满足所有分量Ricci核约束，则每个b、c的Bmix=0 | 符合原文452中的全部混合项。两幅度独立量化，既非仅k=ℓ，也非只给一个预选规范幅度 |
| `tensorPairing_comm`、`physicalPairing_comm`，221–253 | 若gInv对称，则原缩并及F交换任意两幅度不变 | 符合；幅度不必先对称或在核 |
| `physicalPairing_add_left/right`、`physicalPairing_smul_left/right`，255–299 | F对两实幅度槽各自线性 | 符合，双线性无需核条件或gInv对称 |
| `mixedQuadraticSymbol_eq_physicalPairing_of_null_kernel`，303–325 | 对称gInv、对称k和ℓ，非零ξ，s=0，k与ℓ各自在同一Ricci核，则 Bmix_bc(k,ℓ)=ξ_bξ_c F(k,ℓ)/4 | 符合原文454–457的实极化；1/4和F中的1/2均正确 |

辅助的trace、q、connection和ordered-cross逐槽线性声明，均对上述实际原定义陈述，没有替换对象。源码中无参数化section变量、额外typeclass参数或假设束。已核中央输出中全部 `#check @` 的实际完整类型，未发现隐式加强参数；没有把目标结论藏入新结构字段或class实例。

中央日志1–47行实际打印Index、Tensor2、Covector及原c、Ricci、tensorPairing、F、新C、M的定义，逐项对应本报告第3节。103–137行为M的交换、双线性和桥接类型；147–155行为任意双核幅度非特征消去；156–179行为原缩并/F的交换及实双线性；180–194行为零锥混合公式与全部真实前提。两条核心定理的实际类型没有比源码或本报告多出假设，也没有丢失对独立k、ℓ和所有b、c的量词。

## 5. 假设、量词与依赖接缝

非特征定理明确使用同一个 gInv、ξ；k和ℓ分别量化，分别要求 `∀ a b, ricciSymbol ...=0`；b、c也独立全称量化。没有混入不同频率的两个核。无需 ξ≠0 的额外参数，因为 s≠0 已排除ξ=0。没有要求Lorentz签名、非退化性、逆矩阵对称或幅度对称，这是允许的较强纯代数推广，仍涵盖原文实Lorentz情形；原核约束足够，不是漏掉论文必要条件。

零锥定理显式列 gInv、k、ℓ 的对称性，`ξ≠0`、`s=0`及各自所有核分量。两个幅度均必须在核；不能拿此结论宣称一幅度在核、另一幅度任意时同一公式成立。不存在幅度正性、规范代表或F非负前提，也没有以Bmix=0或目标零锥等式本身为输入。

原文的ξ非零由单位余球语境保证；本局部定理保留非零参数，没有增加单位余球限制。零锥公式本身可另覆盖ξ=0的平凡情形，但本轮保留原文非零条件完全准确。无需Lorentz签名/非退化性，是局部代数公式的合法推广；几何解释仍需后续桥接。

零锥混合公式调用既有 `NullQuadratic` 的真实对角公式，其假设是逆矩阵与幅度对称、ξ非零、s=0和原核约束；本模块对k、ℓ及其和全部提供这些相同假设。`physicalPairing_comm` 使用显式gInv对称性，故没有把非对称配对误当成对称配对。此处无额外未证数学接口。

## 6. 系数与非零幅度独立核对

除了逐项比较源码与原文，手工从原c乘积式核一次非零例：取 `gInv=diag(−1,1,1,1)`，`ξ=(1,1,0,0)`；k、ℓ只在第2、3指标的屏幕分块非零，分别为

\[
k_{\rm scr}=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
\ell_{\rm scr}=\begin{pmatrix}1&2\\2&-1\end{pmatrix}.
\]

两幅度独立且非零，t=q=s=0，所以都在同一原Ricci核。按全部有序指标直接缩并，`F(k,ℓ)=1·2+1·2=4`；`F(k,k)=2`、`F(ℓ,ℓ)=10`。直接代原连接乘积，在b=c=0时trace乘积为零，而第一乘积为屏幕矩阵乘积迹的1/4，故 `C00(k,ℓ)=C00(ℓ,k)=1`。因此 Bmix00=1，恰等于 `ξ0²·4/4`；未除2的交叉和为2，恰等于 `ξ0²·4/2`。

同例原对角式给 `Q00(k)=1/2`、`Q00(ℓ)=5/2`、`Q00(k+ℓ)=5`，故极化商 `[5−1/2−5/2]/2=1`。这同时暴露少掉非对角重数或混淆归一化交叉项会造成的系数错误。该有限分量手算是局部复核补充，不代替通用Lean定理或机器构建。

齐次性也一致：固定g、ξ，Bmix对k、ℓ分别一次；固定k、ℓ，对ξ二次；零锥右端具有相同次数。

## 7. 结论边界与实际机器证据

最终独立语义结论为：本轮可消费交付确实覆盖原B的实对称混合交叉、对角/极化桥接、非特征核任意双幅度混合消去、零锥混合B公式，以及Bmix/F所需实双线性。实际类型和重要定义已与源码、锁定原文及第一阶段独立规格交叉核对，未发现需要改数学陈述或追加假设的缺陷。

机器事实来自协调者独立执行的 `lake env lean .project-verification/slice-workflow-test/central/ActualTypes.lean` 实际输出；回执绑定本轮冻结源码SHA，日志196行记录 `EXIT_CODE=0`。本代理重新从源码提取29项公共声明，与查询源中的29项 `#check @` 及日志中的29条 `#print axioms` 结果逐集合比较，三个集合完全一致；私有证明辅助 `rp_sum_comm` 不冒充新增公共结果。29条实际公理集合均恰为 `{propext, Classical.choice, Quot.sound}`，未见sorryAx、额外数学公理或native_decide。完整中央库构建、项目检查器和CI的证据另由协调者记录；本代理没有把“读过日志”写成“自己运行过构建”。

此结论只覆盖冻结SHA所指实代数局部。没有复标量、复共轭或sesquilinear声明，故不提升原文450的复Hermitian义务；没有零标架构造、商空间、非负定理或代表不变性，故不提升465的物理商正性；几何、测度与后续分析桥接继续开放。不改变F06父项部分完成、17项编号结果未完成、作者数学确认待定或最终信任政策待决的状态。

## 8. 普通数学说明核对

在完成上述实际类型判断后，另读 `docs/statements/real-polarization.md`（SHA见输入表）全部57行。其C、M、Q归一化、对称幅度含义、逐槽实线性、两类核结论、1/4零锥系数、F的有序实缩并、假设和未覆盖范围，均准确表达实际声明；未发现数学过强或必要前提遗漏。

说明中的“9项主要支持目标与3项独立标量接口审计目标”也与当时实际scope登记的12个 `polarization:` 目标逐项一致；“2定义、27定理”与29项公共声明一致。核对时F06父项为 `partially_formalized`，17项编号结果仍 `not_formalized`。这只是本轮解释及登记一致性的核对，不替代论文正式结果全集的独立范围审计。

该普通数学说明是一个可识别、已独立核对准确性、拟交用户/作者确认的解释版本。代理复核本身没有产生用户/作者确认；确认仍为pending。解释文件今后若有数学含义或范围改变，需核对影响；纯措辞排版变化按工作流处理，不自动重审整个F06。
