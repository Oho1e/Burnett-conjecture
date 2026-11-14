# Burnett 论文初始结构清点

工程副本：本机原始路径改为项目内 `paper/burnett.tex`，其余原文哈希、定位和状态不变。

本轮用途是新工程初始化。本文各数学断言均按原文的 **proposed proof** 状态接收：**待建模、未形式化、未进行数学真伪审查，也未进行独立 Lean 陈述对应审查**。本清点没有证明或修补论文中的数学内容。

## 固定原文

- 原文：`paper/burnett.tex`。
- SHA-256：`e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`。
- 原始大小：176,424 bytes；UTF-8、LF；共 3475 行。以下均为该哈希原文的 1 起算、两端包含行号。
- 题名：*High-frequency vacuum limits with bounded first derivatives: a variational approach to the forward Burnett conjecture*。作者栏与日期栏为空。
- 已通读原文第 1–3475 行，保留原文不变。定位使用 TeX 章节、环境及标签提取，并结合逐段阅读补录叙述中的候选项；未执行 LaTeX 编译。

## 数学主题与边界

原文处理光滑四维时空中真空度规序列的高频极限：度规局部一致趋于光滑、时间定向 Lorentz 极限，一阶导数局部一致有界，不假定坐标条件、对称性或二阶导数与振幅之间的尺度关系。主陈述提出同一非负零锥射线测度的 Einstein 二阶矩表示与 Hamilton 输运；全动量测度和局部有限二阶矩另在全局双曲开子时空上实现。

原文明确区分二次正性/零锥矩构造与输运；完整三次变分及其输运剩余的消失是 proposed proof 的中心主张。反向逼近、非光滑极限、超出给定一阶导数界的集中、非零宇宙学常数和其他维数均不进入当前接收范围（178–190 行）。

供后续模块规划使用的主题层次为：基本几何与容许序列；Ricci 符号和规范商的有限维代数；张量缺陷与正测度；Fourier/伪微分与三线性估计；物理投影的标量有界源；作用变分、Ward 恒等式和两类修正；变背景局部化及顺序极限；全局双曲提升；附录例子与恒等式。这只是主题导航，尚未选择 Lean 定义、数学库接口或首个证明任务。

## 章节与附录

| 编号 | 原文标题 | 标签 | 原文行 |
|---|---|---|---|
| 1 | Introduction | `sec:introduction` | 86–351 |
| 2 | Preliminaries | `sec:quadratic` | 352–518 |
| 3 | Analytic estimates for cubic energies | `sec:analytic` | 519–1591 |
| 4 | A bounded physical source in arbitrary coordinates | `sec:general-projection` | 1592–1719 |
| 5 | The variational transport identity and cubic cancellation | `sec:variational-transport` | 1720–2642 |
| 6 | Proof of Theorem~\ref{thm:main} | `sec:completion` | 2643–3115 |
| A | A harmonic-coordinate example with an unbounded source | `sec:shear` | 3116–3172 |
| B | Characteristic localization and cubic interactions | `sec:cubic` | 3173–3212 |
| C | Conservation and positive null moments do not give transport | `sec:rotating` | 3213–3304 |
| D | The Rosen plane-wave class | `sec:rosen` | 3305–3424 |
| E | Auxiliary identities and coordinate oscillations | 无 | 3425–3463 |

正文为 86–3113 行；`\appendix` 在 3115 行；附录 A–E 的内容为 3116–3463 行，参考文献块为 3464–3474 行。附录 E 原文没有章节标签。全部小节和五个 paragraph 的精确范围保存在 `source-index.json` 的 `headings`。

## 正式结果初始索引

下表的编号按原文共享 theorem 计数器规则推得，未用编译 PDF 核验。每一行均为“原文提出、待建模、未形式化”。“陈述行”只定位结果环境；JSON 另存原文 proof 环境或相邻叙述论证的定位，不认证其内容或覆盖。

| 预计编号 | 类别 | 原文标签 | 原文标题 | 陈述行 |
|---|---|---|---|---|
| 1.1 | theorem | `thm:main` | Forward kinetic limit in the smooth-limit class | 139–168 |
| 2.1 | theorem | `thm:quadratic` | Positive null second moments, without transport | 354–356 |
| 2.2 | corollary | `cor:base-marginal` | Base marginal and angular disintegration | 487–506 |
| 3.1 | lemma | `lem:commutator` | Lipschitz-small coefficients in a symmetric energy pairing | 566–575 |
| 3.2 | lemma | `lem:cubic-continuity` | Continuity of the complete cubic energy | 613–623 |
| 3.3 | lemma | `lem:freezing` | Quantitative freezing of a complete cubic energy | 736–764 |
| 3.4 | lemma | `lem:analytic-near` | All-scale transfer and angular summation | 1026–1057 |
| 3.5 | lemma | `lem:analytic-correction-bounds` | Bounds for the correction and its rough commutator | 1380–1394 |
| 4.1 | proposition | `prop:general-projection` | A projected source without a coordinate condition | 1600–1616 |
| 5.1 | theorem | `thm:variational-transport` | Transport under the original first-derivative hypotheses | 1729–1735 |
| 6.1 | lemma | `lem:lift` | Local-moment version of the globally hyperbolic lift | 2989–2991 |
| 6.2 | corollary | `cor:strong` | Vacuum limits and strong physical compactness | 3063–3078 |
| A.1 | proposition | `prop:shear` | Failure of a background $L^2$ source estimate | 3121–3123 |
| B.1 | proposition | `prop:cubic` | An auxiliary trilinear counterexample | 3175–3181 |
| C.1 | proposition | `prop:bianchi` | Geometric nonrepresentability without vacuum approximation | 3245–3247 |
| D.1 | proposition | `prop:rosen` | Two-polarization Rosen closure | 3307–3312 |
| D.2 | proposition | `prop:flat-rigidity` | Flat admissible sequences have flat smooth limits | 3390–3392 |

共清点 17 个显式正式结果环境：3 theorem、6 lemma、6 proposition、2 corollary。另有 2 个 remark（170–176、178–190 行），共享计数器而分别预计为 1.2、1.3；没有显式 definition 或 problem 实例。原文有 16 个 proof 环境；`thm:quadratic` 的论证以相邻叙述呈现（358–485 行），没有独立 proof 环境。以上是固定源文件的结构记录，不能解释为数学证明完整性或形式化覆盖率。

关键陈述的关系按原文叙述记录如下：主结果结合 `thm:quadratic`、`thm:variational-transport` 与 `lem:lift`（3046–3061 行）；`lem:lift` 以输运为前提（2989–3043 行）；`cor:base-marginal` 和 `cor:strong` 的原文论证说明不使用输运（507–517、3079–3113 行）。JSON 中的结果引用仅为源文本出现的引用，并非已经复核的依赖图。

## 未编号结果候选

原文还有大量在正文中陈述的代数、估计、构造和例子。以下 33 项是进一步建模时需要逐项确认的初始候选，既不是已接受的 Lean 目标，也不表示穷尽全部隐含断言、假设或证明义务。

| 候选主题 | 原文行 |
|---|---|
| 线性化 Ricci 的局部 H^{-1} 紧性/强消失 | 360–388 |
| 共同微局部缺陷测度、单一子序列与 Ricci 核约束 | 392–428 |
| 完整二次代数、非零锥纯规范消除及零锥商正性 | 432–465 |
| 物理测度构造及辅助度量改变时的加权变换 | 469–485 |
| 三次能量的光滑系数差估计 | 719–734 |
| 低高频/可比三元组分割及相邻角帽几何 | 895–951 |
| 角帽乘子有限指数界与角指标 L^3 求和界 | 953–992 |
| 分离物理方向上的精确标量相位隙 | 994–1016 |
| 独立低角变量展开、BS^1 符号与有限导数阈值 | 1248–1377 |
| 散度算子与修正的四次交换子估计 | 1476–1504 |
| 精确修正算子恒等式与有界源配对 | 1506–1526 |
| 角向有限和与上频率截断在固定 n 下的移除说明 | 1528–1590 |
| 密度型 Hessian 的精确 Hermitian 主符号式及规范压缩 | 1747–1809 |
| Hessian 交换子、非线性余项配对与完整三次输运剩余 | 1811–1904 |
| 完整三次变分的低阶项处理、循环 Fourier 顶点和极化连续性 | 1906–2009 |
| 冻结屏幕投影的显式矩阵式及物理相位抽取 | 2053–2107 |
| off-shell Ward 恒等式及一/二/三规范因子分类 | 2109–2261 |
| 低规范修正、Hermitian 对称与独立变量延拓 | 2265–2341 |
| 完整物理近角相互作用的测试符号二次角增益与算子估计 | 2343–2502 |
| 物理远角低高频相互作用的精确相位除法与延拓 | 2504–2555 |
| 两种修正和原始投影场标量波方程的配对估计 | 2557–2590 |
| 完整冻结三次项的近角/修正/物理相位精确装配 | 2592–2641 |
| 变背景的三次局部化与定量冻结 | 2647–2729 |
| 全空间投影梯度范数的缺陷测度表达 | 2731–2758 |
| 冻结屏幕与相位误差及有限指数插值 | 2760–2841 |
| 补丁求和、最终剩余估计及顺序极限 | 2843–2985 |
| 平直背景上的旋转正零锥矩张量：守恒不能推出输运 | 3215–3239 |
| 显式多尺度 Rosen 真空序列及精确零源坐标例 | 3360–3386 |
| 多尺度平直拉回例 | 3430–3439 |
| 类空原始梯度缺陷而物理测度为零的例 | 3441–3442 |
| 弱能量等代数性质不足以给出正实余向量二阶矩的例 | 3444–3445 |
| 二阶导数乘积的分布/H^{-1} 恒等式 | 3447–3459 |
| 改变单位截面的二齐次测试权重 | 3461–3462 |

附录 C 开头的旋转矩张量例子没有 proposition 环境（3215–3239 行）；附录 D 的显式多尺度 Rosen 例子也没有单独结果环境（3360–3386 行）。附录 E 五个 paragraph 已分别列为候选。附录 A、B、C 的辅助反例均按其原文限定接收，不把它们登记为针对主定理的反例结论。

## 定义与记号候选

虽然没有显式 definition 环境，原文仍在行文中定义了以下建模对象。各候选均待确定 Lean 中的类型、上下文、约定及与原文的对应。

| 对象 | 原文行 |
|---|---|
| 四维光滑背景、容许真空序列、辅助度量与导数范数 | 90–112 |
| 非零余切丛、正射线单位截面、Hamiltonian 与 Hamilton 向量场 | 114–125 |
| Einstein 二阶矩、射线测度输运与一齐次测试类 | 126–135 |
| 全动量测度、局部二阶矩和紧支撑输运测试 | 150–167 |
| 指标、有序对称指标求和、体积密度、内积和局部坐标范数 | 331–350 |
| 张量缺陷测度、协方差矩阵约定、Ricci 符号核及物理商 | 392–428 |
| Fourier 约定、双线性乘子及三线性形式 | 539–562 |
| 三元组低高频分割、角帽、薄锥厚度与归一化变量 | 895–1024 |
| 修正的独立变量延拓、球谐展开和 BS^1 符号半范数 | 1248–1377 |
| Euclidean 规范补投影及固定红外正则化 | 1621–1642 |
| Einstein-Hilbert 作用、密度型 Euler 式、Hessian 与物理收缩 | 1747–1788 |
| 完整三次变分、冻结 Fourier 顶点及循环测试因子 | 1917–2009 |
| 高频物理/规范分解、规范势与屏幕投影 | 2013–2107 |
| 规范修正、物理远角修正与完整冻结能量分解 | 2265–2641 |
| Cauchy 截面的齐次能量、流不变截面与加权推前测度 | 2993–3039 |

## 记录含义与后续入口

`source-index.json` 保存固定源身份、完整章节层次、17 个正式结果的原文标签/标题/起止行、论证位置、2 个 remark、33 个未编号候选、15 个定义/记号候选、87 个源标签和 6 个书目键。书目只登记原文条目，未联网核验、获取全文或判断引用是否足够。

后续开始形式化之前，可据本索引单独建立完整陈述与真实 Lean 类型的对应记录，并逐项核对假设、作用域和依赖；该工作尚未进行。所有结果和候选保持待建模、未形式化状态。本轮没有修改原文、创建或修改 Burnett 工程本体、安装依赖、联网或发布。

**交付性质：结构清点，不是独立 Lean 对应审查。**
