# Ricci 符号片段的独立逆向核验

复核日期：2026-11-15。复核范围仅为 `Burnett/Algebra/RicciSymbol.lean` 对应的固定点实代数，尤其是原文第 452 行的非特征分支。本文不是整篇论文的结果覆盖结论，也不是主定理通过或作者确认记录。

**结论：该实数、非特征、对角消去片段的独立语义核对通过，固定版本下的独立源码编译、类型及传递公理探针也通过。** 原文第 432–465 行中的完整二次展开、极化、零锥分支和物理商空间非负性均不在此片段的已证范围。首次探针使用已逐包核对版本的父工作区只读编译路径；项目自身的官方依赖缓存准备完成后，同一冻结源码与同一探针又在本项目独立依赖环境中实际复跑通过。最后仅规范换行和文件尾空白的当前源码也经独立差异核对及本项目环境复跑通过。各次证据分别保留，具体见下文；本探针不冒称整项目检查入口或整篇结果通过。

## 独立性与输入

本复核先直接读实际 Lean 文件，写下数学解释，再读锁定原文比较。首次读回保存在 `.project-verification/reverse-ricci/initial-readback.md`。没有读取 `.project-verification/forward/`、实现者正向说明或其他代理结论。项目规则、标准及通用工程状态用于确定工作边界，不作为数学对应正确的依据。

| 输入 | 身份 |
| --- | --- |
| 锁定原文 `paper/burnett.tex` | SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e` |
| 当前实际实现 `Burnett/Algebra/RicciSymbol.lean` | SHA256 `f9cfae66918e599d0fb1fc9380118ca6f3a0c96449dc194d69bbca79fb736bf8`；仅换行及文件尾空白规范化，见最后追加记录 |
| 初次独立复核的实现 | SHA256 `60683d4f8d9f4d80cf39511f0669407dd67e8613006901c87008ff51f2ba2d95`；原字节保存在 `.project-verification/reverse-ricci/RicciSymbol.snapshot.lean` |
| 当前实现字节快照 | `.project-verification/reverse-ricci/RicciSymbol.current.snapshot.lean`，与当前实现哈希相同 |
| 原文比较位置 | 第 415–465 行；另核对第 99–114 行的四维 Lorentz 背景及第 334–338 行的指标、求和约定 |
| Lean | `leanprover/lean4:v4.24.0` |
| Mathlib 固定版本 | `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` |

## 从实际定义读回的数学命题

这里所有量都在一个固定点。指标集为 $I=\{0,1,2,3\}$。`Covector` 是 $I\to\mathbb R$，`Tensor2` 是 $I\times I\to\mathbb R$，没有在类型中要求张量对称。令 $G^{ab}$ 表示 `gInv` 的分量。实际定义为

$$
\xi^a=\sum_dG^{ad}\xi_d,\qquad
k_c{}^a=\sum_dG^{ad}k_{cd},\qquad
s=\sum_{a,b}G^{ab}\xi_a\xi_b,
$$

$$
t=\sum_{a,b}G^{ab}k_{ab},\qquad
q_b=\sum_a\xi^ak_{ab},\qquad
\mathcal R_\xi(k)_{ab}=\frac{s k_{ab}+\xi_a\xi_bt-\xi_aq_b-\xi_bq_a}{2}.
$$

每个求和遍历完整指标集；二重和包含全部有序指标对，不是只枚举对称分量的上三角，也没有额外除以二。

实际的第一个主要命题是：对任意实数组 $G$、实协向量 $\xi$ 和实数组 $k$，如果 $s\ne0$ 且每个 $a,b$ 都满足 $\mathcal R_\xi(k)_{ab}=0$，则数组等式

$$
k_{ab}=\xi_av_b+v_a\xi_b,\qquad
v_b=\frac{q_b-t\xi_b/2}{s}
$$

成立。这是 `kernel_eq_pureGauge` 的全部结论。它没有声明逆向“任意规范张量都在 Ricci 核中”。实际证明从 $2\mathcal R=0$ 移项，利用 $s\ne0$ 除以 $s$。这一步不需要 $G$ 对称或非退化，也不需要预先假定 $k$ 对称；结论本身使该核中的 $k$ 对称。

不能在任意非对称 $G$ 上擅自补上逆向。例如令 $G^{00}=G^{01}=1$、其他分量为零，$\xi=(1,0,0,0)$、$v=(0,1,0,0)$、$k=\xi\otimes v+v\otimes\xi$。此时 $s=1$、$t=1$，但 $\mathcal R_\xi(k)_{00}=1/2$。所以定理名称必须按其实际单向类型理解。原文使用真实对称逆度量，且第 452 行所需恰是已证方向。

后续定义为

$$
c(k)^a{}_{bc}=\frac{\xi_bk_c{}^a+\xi_ck_b{}^a-\xi^ak_{bc}}2,
$$

$$
B_{bc}(k,k)=\sum_{a,e}\left(c(k)^a{}_{ce}c(k)^e{}_{ba}-c(k)^a{}_{ae}c(k)^e{}_{bc}\right).
$$

Lean 分别证明升指标的线性展开、规范张量的连接符号公式，以及二次消去：

$$
c(\xi\otimes v+v\otimes\xi)^a{}_{bc}=\xi_b\xi_cv^a,
\qquad B_{bc}(\xi\otimes v+v\otimes\xi,\xi\otimes v+v\otimes\xi)=0.
$$

二次消去的两个被加项对于每个有序 $(a,e)$ 已经相等，所以没有换和、截断或符号遗漏问题。最终命题 `quadraticSymbol_eq_zero_of_noncharacteristic_kernel` 把前述规范表示代入，得出

$$
s\ne0,\quad \mathcal R_\xi(k)=0
\quad\Longrightarrow\quad
\forall b,c,\ B_{bc}(k,k)=0.
$$

除所列 $G,\xi,k,s\ne0,\mathcal R=0,b,c$ 外，实际 `#check @...` 确认这些定理没有外加几何、正则性、存在性或待证结论参数。实数域及有限求和的库结构是固定类型，不是由使用者提供的额外数学假设。完整类型与公理输出保存在下述探针日志中。

## 与锁定原文的逐项比较

| 核对项 | 判断及理由 |
| --- | --- |
| 四维实坐标对象 | 原文第 99–101、334 行使用四维 Lorentz 度量的坐标分量；`Fin 4` 恰好给出四个坐标指标。这里仅表示点上的实分量。 |
| 升指标 | `raiseCovector` 用 $G^{ad}\xi_d$；`raiseSecond` 用 $G^{ad}k_{cd}$，对应原文的 $\xi^a,k_c{}^a$。对原文对称 $k$，无换置差异。 |
| $q,t,s$ 与 Ricci 符号 | 与原文第 416–417 行逐项相同，包括 $1/2$、两个负号及自由指标位置。 |
| 有序求和 | $t,s$ 和 $B$ 的双和均覆盖所有有序对，符合原文第 335、428 行；对称张量非对角分量的重数得到保留。 |
| 分母 | $v$ 中的分母是同一 `symbolNorm`，有实际前提 $s\ne0$；实数中的 $2$ 非零。没有依赖 Lean 在零处分式的默认值证明零锥结论。 |
| 规范表示 | 第 452 行的 $\mathcal R=0\Rightarrow k=\xi\otimes v+v\otimes\xi$ 与显式 $v$ 均已对应；原文此处不要求一个双向定理，Lean 也没有提供逆向。 |
| 连接符号及 $B$ 顺序 | 与第 434–435 行相同，特别是 $c^a{}_{ce}c^e{}_{ba}-c^a{}_{ae}c^e{}_{bc}$ 的两项顺序及负号。 |
| 实数对角消去 | 对任意实规范振幅的 $c$ 公式与 $B(k,k)=0$ 已表示，继而在非特征 Ricci 核上消去。 |
| 混合项/复数振幅 | 未定义双线性或 Hermitian 极化，不能把最后一个实数对角命题登记为原文“包括全部混合项”的已形式化结论。 |

### 一般数组的命题如何用于真实逆 Lorentz 度量

这里不能只用“形式命题更一般”作为判断理由。具体代入如下：在原文任一点 $x$ 的坐标基中，取 $G^{ab}$ 为真实逆度量 $g^{ab}(x)$，取 $\xi_a,k_{ab}$ 为原文实协向量与实对称张量的坐标分量。上述每个定义遂分别变成原文的 $\xi^a,k_c{}^a,s,t,q,c,B$；没有把逆度量替成 Euclidean 单位阵，也没有要求该坐标基把度量对角化。原文的 $s\ne0$ 和 $\mathcal R=0$ 正好给出实际定理的两个前提。因此该实数非特征结论适用于原文一般逆 Lorentz 度量，而非仅 Minkowski 常系数特例。

源码没有创建几何度量对象，也没有证明 $G$ 是某个协变度量的逆或证明坐标自然性。这是分量模型的表示边界；此代数片段在每个点代入已给的真实逆度量，不需要额外的求逆定理。但后续若要声称流形级或坐标无关的 Lean 结论，需要相应桥接，不能把本说明当作已形式化的几何定理。

原文还将两个完整乘积写为 $\xi_b\xi_c(\xi^av_a)^2$。源码直接证明两乘积的差逐项为零，没有另证该平方表达式。根据实际定义，其各自求和为 $\xi_b\xi_c(\xi_av^a)^2$；在原文对称逆度量下 $\xi_av^a=\xi^av_a$，故没有符号矛盾。一般非对称数组 $G$ 的额外适用域不应被解释成原文 Lorentz 几何的域。

### 数学自检

在 $k\mapsto\lambda k$ 下，$t,q,\mathcal R,v,c$ 均一次齐次，$B$ 二次齐次；在 $\xi\mapsto\mu\xi$ 下，$s,\mathcal R,B$ 二次齐次，$q,c$ 一次齐次，非特征区中的 $v$ 为负一次齐次，因而规范表示保持正确次数。分母与 $s=0$ 的界线相容。

假设不是只允许零数据。例如取 $G=\operatorname{diag}(-1,1,1,1)$、$\xi=(1,0,0,0)$，令 $k_{01}=k_{10}=1$、其他分量为零。直接代入给出 $s=-1$、$t=0$、$q=(0,-1,0,0)$、$\mathcal R=0$、$v=(0,1,0,0)$，得到非零 $k=\xi\otimes v+v\otimes\xi$。这项人工分量自检用于排除空前提误读，不替代普遍命题的 Lean 证明。相反，若 $G=0$ 或 $\xi=0$，则 $s=0$，不能使用非特征定理。对非对称 $k$ 也没有漏掉的核方向：反对称化 $\mathcal R=0$ 给出 $s(k_{ab}-k_{ba})=0$，所以 $s\ne0$ 时 $k$ 必须对称。

## 尚未覆盖的原文结论

以下内容没有被本文件形式化，均仍需后续目标：

1. 第 437–449 行的 $K_2,(k^2)$、九项展开、$c(k)^a{}_{ae}=\xi_et/2$ 以及完整公式 `eq:B-algebra`。
2. 第 450、452 行的双线性混合消去、Hermitian 极化和复振幅结论。它们可以在数学上由适当极化获得，但尚无相应 Lean 对象及证明。
3. 第 454–458 行 $s=0$ 下 Ricci 核与 $q=t\xi/2$ 的等价关系及 `eq:B-null`。零锥下还需原文非零 $\xi$；本片段的 $s\ne0$ 前提自动排除了该处，不能替代零锥推理。
4. 第 459–463 行 $F(k,\ell)=0$ 的物理/规范混合交叉消去。
5. 第 465 行零标架、可独立消去的规范分量、无迹屏幕张量代表、物理商空间的非负性与代表无关性。
6. 第 414、421–428 行从缺陷测度得到 Ricci 核约束的分析过程、正 Hermitian 测度、$r$-等距与协变变换；也没有测度支集、极限 Ricci 张量或主定理结论。

因此，现有整个 `unnum:quadratic-symbol-algebra`（第 432–465 行）只能记为部分完成；本次通过范围应准确收窄为“非特征 Ricci 核的实数规范表示与二次对角消去”。

## 机器复核记录

### 首次探针：父工作区只读编译路径

实际执行的 SDK 为 `D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lean.exe`，报告 Lean 4.24.0，commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`。探针 `.project-verification/reverse-ricci/Probe.lean` 直接含实际源正文，在末尾执行全部定义及定理的 `#check @...`、五个已证定理的 `#print axioms`，避免误读过时项目 `.olean`。

为不阻塞在项目自身的官方定向缓存下载，本复核按授权只读使用父工作区 `D:\Chatpgt\Lean形式化\.lake\packages\<包名>\.lake\build\lib\lean` 中的库对象。在运行前逐一核对本项目 `lake-manifest.json` 的全部九包：父目录的实际 HEAD 均与相应锁定值一致，tracked 源码均无修改。`Cli` 没有可用编译目录，故未加入路径；本片段的导入闭包不需要它。没有复制、写入或替换共享缓存，也没有运行 Lake 更新或更改项目配置。

实际命令，在项目目录运行并按记录设置 `LEAN_PATH`：

```powershell
& 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lean.exe' `
  -o '.project-verification/reverse-ricci/Probe.olean' `
  '.project-verification/reverse-ricci/Probe.lean'
```

**实际退出码为 0。** 原文、实现和探针的运行后哈希仍与所绑定输入一致。探针 SHA256 为 `7706ee9e830aa6eb59cfd0876f421ba137c213e631582d36ed5a4ca9f69afc94`。没有编译警告或错误，五个定理的传递公理集均恰为

```text
propext, Classical.choice, Quot.sound
```

没有出现 `sorryAx` 或新增数学公理。该公理报告描述实际依赖，不代表用户已经批准最终信任政策。

| 本地证据 | 内容 |
| --- | --- |
| `.project-verification/reverse-ricci/initial-readback.md` | 先于原文比较形成的数学读回 |
| `.project-verification/reverse-ricci/inputs.json` | 探针运行前的原文、源码、配置哈希及实际 SDK / Mathlib 版本 |
| `.project-verification/reverse-ricci/readonly-fallback-package-heads.json` | 九包锁定值、实际 HEAD、tracked 源码状态、编译目录存在性 |
| `.project-verification/reverse-ricci/readonly-fallback-lean-path.txt` | 运行时实际只读导入路径 |
| `.project-verification/reverse-ricci/probe-readonly-fallback.log` | 全部实际类型和五个传递公理集 |
| `.project-verification/reverse-ricci/probe-readonly-fallback-result.json` | 实际命令、开始/结束时间、退出码、源码/探针/日志哈希 |

这些输出记录的是本次独立编译，不代替项目自身 Lake 构建、目标清单登记或完整机器入口的检查结果。

### 追加复跑：本项目独立依赖环境

2026-11-15（UTC 开始 `2026-11-14T18:25:36.6824689Z`，结束 `2026-11-14T18:25:52.1587554Z`），在本项目自身的官方依赖缓存就绪后，再次核对本项目九包实际 HEAD 与本项目 manifest 全部匹配，tracked 源码无修改。随后清除该子进程可能继承的 `LEAN_PATH`，仅在此次 PowerShell 子进程的 `PATH` 前置 SDK 的 bin，使用本项目 `lake env` 设置导入环境。

实际命令：

```powershell
$projectSdkBin = 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin'
$env:PATH = $projectSdkBin + ';' + $env:PATH
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
& "$projectSdkBin\lake.exe" env "$projectSdkBin\lean.exe" `
  -o '.project-verification/reverse-ricci/Probe.project.olean' `
  '.project-verification/reverse-ricci/Probe.lean'
```

**实际退出码再次为 0，无警告或错误。** 实际 `LEAN_PATH` 中的第三方包均在 `D:\Chatpgt\Lean形式化\Burnett-conjecture\.lake\packages\` 下，另包含本项目的编译目录和 SDK 标准库，没有使用父工作区的包编译路径。此次没有再运行缓存下载、复制缓存或修改配置。

与首次探针相同，全部定义及五个定理的实际类型符合上述读回，五个传递公理集均恰为 `propext, Classical.choice, Quot.sound`，没有 `sorryAx` 或新增数学公理。两次完整 stdout 日志的 SHA256 均为 `03a869cc1f9aede07957022522bfe89037d8e10ea65bbec4fba2fb19e9a453bf`。

复跑前后原文、冻结实现、原探针、工具链、lakefile、manifest 及本轮 scope 的哈希均未变化。其中原文、实现和探针分别仍为上文的 `e5e9fc…`、`60683d…`、`7706ee…`；本轮 scope SHA256 为 `81651a0da2c7090e336c289faed1aa3685a54dda937c5d64aa61455b07e58668`。完整值与各包实际 revision 已保存，不据 scope 增加支持目标而扩大本复核的数学范围。

| 追加证据 | 内容 |
| --- | --- |
| `.project-verification/reverse-ricci/project-probe-inputs.json` | 本轮全部输入哈希、本项目九包实际 HEAD 及 tracked 状态 |
| `.project-verification/reverse-ricci/project-lean-path.txt` | 本项目 `lake env` 实际提供的独立导入路径 |
| `.project-verification/reverse-ricci/probe-project.log` | 本项目环境下再次输出的全部实际类型与五个公理集 |
| `.project-verification/reverse-ricci/probe-project-result.json` | 新命令、开始/结束时间、实际退出码 0、输入前后绑定及日志哈希；`fallback_used: false` |

这次追加消除了首次机器证据依赖父工作区编译路径的局限；首次记录仍作为历史证据保留。这里实际运行的是本项目环境中的冻结源码探针，完整项目构建及目标检查入口由其各自的实际执行记录负责。

### 最终源码绑定：仅换行和文件尾空白变化

提交格式整理后，实际实现哈希从 `60683d4f8d9f4d80cf39511f0669407dd67e8613006901c87008ff51f2ba2d95` 变为 `f9cfae66918e599d0fb1fc9380118ca6f3a0c96449dc194d69bbca79fb736bf8`。本复核没有读取 forward 目录，而是将当前源与自己原先保留的 `RicciSymbol.snapshot.lean` 直接比较，实际断言

```text
current_source == old_source.Replace(CRLF, LF).TrimEnd() + LF
```

通过。因此变化精确限于 CRLF 改 LF 及文件尾空白，定义、类型、证明内容和数学解释均未改变；沿用上述独立语义核对，不重复全数学复审。原探针的完整字节另存为 `Probe.pre-format.lean`（SHA256 `7706ee9e830aa6eb59cfd0876f421ba137c213e631582d36ed5a4ca9f69afc94`），保留前两次证据中的原路径和原哈希作为历史记录。当前 `Probe.lean` 用当前源正文加上完全不变的检查后缀重新生成，SHA256 为 `02c44241376378abc6deae91dec36ce4c1378045a744c2a030413611176a4b88`。

2026-11-15（UTC 开始 `2026-11-14T18:29:47.7977256Z`，结束 `2026-11-14T18:30:04.7173462Z`），仍仅使用本项目独立依赖环境，再次实际运行：

```powershell
& 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lake.exe' env `
  'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lean.exe' `
  -o '.project-verification/reverse-ricci/Probe.current.olean' `
  '.project-verification/reverse-ricci/Probe.lean'
```

**实际退出码为 0，无警告或错误。** 实际 `#check @...` 类型与五个 `#print axioms` 的 stdout 与格式整理前逐字一致，日志 SHA256 仍为 `03a869cc1f9aede07957022522bfe89037d8e10ea65bbec4fba2fb19e9a453bf`。五个定理仍恰依赖 `propext, Classical.choice, Quot.sound`，无 `sorryAx`。本次输入前后哈希绑定全部一致，原文与项目配置均未改变。

| 当前源码的追加证据 | 内容 |
| --- | --- |
| `.project-verification/reverse-ricci/current-source-inputs.json` | 独立格式差异断言、原/当前源及原/当前探针哈希、其他输入绑定 |
| `.project-verification/reverse-ricci/RicciSymbol.current.snapshot.lean` | 当前实际实现的字节快照 |
| `.project-verification/reverse-ricci/Probe.pre-format.lean` | 完整保留前两次机器证据对应的原探针 |
| `.project-verification/reverse-ricci/current-source-lean-path.txt` | 此次本项目环境实际导入路径 |
| `.project-verification/reverse-ricci/probe-current-source.log` | 当前源码的实际类型与传递公理输出 |
| `.project-verification/reverse-ricci/probe-current-source-result.json` | 当前源码的实际命令、时间、退出码、前后输入及输出绑定 |

## 确认与状态

独立代理的数学核对没有发现该实数非特征片段与原文的实质不符；该范围的独立源码编译、类型及传递公理探针已在上述两个环境中实际通过。用户/作者对以上普通数学解释的确认截至本次追加仍未收到。本记录不伪造确认，不宣布整篇覆盖、最终信任政策批准或论文主定理通过。

## 2026-11-15：按用户要求进行第二轮交叉讨论

用户对数学解释确认问题的实际答复为“找子代理讨论核对”。本轮据此增加独立复核，不将该答复登记为作者确认。输入仍为本文顶部列出的原文 `e5e9fc…` 与实现 `f9cfae…`；本轮没有改变原文、Lean 定义、定理、证明、依赖锁或目标清单。

### 独立取证与交叉质疑

- `ricci_type_readback_v2` 在新上下文中先读实际 Lean 文件，冻结全部定义及5条定理的普通数学回读，再读原文第400–475行及符号约定；未借用旧复核结论。
- `ricci_paper_adversary_v2` 在另一新上下文中先从原文第390–480行及相关约定提取命题，再读实际 Lean 文件；独立核对升指标、两项乘积顺序、单向/双向及实数/复数边界。
- 两者独立形成判断后互换争议和反例，并核对主代理从原文定义重建的精确边界例。下述裁决依据实际等式与反例，不以代理一致或历史CI代替数学证明。

### 重新展开的核心证明

对每个 $a,b$，由 $\mathcal R_\xi(k)_{ab}=0$ 得

$$
s k_{ab}=\xi_aq_b+\xi_bq_a-t\xi_a\xi_b
=s(\xi_av_b+v_a\xi_b),\qquad
v_b=(q_b-t\xi_b/2)/s.
$$

这里使用明示前提 $s\ne0$，所以约去 $s$ 合法。升第二指标后，$k_c{}^a=\xi_cv^a+v_c\xi^a$；代回原文的 $c$，交叉项相消，得到 $c(k)^a{}_{bc}=\xi_b\xi_cv^a$。因此，$B$ 中每个有序指标对 $(a,e)$ 的两项分别为

$$
(\xi_c\xi_ev^a)(\xi_b\xi_av^e),\qquad
(\xi_a\xi_ev^a)(\xi_b\xi_cv^e),
$$

二者逐项相等，故求和后的差为零。此推导不需要预设 $G$ 或 $k$ 对称；把 $G$ 取为原文真实逆Lorentz度量即可逐点应用。

### 争议、反例与裁决

| 质疑 | 实际核查与裁决 |
| --- | --- |
| 一般实数组会不会把原命题换掉？ | 各收缩、自由指标、$1/2$、负号和完整有序求和与原文一致；取 $G^{ab}=g^{ab}(x)$ 时回到原文分量。没有用单位阵替代逆度量，也未声称已完成流形级求逆或坐标自然性桥接。 |
| 名称是否暗示核与全部纯规范张量双向相等？ | 实际类型只有核 $\Rightarrow$ 显式纯规范。任意非对称 $G$ 上逆向确实可能为假：取 $G$ 为单位阵加 $G^{01}=1$，$\xi=e_0,v=e_1$，则 $s=1$，但 $\mathcal R_\xi(\xi\otimes v+v\otimes\xi)_{00}=1/2$。不能把定理名解读成额外的集合等价。 |
| 原文两乘积的平方表达式是否匹配？ | 直接求和的自然表达式为 $\xi_b\xi_c(\xi_av^a)^2$；原文写为 $\xi_b\xi_c(\xi^av_a)^2$。真实逆度量对称，故两缩并相等。一般非对称 $G$ 与任意纯规范张量上不可直接互换；但这不否定当前逐项消去，也不要求给核子命题新增对称性假设。实际5条定理没有另行声明两乘积各自的平方值。 |
| 是否已经覆盖第452行的全部混合项？ | 没有。当前定义与最后一个定理只有实数对角 $B(k,k)$，未编码双线性、Hermitian极化或测度结论。原文第450行和第452行末句仍是后续义务；“本轮目标”应明确指第452行的实数、非特征、对角子命题。 |
| $s\ne0$ 是否只是可删的技术前提？ | 不能删除。取 $G=\operatorname{diag}(-1,1,1,1)$，$\xi=(1,1,0,0)$，$k=\operatorname{diag}(0,0,1,-1)$。有 $s=t=q=0$，故 $\mathcal R_\xi(k)=0$，但 $B_{00}(k,k)=1/2$。直接算得 $c(k)^e{}_{00}=0$，$c(k)^a{}_{0e}=k_e{}^a/2$，所以第一乘积求和为 $(1+1)/4$。此例也由两位代理独立核对。 |

主代理用 Python 标准库 `Fraction` 从原文定义重建了三个精确分量检验：非零Lorentz非特征规范例、上述非对称逆向反例及零锥反例。脚本 `.project-verification/ricci-cross-review/exact_checks.py` 实际退出0，结果保存在同目录 `exact-checks.json`。这些有限例仅检查陈述边界，不作为普遍恒等式或新增Lean目标的证明。本轮未重复运行未变的Lean构建；先前固定源码机器证据继续按其原绑定适用。

**本轮裁决：当前5条声明准确覆盖所述实数、非特征、对角子命题，未发现需要修改实现或补加数学假设的缺陷。** 完整二次展开、混合/Hermitian极化、零锥及几何/测度桥接保持未完成。作者确认仍待实际答复，本轮交叉讨论不替代人类确认或整篇覆盖。
