# Burnett-conjecture

这是论文 **High-frequency vacuum limits with bounded first derivatives: a variational approach to the forward Burnett conjecture** 的 Lean 工程。远程仓库为 [Oho1e/Burnett-conjecture](https://github.com/Oho1e/Burnett-conjecture)，已按用户授权改为**公开**。构建运行见 [GitHub Actions](https://github.com/Oho1e/Burnett-conjecture/actions)，固定提交和实际运行状态由 GitHub 记录。

当前状态为 `development`：已有 **9个注册Lean支持目标**，覆盖实非特征消去、完整实B展开、实零锥核/B公式及实规范交叉消去。原文17项正式 theorem/lemma/proposition/corollary 仍均未完成；已有支持引理不计作其中一项完成。关键未编号断言、必要定义和依赖的完整覆盖仍待核对，整篇数学与输运主线尚未闭合。

用户另已明确将“旋转零矩张量无输运表示”及“多尺度Rosen真空序列与精确零源坐标”两个未编号结果纳入最终必做目标；它们尚未形式化，分别对应X03、X06。全文工作图共有46片；切片完成了源码归属与接口规划，不表示46项数学证明已经完成。

原文快照为 [`paper/burnett.tex`](paper/burnett.tex)，176424字节，SHA256：

```text
e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e
```

来源身份见 [`paper/source.json`](paper/source.json)。该副本保留用户原文件字节；Git 对该文件禁用行尾转换。

工程固定 **Lean 4.24.0** 和 **Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`**，其余依赖见 `lake-manifest.json`。该选择已由近期代数接口实际探针验证；中期测度、微局部分析与几何接口仍有待补的桥接和实现。

```powershell
lake exe cache get Mathlib.Data.Real.Basic Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
python scripts/check_project.py --repo .
```

本机可用已存在的SDK：

```powershell
$env:PATH = 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin;' + $env:PATH
lake exe cache get Mathlib.Data.Real.Basic Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
python scripts/check_project.py --repo . --lake 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lake.exe'
```

此 PATH 设置只影响当前终端，确保缓存程序内部再调用 `lake` 时也使用同一SDK。

入口核对原文身份、标准、固定运行时并构建库入口；对当前9个真实支持目标再调用 `scripts/check_paper.py` 做存在性、来源和传递公理审计。机器通过仍不能代替结果覆盖、语义对应或作者确认，`paper_formalization_verified` 保持false。没有目标的初始阶段仅输出 `project-setup-passed`。

- [`RicciSymbol.lean`](Burnett/Algebra/RicciSymbol.lean) 实现实数非特征核的显式规范表示和二次消去；[数学解释及实际声明](docs/statements/ricci-symbol.md)、[独立回读](docs/statements/ricci-symbol-review.md)。
- [完整实二次代数与零锥交叉](docs/statements/quadratic-real-algebra.md) 对应两条并行实现及主代理的实际拼接；[独立回读](docs/statements/quadratic-real-algebra-review.md) 记录输入版本、真实类型及未覆盖项。
- [多代理并行工作流](docs/formalization/parallel-workflow.md) 记录分工与构建/快照交接；[GitHub PR与合并](docs/formalization/github-workflow.md) 规定独立复核、组合CI和协调者逐个合并。数学标准仍为1.2，当前skill与工程工作流为1.3；旧技能包保留。
- [`全文切片与依赖图`](docs/formalization/slices.md) 给出每段源码的归属、逐片输入输出、正式结果的陈述与闭合位置、共同闭合组及下一步；[机器清单](docs/formalization/slices.json) 与现有 scope 相连。运行 `python scripts/check_slices.py --repo .` 检查原文身份、分区、结果映射、依赖环和文档一致性；该结构检查不认证数学完备。
- `python scripts/prepare_slice.py F06 --repo .` 导出指定切片的工作包，含锁定原文、当前清单状态、直接输入及消费者，保存于 `.project-verification/slice-packets/`；换用表中ID即可。每次续接重新导出，避免沿用过期状态。
- [切片独立复核与修订](docs/formalization/slicing-review.md) 记录新上下文代理的发现、相位隙反例及修复。工作包同时附本片开放外部接口与公共记录入口；这些待核输入不因导出而成为已证结果。
- [`主定理接口`](docs/statements/main-interface.md)、[`主线依赖`](docs/formalization/dependencies.md)、[`库调查`](docs/formalization/library-audit.md) 记录当前对象、量词、消费者和实际库证据。
- [`docs/statements/`](docs/statements/) 保存原文结果索引与未来数学/Lean对照。
- [`docs/formalization/scope.json`](docs/formalization/scope.json) 是范围与进度的主清单；完整二次代数父项仍为部分完成。
- [`docs/formalization/review.md`](docs/formalization/review.md) 记录实际复核及发布情况；[1.3版工作流对抗审核与测试](docs/formalization/workflow-review.md) 区分独立审查、模拟场景和真实GitHub检查。
- [`docs/formalization/standard.zh-CN.md`](docs/formalization/standard.zh-CN.md) 固定 `paper-results` 第1.2版标准。
- [`tools/lean-paper-results/`](tools/lean-paper-results/) 是1.3版skill与工程工作流的文本快照；维护负例套件无需逐篇论文重复运行。

最终信任政策仍在项目记录中单列。当前机器检查使用标准三基础公理配置；不把它推定为其他项目的政策。当前片段的最终机器、独立复核、作者确认和CI状态见复核记录。后续沿一般极化、复Hermitian及零锥规范商正性继续推进，并补核输运所需外部精确定理。
