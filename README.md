# Burnett-conjecture

这是论文 **High-frequency vacuum limits with bounded first derivatives: a variational approach to the forward Burnett conjecture** 的 Lean 工程。远程仓库为 [Oho1e/Burnett-conjecture](https://github.com/Oho1e/Burnett-conjecture)，已按用户授权改为**公开**。构建运行见 [GitHub Actions](https://github.com/Oho1e/Burnett-conjecture/actions)，固定提交和实际运行状态由 GitHub 记录。

当前状态为 `development`：共有102个注册Lean审计目标，保留F06的78项并加入X02的24项。其中正式命题 `prop:cubic` 已有同一见证的完整证明和用户委托的语义确认；其余16项编号结果尚未形式化。用户另批准原3193行固定离零锥Fourier梯度局部化为第三项必做未编号结果，当前未证。174条inventory、33份Lean源和46片工作图只用于防漏组织，不是数学完成率；整篇verified保持false。

用户另已明确将“旋转零矩张量无输运表示”及“多尺度Rosen真空序列与精确零源坐标”两个未编号结果纳入最终必做目标；它们尚未形式化，分别对应X03、X06。全文工作图共有46片；切片完成了源码归属与接口规划，不表示46项数学证明已经完成。

原文快照为 [`paper/burnett.tex`](paper/burnett.tex)，176424字节，SHA256：

```text
e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e
```

来源身份见 [`paper/source.json`](paper/source.json)。该副本保留用户原文件字节；Git 对该文件禁用行尾转换。

工程固定 **Lean 4.24.0** 和 **Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`**，其余依赖见 `lake-manifest.json`。该选择已由近期代数接口实际探针验证；中期测度、微局部分析与几何接口仍有待补的桥接和实现。

```powershell
lake exe cache get Mathlib.Algebra.BigOperators.Fin Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Analysis.Calculus.BumpFunction.InnerProduct Mathlib.Analysis.Calculus.BumpFunction.Normed Mathlib.Analysis.Calculus.ContDiff.Basic Mathlib.Analysis.Calculus.ContDiff.Operations Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts Mathlib.Analysis.InnerProductSpace.LinearMap Mathlib.Analysis.InnerProductSpace.PiL2 Mathlib.Analysis.Normed.Operator.Completeness Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv Mathlib.Data.Complex.Basic Mathlib.Data.Real.Basic Mathlib.MeasureTheory.Function.L2Space Mathlib.MeasureTheory.Function.LpSpace.Indicator Mathlib.Order.Filter.AtTopBot.Archimedean Mathlib.Tactic.FieldSimp Mathlib.Tactic.FinCases Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Topology.Algebra.Module.Basic Mathlib.Topology.Algebra.Order.Field Mathlib.Topology.MetricSpace.Pseudo.Basic
python scripts/check_project.py --repo .
```

本机可用已存在的SDK：

```powershell
$env:PATH = 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin;' + $env:PATH
lake exe cache get Mathlib.Algebra.BigOperators.Fin Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Analysis.Calculus.BumpFunction.InnerProduct Mathlib.Analysis.Calculus.BumpFunction.Normed Mathlib.Analysis.Calculus.ContDiff.Basic Mathlib.Analysis.Calculus.ContDiff.Operations Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts Mathlib.Analysis.InnerProductSpace.LinearMap Mathlib.Analysis.InnerProductSpace.PiL2 Mathlib.Analysis.Normed.Operator.Completeness Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv Mathlib.Data.Complex.Basic Mathlib.Data.Real.Basic Mathlib.MeasureTheory.Function.L2Space Mathlib.MeasureTheory.Function.LpSpace.Indicator Mathlib.Order.Filter.AtTopBot.Archimedean Mathlib.Tactic.FieldSimp Mathlib.Tactic.FinCases Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Topology.Algebra.Module.Basic Mathlib.Topology.Algebra.Order.Field Mathlib.Topology.MetricSpace.Pseudo.Basic
python scripts/check_project.py --repo . --lake 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lake.exe'
```

此 PATH 设置只影响当前终端，确保缓存程序内部再调用 `lake` 时也使用同一SDK。

入口核对原文身份、标准、固定运行时并构建库入口；对当前102个真实注册目标再调用 `scripts/check_paper.py` 做存在性、来源和传递公理审计。机器通过仍不能代替结果覆盖、语义对应或作者确认，`paper_formalization_verified` 保持false。没有目标的初始阶段仅输出 `project-setup-passed`。

- [`RicciSymbol.lean`](Burnett/Algebra/RicciSymbol.lean) 实现实数非特征核的显式规范表示和二次消去；[数学解释及实际声明](docs/statements/ricci-symbol.md)、[独立回读](docs/statements/ricci-symbol-review.md)。
- [完整实二次代数与零锥交叉](docs/statements/quadratic-real-algebra.md) 对应两条并行实现及主代理的实际拼接；[独立回读](docs/statements/quadratic-real-algebra-review.md) 记录输入版本、真实类型及未覆盖项。
- [实混合极化](docs/statements/real-polarization.md)及[独立实际类型回读](docs/statements/real-polarization-review.md)记录F06新增交付；[本轮监督实测报告](docs/formalization/f06-workflow-test.md)分别记录数学、流程、CI和未覆盖边界。
- [多代理并行工作流](docs/formalization/parallel-workflow.md) 记录分工与构建/快照交接；[GitHub PR与合并](docs/formalization/github-workflow.md) 规定独立复核、组合CI、候选交接及按项目授权执行合并。数学标准仍为1.2，当前skill与工程工作流为1.3.1；旧技能包保留。
- [点态Hermitian与二维物理类](docs/statements/hermitian-null-algebra.md)及[独立复核](docs/statements/hermitian-null-algebra-review.md)记录F06的57个新增支持目标，已随用户合并PR4进入main。PR5保留这些成果并加入X02，不重写已确认的数学源码。
- [`全文切片与依赖图`](docs/formalization/slices.md) 给出每段源码的归属、逐片输入输出、正式结果的陈述与闭合位置、共同闭合组及下一步；[机器清单](docs/formalization/slices.json) 与现有 scope 相连。运行 `python scripts/check_slices.py --repo .` 检查原文身份、分区、结果映射、依赖环和文档一致性；该结构检查不认证数学完备。
- `python scripts/prepare_slice.py F06 --repo .` 导出指定切片的工作包，含锁定原文、当前清单状态、直接输入及消费者，保存于 `.project-verification/slice-packets/`；换用表中ID即可。每次续接重新导出，避免沿用过期状态。
- [切片独立复核与修订](docs/formalization/slicing-review.md) 记录新上下文代理的发现、相位隙反例及修复。工作包同时附本片开放外部接口与公共记录入口；这些待核输入不因导出而成为已证结果。
- [`主定理接口`](docs/statements/main-interface.md)、[`主线依赖`](docs/formalization/dependencies.md)、[`库调查`](docs/formalization/library-audit.md) 记录当前对象、量词、消费者和实际库证据。
- [`docs/statements/`](docs/statements/) 保存原文结果索引与未来数学/Lean对照。
- [`docs/formalization/scope.json`](docs/formalization/scope.json) 是范围与进度的主清单；完整二次代数父项仍为部分完成。
- [维护工具与PR交接](docs/formalization/maintenance-1.3.1.md)记录快照边界、完整保护比较和只读就绪判定；本轮维护停在PR，长期默认合并执行者仍待用户选择。
- [`docs/formalization/review.md`](docs/formalization/review.md) 记录实际复核及发布情况；[1.3版工作流对抗审核与测试](docs/formalization/workflow-review.md) 区分独立审查、模拟场景和真实GitHub检查。
- [`docs/formalization/standard.zh-CN.md`](docs/formalization/standard.zh-CN.md) 固定 `paper-results` 第1.2版标准。
- [`tools/lean-paper-results/`](tools/lean-paper-results/) 是1.3.1版skill与工程工作流的文本快照；维护负例套件无需逐篇论文重复运行。

2026-11-16用户选择A：全部数学依赖闭合，只接受scope所列三基础公理，可复用固定库证明。新点态复代数解释按用户明确委托由主代理与独立代理确认；不记为用户/作者本人逐行读过Lean。正式结果与测度/输运主线仍未完成，后续接入几何Lorentz数据及F05/F07协方差对象，并推进独立结果X02。

- [X02三线性反例](docs/statements/cubic-counterexample.md)及[复核](docs/statements/cubic-counterexample-review.md)记录完整正式命题与1A委托确认。[新增固定Fourier离锥目标](docs/statements/cubic-off-null-localization.md)单列2A批准范围和未证状态。PR5尚未合并，旧3A不自动授权它的最终合并。
