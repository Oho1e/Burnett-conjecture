# Burnett-conjecture

[English](README.md) · [贡献说明](CONTRIBUTORS.zh-CN.md)

这是论文 **High-frequency vacuum limits with bounded first derivatives: a variational approach to the forward Burnett conjecture** 的 Lean 工程。远程仓库为 [Oho1e/Burnett-conjecture](https://github.com/Oho1e/Burnett-conjecture)，已按用户授权改为**公开**。构建运行见 [GitHub Actions](https://github.com/Oho1e/Burnett-conjecture/actions)，固定提交和实际运行状态由 GitHub 记录。

当前状态为 `development`。本候选累计 675 个目标、740 个库存项和 732 份 Lean 源码。F04 的局部结果在显式坐标真空条件下识别弱 Ricci 极限，并证明每张优先图内实际线性化 Ricci 的强 H⁻¹ 收敛。内禀曲率结果识别图内的 Ricci 迹，并从同一内禀真空序列导出上述坐标真空条件。Ward 批次提供有限维变分、Fourier Hessian 与规范消去的八个支持目标。完整 Lorentz 数据、全局张量测试、F05 和输运定理仍待完成。[Ward 命题](docs/statements/transport-ward.md) · [弱 Ricci](docs/statements/weak-ricci-identification.md) · [局部强 H⁻¹](docs/statements/geometric-Hminus-closure.md) · [内禀曲率](docs/statements/intrinsic-curvature-Ricci.md) · [范围清单](docs/formalization/scope.json)

四项支持结果证明给定条件角核在可测变换坐标及非负加权后的重构。 [条件角核的变换](docs/statements/angular-kernel-transforms.zh-CN.md)

最终范围包括旋转零矩张量无输运表示（X03）及多尺度 Rosen 真空序列与精确零源坐标（X06）。X03 已随 PR #13 进入 `main`。本次交付实现 X06，覆盖不存在共同导数尺度的结论，以及两套坐标下的 Einstein 矩和输运恒等式。作者确认在范围清单中登记。[X06 命题说明](docs/statements/rosen-multiscale.md) · [切片总览](docs/formalization/slices.md)

X07 证明满足容许条件的平直序列，其光滑极限的内禀 Riemann 全曲率为零。[X07 命题说明](docs/statements/flat-rigidity.zh-CN.md)

一般双极化 Rosen 命题（X05）从原文的物理一阶导数界推出完整动理学表示。同一图测度满足 Einstein 张量矩、Hamilton 输运恒等式和有限局部二阶矩条件。[X05 命题说明](docs/statements/rosen-two-polarization.md) · [数学复核](docs/statements/rosen-two-polarization-review.md)

F05 证明了固定零次齐次角向 Fourier 乘子的截断交换子作用于局部弱零序列后强趋零，并覆盖固定低频正则化。 [角向 Fourier 交换子与固定低频正则化](docs/statements/angular-cutoff-commutator.zh-CN.md)
F05 将紧空间上满足正性的连续测试泛函矩阵表示为一族有序复测度，并给出共同的有限支配迹。 [正矩阵值测度表示](docs/statements/positive-matrix-measure.zh-CN.md)

谐和坐标例子 X01 证明固定紧盒上的张量波源 L² 范数发散。各项度规内禀平直，序列满足原文的容许界。[X01 命题说明](docs/statements/harmonic-shear.zh-CN.md)

X04 构造了具有正零锥矩的实际光滑 Lorentz 度规，并排除所有正零射线输运表示。[X04 命题说明](docs/statements/bianchi-counterexample.zh-CN.md)
F08 的支持引理用光滑试验确定局部有限测度，并在给定有界边缘密度时分解有限联合测度。[局部测度分解](docs/statements/local-disintegration.zh-CN.md)

原文快照为 [`paper/burnett.tex`](paper/burnett.tex)，176424字节，SHA256：

```text
e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e
```

来源身份见 [`paper/source.json`](paper/source.json)。该副本保留用户原文件字节；Git 对该文件禁用行尾转换。

工程固定 **Lean 4.24.0** 和 **Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`**，其余依赖见 `lake-manifest.json`。该选择已由近期代数接口实际探针验证；中期测度、微局部分析与几何接口仍有待补的桥接和实现。

```powershell
lake exe cache get Mathlib.Algebra.BigOperators.Fin Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Algebra.Order.BigOperators.Ring.Finset Mathlib.Analysis.Calculus.BumpFunction.InnerProduct Mathlib.Analysis.Calculus.BumpFunction.Normed Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox Mathlib.Analysis.Calculus.ContDiff.Basic Mathlib.Analysis.Calculus.ContDiff.Defs Mathlib.Analysis.Calculus.ContDiff.Operations Mathlib.Analysis.Calculus.FDeriv.Add Mathlib.Analysis.Calculus.FDeriv.Congr Mathlib.Analysis.Calculus.FDeriv.Mul Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts Mathlib.Analysis.Calculus.VectorField Mathlib.Analysis.Distribution.FourierSchwartz Mathlib.Analysis.Distribution.SchwartzSpace Mathlib.Analysis.Fourier.FourierTransform Mathlib.Analysis.InnerProductSpace.Basic Mathlib.Analysis.InnerProductSpace.LinearMap Mathlib.Analysis.InnerProductSpace.PiL2 Mathlib.Analysis.Matrix.Order Mathlib.Analysis.Normed.Group.Bounded Mathlib.Analysis.Normed.Operator.Completeness Mathlib.Analysis.SpecialFunctions.Sqrt Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv Mathlib.Data.Complex.Basic Mathlib.Data.Real.Basic Mathlib.Geometry.Manifold.MFDeriv.Atlas Mathlib.Geometry.Manifold.VectorBundle.Riemannian Mathlib.Geometry.Manifold.VectorBundle.SmoothSection Mathlib.Geometry.Manifold.VectorBundle.Tangent Mathlib.Geometry.Manifold.VectorField.LieBracket Mathlib.LinearAlgebra.BilinearForm.Properties Mathlib.LinearAlgebra.Matrix.BilinearForm Mathlib.LinearAlgebra.Matrix.Kronecker Mathlib.LinearAlgebra.Matrix.PosDef Mathlib.LinearAlgebra.Matrix.Vec Mathlib.LinearAlgebra.Multilinear.Basis Mathlib.LinearAlgebra.Multilinear.Curry Mathlib.MeasureTheory.Function.ContinuousMapDense Mathlib.MeasureTheory.Function.Jacobian Mathlib.MeasureTheory.Function.L2Space Mathlib.MeasureTheory.Function.LpSeminorm.Basic Mathlib.MeasureTheory.Function.LpSpace.Basic Mathlib.MeasureTheory.Function.LpSpace.Indicator Mathlib.MeasureTheory.Integral.Bochner.Basic Mathlib.MeasureTheory.Integral.Bochner.Set Mathlib.MeasureTheory.Integral.DominatedConvergence Mathlib.MeasureTheory.Integral.IntegrableOn Mathlib.MeasureTheory.Integral.Prod Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace Mathlib.MeasureTheory.Measure.Haar.NormedSpace Mathlib.MeasureTheory.Measure.Lebesgue.Basic Mathlib.MeasureTheory.Measure.OpenPos Mathlib.MeasureTheory.Measure.Restrict Mathlib.MeasureTheory.Measure.WithDensity Mathlib.Order.Filter.AtTopBot.Archimedean Mathlib.Tactic.FieldSimp Mathlib.Tactic.FinCases Mathlib.Tactic.Linarith Mathlib.Tactic.NoncommRing Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Topology.Algebra.Module.Basic Mathlib.Topology.Algebra.Module.FiniteDimension Mathlib.Topology.Algebra.Module.Multilinear.Basic Mathlib.Topology.Algebra.Order.Field Mathlib.Topology.Compactness.Lindelof Mathlib.Topology.ContinuousMap.CompactlySupported Mathlib.Topology.Instances.Matrix Mathlib.Topology.Instances.Real.Lemmas Mathlib.Topology.MetricSpace.Cauchy Mathlib.Topology.MetricSpace.Pseudo.Basic Mathlib.Topology.Sequences Mathlib.Topology.UniformSpace.HeineCantor Mathlib.Topology.UniformSpace.UniformConvergence Mathlib.Topology.UrysohnsLemma Mathlib.Geometry.Manifold.BumpFunction Mathlib.LinearAlgebra.Trace Mathlib.Analysis.Matrix Mathlib.Analysis.Calculus.Deriv.Abs Mathlib.Analysis.ODE.PicardLindelof Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli Mathlib.Analysis.Calculus.ContDiff.FiniteDimension Mathlib.Analysis.Calculus.ContDiff.WithLp Mathlib.Geometry.Manifold.LocalDiffeomorph Mathlib.Analysis.SpecialFunctions.Integrals.Basic Mathlib.MeasureTheory.Function.LocallyIntegrable Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension Mathlib.Analysis.Calculus.Deriv.Prod Mathlib.Analysis.Calculus.LocalExtr.Basic Mathlib.Analysis.Normed.Module.FiniteDimension Mathlib.Analysis.ODE.Gronwall Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv Mathlib.Geometry.Manifold.PartitionOfUnity Mathlib.Geometry.Manifold.VectorBundle.Hom Mathlib.LinearAlgebra.Matrix.ToLinearEquiv Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap Mathlib.MeasureTheory.Measure.Regular Mathlib.Topology.MetricSpace.ProperSpace Mathlib.Analysis.Calculus.MeanValue Mathlib.Analysis.Complex.Basic Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff Mathlib.MeasureTheory.Function.SpecialFunctions.Basic Mathlib.MeasureTheory.Group.Integral Mathlib.MeasureTheory.Integral.MeanInequalities Mathlib.Data.Complex.BigOperators Mathlib.Data.Matrix.Basic Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real Mathlib.MeasureTheory.Measure.Complex Mathlib.MeasureTheory.Measure.HasOuterApproxClosed Mathlib.Topology.ContinuousMap.Star Mathlib.Probability.Kernel.Disintegration.Integral Mathlib.Probability.Kernel.Disintegration.Unique Mathlib.Probability.Kernel.WithDensity Mathlib.Probability.Kernel.CompProdEqIff Mathlib.Probability.Kernel.Composition.MeasureCompProd Mathlib.Analysis.Calculus.FDeriv.Measurable Mathlib.MeasureTheory.Covering.Vitali Mathlib.MeasureTheory.Integral.Layercake Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar Mathlib.Probability.Kernel.Composition.MapComap
python scripts/check_project.py --repo .
```

本机可用已存在的SDK：

```powershell
$env:PATH = 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin;' + $env:PATH
lake exe cache get Mathlib.Algebra.BigOperators.Fin Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Algebra.Order.BigOperators.Ring.Finset Mathlib.Analysis.Calculus.BumpFunction.InnerProduct Mathlib.Analysis.Calculus.BumpFunction.Normed Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox Mathlib.Analysis.Calculus.ContDiff.Basic Mathlib.Analysis.Calculus.ContDiff.Defs Mathlib.Analysis.Calculus.ContDiff.Operations Mathlib.Analysis.Calculus.FDeriv.Add Mathlib.Analysis.Calculus.FDeriv.Congr Mathlib.Analysis.Calculus.FDeriv.Mul Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts Mathlib.Analysis.Calculus.VectorField Mathlib.Analysis.Distribution.FourierSchwartz Mathlib.Analysis.Distribution.SchwartzSpace Mathlib.Analysis.Fourier.FourierTransform Mathlib.Analysis.InnerProductSpace.Basic Mathlib.Analysis.InnerProductSpace.LinearMap Mathlib.Analysis.InnerProductSpace.PiL2 Mathlib.Analysis.Matrix.Order Mathlib.Analysis.Normed.Group.Bounded Mathlib.Analysis.Normed.Operator.Completeness Mathlib.Analysis.SpecialFunctions.Sqrt Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv Mathlib.Data.Complex.Basic Mathlib.Data.Real.Basic Mathlib.Geometry.Manifold.MFDeriv.Atlas Mathlib.Geometry.Manifold.VectorBundle.Riemannian Mathlib.Geometry.Manifold.VectorBundle.SmoothSection Mathlib.Geometry.Manifold.VectorBundle.Tangent Mathlib.Geometry.Manifold.VectorField.LieBracket Mathlib.LinearAlgebra.BilinearForm.Properties Mathlib.LinearAlgebra.Matrix.BilinearForm Mathlib.LinearAlgebra.Matrix.Kronecker Mathlib.LinearAlgebra.Matrix.PosDef Mathlib.LinearAlgebra.Matrix.Vec Mathlib.LinearAlgebra.Multilinear.Basis Mathlib.LinearAlgebra.Multilinear.Curry Mathlib.MeasureTheory.Function.ContinuousMapDense Mathlib.MeasureTheory.Function.Jacobian Mathlib.MeasureTheory.Function.L2Space Mathlib.MeasureTheory.Function.LpSeminorm.Basic Mathlib.MeasureTheory.Function.LpSpace.Basic Mathlib.MeasureTheory.Function.LpSpace.Indicator Mathlib.MeasureTheory.Integral.Bochner.Basic Mathlib.MeasureTheory.Integral.Bochner.Set Mathlib.MeasureTheory.Integral.DominatedConvergence Mathlib.MeasureTheory.Integral.IntegrableOn Mathlib.MeasureTheory.Integral.Prod Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace Mathlib.MeasureTheory.Measure.Haar.NormedSpace Mathlib.MeasureTheory.Measure.Lebesgue.Basic Mathlib.MeasureTheory.Measure.OpenPos Mathlib.MeasureTheory.Measure.Restrict Mathlib.MeasureTheory.Measure.WithDensity Mathlib.Order.Filter.AtTopBot.Archimedean Mathlib.Tactic.FieldSimp Mathlib.Tactic.FinCases Mathlib.Tactic.Linarith Mathlib.Tactic.NoncommRing Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Topology.Algebra.Module.Basic Mathlib.Topology.Algebra.Module.FiniteDimension Mathlib.Topology.Algebra.Module.Multilinear.Basic Mathlib.Topology.Algebra.Order.Field Mathlib.Topology.Compactness.Lindelof Mathlib.Topology.ContinuousMap.CompactlySupported Mathlib.Topology.Instances.Matrix Mathlib.Topology.Instances.Real.Lemmas Mathlib.Topology.MetricSpace.Cauchy Mathlib.Topology.MetricSpace.Pseudo.Basic Mathlib.Topology.Sequences Mathlib.Topology.UniformSpace.HeineCantor Mathlib.Topology.UniformSpace.UniformConvergence Mathlib.Topology.UrysohnsLemma Mathlib.Geometry.Manifold.BumpFunction Mathlib.LinearAlgebra.Trace Mathlib.Analysis.Matrix Mathlib.Analysis.Calculus.Deriv.Abs Mathlib.Analysis.ODE.PicardLindelof Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli Mathlib.Analysis.Calculus.ContDiff.FiniteDimension Mathlib.Analysis.Calculus.ContDiff.WithLp Mathlib.Geometry.Manifold.LocalDiffeomorph Mathlib.Analysis.SpecialFunctions.Integrals.Basic Mathlib.MeasureTheory.Function.LocallyIntegrable Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension Mathlib.Analysis.Calculus.Deriv.Prod Mathlib.Analysis.Calculus.LocalExtr.Basic Mathlib.Analysis.Normed.Module.FiniteDimension Mathlib.Analysis.ODE.Gronwall Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv Mathlib.Geometry.Manifold.PartitionOfUnity Mathlib.Geometry.Manifold.VectorBundle.Hom Mathlib.LinearAlgebra.Matrix.ToLinearEquiv Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap Mathlib.MeasureTheory.Measure.Regular Mathlib.Topology.MetricSpace.ProperSpace Mathlib.Analysis.Calculus.MeanValue Mathlib.Analysis.Complex.Basic Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff Mathlib.MeasureTheory.Function.SpecialFunctions.Basic Mathlib.MeasureTheory.Group.Integral Mathlib.MeasureTheory.Integral.MeanInequalities Mathlib.Data.Complex.BigOperators Mathlib.Data.Matrix.Basic Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real Mathlib.MeasureTheory.Measure.Complex Mathlib.MeasureTheory.Measure.HasOuterApproxClosed Mathlib.Topology.ContinuousMap.Star Mathlib.Probability.Kernel.Disintegration.Integral Mathlib.Probability.Kernel.Disintegration.Unique Mathlib.Probability.Kernel.WithDensity Mathlib.Probability.Kernel.CompProdEqIff Mathlib.Probability.Kernel.Composition.MeasureCompProd Mathlib.Analysis.Calculus.FDeriv.Measurable Mathlib.MeasureTheory.Covering.Vitali Mathlib.MeasureTheory.Integral.Layercake Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar Mathlib.Probability.Kernel.Composition.MapComap
python scripts/check_project.py --repo . --lake 'D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lake.exe'
```

此 PATH 设置只影响当前终端，确保缓存程序内部再调用 `lake` 时也使用同一SDK。

入口核对原文身份、标准、固定运行时并构建库入口；对当前真实注册目标再调用 `scripts/check_paper.py` 做存在性、来源和传递公理审计。机器通过仍不能代替结果覆盖、语义对应或作者确认，`paper_formalization_verified` 保持false。没有目标的初始阶段仅输出 `project-setup-passed`。

- [`RicciSymbol.lean`](Burnett/Algebra/RicciSymbol.lean) 实现实数非特征核的显式规范表示和二次消去；[数学解释及实际声明](docs/statements/ricci-symbol.md)、[独立回读](docs/statements/ricci-symbol-review.md)。
- [完整实二次代数与零锥交叉](docs/statements/quadratic-real-algebra.md) 对应两条并行实现及主代理的实际拼接；[独立回读](docs/statements/quadratic-real-algebra-review.md) 记录输入版本、真实类型及未覆盖项。
- [实混合极化](docs/statements/real-polarization.md)及[独立实际类型回读](docs/statements/real-polarization-review.md)记录F06新增交付；[本轮监督实测报告](docs/formalization/f06-workflow-test.md)分别记录数学、流程、CI和未覆盖边界。
- [多代理并行工作流](docs/formalization/parallel-workflow.md) 记录分工与构建/快照交接；[GitHub PR与合并](docs/formalization/github-workflow.md) 规定独立复核、组合CI、候选交接及按项目授权执行合并。数学标准仍为1.2，当前skill与工程工作流为1.3.1；旧技能包保留。
- [点态Hermitian与二维物理类](docs/statements/hermitian-null-algebra.md)及[独立复核](docs/statements/hermitian-null-algebra-review.md)记录F06的57个新增支持目标，已随用户合并PR4进入main。PR5保留这些成果并加入X02，不重写已确认的数学源码。
- [`全文切片与依赖图`](docs/formalization/slices.md) 给出每段源码的归属、逐片输入输出、正式结果的陈述与闭合位置、共同闭合组及下一步；[机器清单](docs/formalization/slices.json) 与现有 scope 相连。运行 `python scripts/check_slices.py --repo .` 检查原文身份、分区、结果映射、依赖环和文档一致性；该结构检查不认证数学完备。
- [后续整体工作安排](docs/formalization/WORK-PLAN.zh-CN.md) 说明可交错的切片顺序、近期N1/N2/N3任务、依赖类型和共同闭合责任；实际数学状态仍以scope及适用证据为准。
- `python scripts/prepare_slice.py F06 --repo .` 导出指定切片的工作包，含锁定原文、当前清单状态、直接输入及消费者，保存于 `.project-verification/slice-packets/`；换用表中ID即可。每次续接重新导出，避免沿用过期状态。
- [切片独立复核与修订](docs/formalization/slicing-review.md) 记录新上下文代理的发现、相位隙反例及修复。工作包同时附本片开放外部接口与公共记录入口；这些待核输入不因导出而成为已证结果。
- [`主定理接口`](docs/statements/main-interface.md)、[`主线依赖`](docs/formalization/dependencies.md)、[`库调查`](docs/formalization/library-audit.md) 记录当前对象、量词、消费者和实际库证据。
- [`docs/statements/`](docs/statements/) 保存原文结果索引与未来数学/Lean对照。
- [`docs/formalization/scope.json`](docs/formalization/scope.json) 是范围与进度的主清单；完整二次代数父项仍为部分完成。
- [维护工具与PR交接](docs/formalization/maintenance-1.3.1.md)记录快照边界、完整保护比较和只读就绪判定；最终main合并由用户执行；PR就绪后按[目标续接规则](docs/formalization/GOAL.zh-CN.md)继续独立后继任务。
- [`docs/formalization/review.md`](docs/formalization/review.md) 记录实际复核及发布情况；[1.3版工作流对抗审核与测试](docs/formalization/workflow-review.md) 区分独立审查、模拟场景和真实GitHub检查。
- [`docs/formalization/standard.zh-CN.md`](docs/formalization/standard.zh-CN.md) 固定 `paper-results` 第1.2版标准。
- [`tools/lean-paper-results/`](tools/lean-paper-results/) 是1.3.1版skill与工程工作流的文本快照；维护负例套件无需逐篇论文重复运行。

2026-11-16用户选择A：全部数学依赖闭合，只接受scope所列三基础公理，可复用固定库证明。新点态复代数解释按用户明确委托由主代理与独立代理确认；不记为用户/作者本人逐行读过Lean。全文及测度/输运主线仍未完成；本轮X02固定Fourier目标的新增解释不沿用旧prop:cubic确认，后续推进F04分析桥和F05/F07共同协方差对象。

- [X02三线性反例](docs/statements/cubic-counterexample.md)及[复核](docs/statements/cubic-counterexample-review.md)记录完整正式命题与1A委托确认。[固定 Fourier 离锥目标](docs/statements/cubic-off-null-localization.md)分别记录 2A 批准范围、已实现的证明与尚待确认的新解释。PR5已由用户合并到main `242eebe9d87ef62c15efab8df7741051f0aed260`，[该提交的主线CI](https://github.com/Oho1e/Burnett-conjecture/actions/runs/43807809558)成功；该次人类操作不增加代理后续合并权限。

后续 PR 按[双语目标](docs/formalization/GOAL.zh-CN.md#双语交付)同步更新中英文说明。

可数覆盖上的测度分解定理为给定的联合测度构造具有指定质量的有限纤维测度。[F08 假设与结论](docs/statements/countable-fiber-disintegration.zh-CN.md)
F05 已建立首选图重叠域上的几何体积配对及近场、远场核变量几何界。[假设与结果](docs/statements/chart-overlap-geometry.zh-CN.md)
已证明原真空序列的局部一致收敛与紧集一阶导数界在任意两个光滑辅助黎曼度量之间等价。 [辅助度量变换下的真空序列假设](docs/statements/auxiliary-metric-admissibility.zh-CN.md)
原文第 626–677 行取一个在非零频率上光滑的实一次齐次符号。以下结果覆盖原文符号分解及其 Schwartz 测试配对。 [三次能量交换子的 Fourier 符号](docs/statements/cubic-energy-fourier-symbols.zh-CN.md)
原文第 626–685 行在三次能量证明中使用有限指数乘子界。以下解析引理用于该证明。 [四维极大函数与环带平方估计](docs/statements/harmonic-maximal-and-square-estimates.zh-CN.md)

A02 的低频因子有实际卷积公式以及对全部正尺度的强 Lᵖ 极大函数界。 [四维移位 Fourier 窗估计](docs/statements/shifted-fourier-window-estimates.zh-CN.md)

两侧空间截断下，连续衰减 Fourier 乘子的紧性已证，可用于局部负一阶余项的固定基底 Fourier 频率。 [双侧空间截断的紧 Fourier 乘子](docs/statements/compact-frequency-localization.zh-CN.md)

有符号环带和具有统一 L² 界，其实际卷积核满足积分 Hörmander 条件。 [四维有符号 Fourier 窗估计](docs/statements/signed-fourier-window-estimates.zh-CN.md)

已证明有符号环带和及环带平方函数的有限指数 Lᵖ 界，以及两个环带因子和一个低频因子的乘积估计。继续接入全尺度联合乘子界及其三次能量应用。 [四维环带平方函数与乘积估计](docs/statements/annular-square-and-product-estimates.zh-CN.md)

全尺度联合 Fourier 乘子已在 Schwartz 测试上得到定量三线性界。继续通过对偶接到实际双线性输出，并装配标量乘子界和三次能量。 [定量联合 Fourier 乘子估计](docs/statements/joint-fourier-multiplier-estimates.zh-CN.md)

实际一阶行已有 Bessel 主部定位，原度规列已有坐标旋度约束。继续接入 Ricci 行、同一抽取的有序测度和密度约束。 [F05 一阶定位与原度规列的坐标旋度](docs/statements/bessel-and-coordinate-curl.zh-CN.md)

实际双线性输出、谱输入和标量 Fourier 乘子已有有限指数界。继续装配实际交换子的定量界及完整三次能量。 [实际双线性与标量 Fourier 乘子](docs/statements/bilinear-fourier-operators.zh-CN.md)

完整齐次及固定正则化能量、有穷指数交换子和混合系数界均有 Lean 证明。原文命题确认及空间变系数应用另有后续工作。 [Lean 库中的完整三次能量](docs/statements/complete-cubic-energy.zh-CN.md)

实际屏幕约束、统一宽锥正下界、偶性、零次齐次性及冻结代数相位已有 Lean 证明。后续接续光滑性、全局截断和变分算子接口。 [冻结屏幕与相位恒等式](docs/statements/frozen-screen.zh-CN.md)

在登记的符号及支撑假设下，完整左量子化的标量、矩阵主能量配对和两条固定图密度估计已有 Lean 证明。后续须将原文算子类和下游 Weyl 作用与这些 Lean 输入对接。 [主能量交换子估计](docs/statements/a01-principal-energy.zh-CN.md)

角帽批次证明了基本帽和放大帽的统一场乘子估计，以及薄锥三元组低槽远角区的精确相位下界。 [角帽与有符号相位下界](docs/statements/angular-cap-geometry.zh-CN.md)

P01 的有限维规范补投影、固定红外正则化及带权零阶符号估计已有 Lean 证明。 [固定规范补投影及其零阶符号](docs/statements/fixed-gauge-projection.zh-CN.md)

固定投影已有 Schwartz 乘子及温和分布对偶作用、对称梯度消去和逐系数有限指数估计。 [固定规范补投影的 Fourier 作用](docs/statements/gauge-projection-fourier-action.zh-CN.md)

固定矩阵投影在有限指数下控制投影场和梯度，并给出固定截断后投影场的全空间 Lᵖ 收敛。 [固定投影场的有限指数范数](docs/statements/projected-field-finite-lp.zh-CN.md)

统一 Lipschitz 界与输入一致小性给出同一固定投影场的全空间一致趋零和 L∞ 收敛。 [固定投影场的一致趋零](docs/statements/projected-field-uniform-convergence.zh-CN.md)

原开图与内禀输入已给出同一个实际投影场的有限指数范数、梯度界和一致趋零。 [原开坐标图上的投影场范数](docs/statements/open-chart-projected-norms.zh-CN.md)

固定投影的红外因子已具备实际卷积公式和只用系数 Lipschitz 界的梯度型 L² 交换子估计。 [固定红外因子的梯度交换子](docs/statements/projection-infrared-commutator.zh-CN.md)

固定矩阵投影的梯度交换子已取得全局 Lipschitz 系数下的 L² 有界延拓。 [固定矩阵投影的梯度交换子](docs/statements/projection-hodge-commutator.zh-CN.md)

已用同一个固定投影接通坐标真空余项与全空间负散度的统一 L² 界。 [投影真空余项与全空间散度源](docs/statements/projected-vacuum-source.zh-CN.md)

从内禀真空序列导出的投影范数和全空间散度界已推广到任意相容光滑图。 [任意光滑图上的统一投影散度源](docs/statements/maximal-chart-projected-source.zh-CN.md)

给定原矩阵配对见证时，固定投影的实际配对取得两槽协方差，并保持给定 Ricci 核振幅的完整零壳物理测度。 [固定投影的角向协方差与物理测度](docs/statements/projected-angular-covariance.zh-CN.md)
