# 固定 Mathlib 接口调查

调查日期：2026-11-15。对象为本机父工作区已有的 Mathlib checkout，**不是最新版本调查**。以下只报告库身份、接口和探针结果；项目依赖接入及论文目标状态由现有工程记录管理。

## 版本与证据边界

- SDK：`D:\Chatpgt\Lean形式化\.tools\lean-4.24.0-windows\bin\lean.exe`，实际输出 Lean **4.24.0**，编译器提交 `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`。
- Mathlib 源码：`D:\Chatpgt\Lean形式化\.lake\packages\mathlib`；实际 Git HEAD 为 **`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`**，与父工作区 `lakefile.toml`、`lake-manifest.json` 的锁定值相同；源码 `lean-toolchain` 也是 4.24.0。
- 已实际检查 Git 元数据、独立仓库顶层及工作树状态：Mathlib 和另外8包均有 `.git`，HEAD 逐一等于父 manifest；`git status --porcelain=v1 --untracked-files=normal` 均无输出。这一结论来自实际 checkout 检查，不能仅由 manifest 推出。
- 该状态检查不覆盖忽略的构建缓存。现有缓存不完整；成功载入某些 `.olean` 不证明所有缓存均从当前干净源码重建。这里不作缓存来源完整性背书。
- 直接调用 SDK Lean，`LEAN_PATH` 仅指向父工作区9包中已有缓存目录的8包（`Cli` 没有该目录）；没有运行共享库的 `lake build/update`、下载、安装或远程命令。探针及日志全部在本工程 `.project-verification/library-audit/`。

本地证据：`source-identity.json` 逐包保存 HEAD、锁定值、origin、顶层和工作树状态；`module-evidence.json` 保存所查模块源码 SHA256 及 `.olean` 是否存在；`source-excerpts.log` 保存下述源码签名的行号摘录。依赖工程改变时，应在新固定环境重跑受影响检查。

## 近期：Ricci 符号及实有限维代数

原文定位：`paper/burnett.tex:415–452`。推荐沿用当前 **Lean 4.24.0 + 上述 Mathlib commit** 作首批代数接口的固定基线：本机已有匹配源码，以下最小探针已经成功运行；这不是分析部分库闭包已经齐备的结论。

实际通过的导入组：

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
```

`AlgebraProbe.lean` / `AlgebraProbe.log` / `AlgebraProbe.result.json`：**exit 0**。已执行 `#check` 和非空例子证明，覆盖：

| 接口 | 已核实签名或行为 | 对近期建模的用途 |
| --- | --- | --- |
| `ℝ`、`Fin 4` | 实数实例和有限索引可用 | `Fin 4 → ℝ`、`Matrix (Fin 4) (Fin 4) ℝ` |
| `Fin.sum_univ_succ` | `∑ i : Fin (n+1), f i = f 0 + ∑ i, f i.succ`；`AddCommMonoid` | 实测将4项求和展开为4项加法 |
| `Finset.sum_comm` | 在 `AddCommMonoid` 中交换两重有限和 | 实测 `∑ a : Fin 4, ∑ b : Fin 4, f a b` 的换序 |
| `Finset.sum_mul`、`Finset.mul_sum` | 有限和与左右乘法分配 | 展开收缩与二次项 |
| `Finset.sum_congr` | 索引集合相等且逐项相等推出和相等 | 逐分量处理对称性、逆矩阵关系 |
| `Matrix.mul_apply` | `(M * N) i k = ∑ j, M i j * N j k`；`Fintype`、`Mul`、`AddCommMonoid` | 已实测4维矩阵乘法分量公式 |
| `Matrix.mulVec`、`Matrix.transpose` | 分别为矩阵作用于列向量、转置 | 升降指标、对称性接口的底层表示 |
| `field_simp [hs]` | 实测 `s ≠ 0` 下消去分母，随后 `nlinarith only [h]` 解线性关系 | 对应非特征情形除以 `s`；必须保留非零假设 |
| `ring` | 实测实数三项平方的完整展开恒等式 | 点态多项式恒等式归一化 |

`ring` 不自动处理未展开的有限和、矩阵乘法或未知指标置换；先用有限和 API 及对称性/逆关系规整，再处理标量多项式。探针只验证这些操作可用，没有证明论文的 Ricci 或 `B` 恒等式。

原文明确对所有**有序指标对**求和（428行）。近期可直接使用全体 `Fin 4 × Fin 4` 的双重和，避免把对称矩阵改成10个独立分量后漏掉非对角重数。Lorentz 度规的双线性配对与辅助正定内积需要各自建模。

已发现的具体导入/缓存限制：

- `Matrix.IsSymm` 在 `Mathlib.LinearAlgebra.Matrix.Symmetric:29`，定义为 `Aᵀ = A`，`IsSymm.ext_iff` 给出逐分量版本；`Data.Matrix.Basic` **不导出**这个名字。
- 上述 `Symmetric` 源码存在，但本机对应 `.olean` 缺失。直接导入已实际失败，日志为 `AlgebraProbe.missing-symmetric-cache.log`。当前可以显式使用 `∀ a b, k a b = k b a`；若接入该标准模块，应在项目独立依赖环境中构建。
- 初次探针的名字/简化失败也保留在 `AlgebraProbe.initial-failed.log`；最终通过结果以 `AlgebraProbe.log` 为准。不能将本机缺缓存写成库中缺定理。

## 中期导航与尚需桥接的接口

证据分为：**执行核签**（Lean 实际 `#check/#print` 或例子通过）、**源码核签**（已读固定源码定义、类型与上下文，尚未在本轮环境编译）、**候选**（相关组件，但未完成目标接口匹配）、**有限检索未定位**。后三者不能登记为已完成论文依赖。

### 有限 Hermitian 正性

**源码核签**：

- `Mathlib.LinearAlgebra.Matrix.Hermitian:41`：`Matrix.IsHermitian A := Aᴴ = A`。
- `Mathlib.LinearAlgebra.Matrix.PosDef:47`：在 `[Fintype n] [Ring R] [PartialOrder R] [StarRing R]` 下，`Matrix.PosSemidef M` 是 `M.IsHermitian ∧ ∀ x : n → R, 0 ≤ star x ⬝ᵥ (M *ᵥ x)`。
- 同模块 `:67` 的 `Matrix.PosSemidef.re_dotProduct_nonneg` 在 `[RCLike 𝕜]` 下给出该二次式实部非负；`:71` 的 `conjTranspose_mul_mul_same` 给出 `A.PosSemidef → (Bᴴ * A * B).PosSemidef`。

这两个模块的本机 `.olean` 均缺失，未执行 Lean 核签。固定源码使用 `open scoped ComplexOrder` 处理复数上的非负性；应用时须保留相应实例/作用域，或使用实部非负版本。有限复数协方差正性可从这里起步；从坐标协方差到纤维算子的 Gram 矩阵变换、Hermitian 测度密度及 a.e. 核约束仍需专用证明。不能把矩阵半正定谓词直接当成原文的正 Hermitian 丛值测度。

### 弱收敛、紧性与下半连续

**源码核签**：

- `Mathlib.Topology.Algebra.Module.WeakDual:133,177` 有 `WeakSpace 𝕜 E` 和线性等价 `toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E`；它们改变拓扑，不能默默当作原范数拓扑。
- `Mathlib.Analysis.LocallyConvex.WeakSpace:36` 的 `Convex.toWeakSpace_closure`：在实/复、适当连续运算及实局部凸假设下，凸集的闭包经 `toWeakSpace` 的像等于弱拓扑下的像之闭包。上下文类型假设见证据摘录，不能省略。
- `Mathlib.Analysis.Normed.Module.WeakDual:254` 的 `WeakDual.isCompact_closedBall`：`[ProperSpace 𝕜]` 下，强对偶闭球在弱星对偶中对应的集合是紧的。它是**对偶空间**结论；应用于 `L²` 原空间须另给表示/自反性桥接。
- `Mathlib.MeasureTheory.Measure.FiniteMeasure:679` 的 `MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto`：有限测度弱收敛等价于对所有 `Ω →ᵇ ℝ` 的积分收敛，背景需要拓扑、可测空间及开集可测。
- `Mathlib.MeasureTheory.Measure.Portmanteau:273` 的 `FiniteMeasure.limsup_measure_closed_le_of_tendsto`：在 `[HasOuterApproxClosed Ω] [OpensMeasurableSpace Ω]` 下，对闭集 `F` 有 `limsup μᵢ(F) ≤ μ(F)`。

以上模块缓存均缺失，属源码核签。有限测度弱收敛不能直接替代局部有限 Radon 测度的 vague 收敛或 bundle-valued defect 的提取。

**执行核签**：`Mathlib.Topology.Algebra.Module.WeakBilin:104` 的 `WeakBilin.tendsto_iff_forall_eval_tendsto`：对分离点的双线性配对 `B`（需 `Function.Injective B`），弱拓扑收敛等价于对每个测试向量的标量配对收敛。`WeakBilinProbe.lean` 的 `#check` **exit 0**，完整类型及结果见对应日志与 `WeakBilinProbe.result.json`。

**候选桥接**：范数弱下半连续可先调查闭凸球与 `Convex.toWeakSpace_closure` 的组合。对四个指定弱拓扑模块搜索 `lowerSemicontinuous`、`norm/liminf` 未定位可直接调用的范数下半连续声明；本轮未证明该桥接，也未据此断言 Mathlib 全库没有相应结论。

### Radon、密度与流形上的测度

**执行核签**：`RegularMeasureProbe.lean` 导入 `Mathlib.MeasureTheory.Measure.Regular`，`#check/#print` **exit 0**。

- `MeasureTheory.Measure.Regular μ` 包含紧集上有限、外正则以及开集对紧集的内正则。
- `MeasureTheory.Measure.InnerRegular μ` 另要求可测集对紧集内正则。这些概念不能只凭词语 “Radon” 相互替换；固定源码开头说明了两种 Radon 约定。
- `Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` 的实际实例要求 `[PseudoMetrizableSpace X] [SigmaCompactSpace X] [BorelSpace X]`，以及 `μ` 局部有限；详见探针完整签名。

**源码核签/候选**：

- `Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym:56` 的 `Measure.withDensity_rnDeriv_eq (μ ν)` 需 `[HaveLebesgueDecomposition μ ν]` 和 `μ ≪ ν`，结论为 `ν.withDensity (μ.rnDeriv ν) = μ`。这是标量测度结论，不能直接推出矩阵值密度的正性及可测性。
- `Mathlib.MeasureTheory.VectorMeasure.Basic:57` 有 `MeasureTheory.VectorMeasure`，可作有限维分量测度的候选底层。尚未核定它与本论文局部有限丛值 Hermitian 测度的具体对应及变换律。
- `Mathlib.Geometry.Manifold.VectorBundle.Riemannian:238` 有 `ContMDiffRiemannianMetric`，`Geometry.Manifold.Riemannian.Basic:77` 有 `IsRiemannianManifold`；已读出的内容提供光滑内积/长度结构。本轮没有定位或构造论文所需的全局正密度 `dV`、坐标体积变换和余球丛上的丛值测度接口。

后三类模块本机缓存缺失。原文在不同辅助度规、坐标及纤维标架之间的协方差变换仍需单独落实，不能由存在一般流形或测度模块推断已经可用。

### PDO、Calderón 型估计与 microlocal defect

**源码核签**：`Mathlib.Analysis.Distribution.FourierSchwartz:31` 有 `SchwartzMap.fourierTransformCLM : 𝓢(V,E) →L[𝕜] 𝓢(V,E)`，背景包括有限维实内积空间 `V`、`RCLike 𝕜` 及兼容的复数标量作用。这是相关 Fourier 基础组件，本机未缓存该模块。

**有限检索未定位**：在 `Analysis/Distribution`、`Analysis/Fourier`、`Geometry/Manifold` 三个限定子树中，以 `pseudodifferential`、`pseudo.differential`、`Calder[oó]n`、`microlocal`、`defect measure`、`symbol calculus` 检索，未定位可直接匹配的声明。范围和 exit code 保存在 `bounded-search.log`。没有全库泛搜；不据此断言这些理论绝不存在。

本论文实际消费者还需要：经典齐次零阶符号与红外正则化、有限符号半范数控制的算子界、负一阶局部紧性、交换子的阶数/主符号以及正 microlocal defect 的提取和定位。现有 Fourier/Schwartz 组件与这些定理之间的桥接尚未核定；它们应继续作为显式待证依赖，不能隐藏进结构字段后报告已闭合。本文档不给分析部分完成工期或全库覆盖保证。

## 复查入口

在工程根目录运行以下脚本，只写审计自有目录；它们不接入项目依赖：

```powershell
& .\.project-verification\library-audit\source-identity.ps1
& .\.project-verification\library-audit\collect-evidence.ps1
& .\.project-verification\library-audit\run-probes.ps1 -Probe AlgebraProbe
& .\.project-verification\library-audit\run-probes.ps1 -Probe RegularMeasureProbe
& .\.project-verification\library-audit\run-probes.ps1 -Probe WeakBilinProbe
```

`.project-verification/` 为忽略的本机证据，不随仓库传输。独立依赖接入完成后，应在项目自身固定的依赖环境验证实际导入与证明；父工作区探针的 exit 0 不能替代项目构建或论文结果的机器检查。
