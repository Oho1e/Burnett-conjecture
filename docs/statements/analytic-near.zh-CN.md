# 全尺度三线性传递与近角求和

[English](analytic-near.en.md) · [源码绑定](analytic-near-source-bindings.json)

锁定论文 `lem:analytic-near` 的陈述在第 1026–1057 行，证明延伸至第 1245 行。登记目标是模块 `Burnett.Analysis.AllScaleTransfer.OriginalAtlasFormBounds` 中的 `Burnett.A05.exists_analyticNear_original_allScale_of_atlases`。它估计剥离三槽一阶微分权重后的实际 radian 三线性形式。 [论文源码](../../paper/burnett.tex#L1026-L1245)

| 原文要求 | Lean 对应 |
| --- | --- |
| 同时正缩放下零齐次 | 符号在三个频率均非零的有向平面 `(p,q,-(p+q))` 上同时正缩放零齐次。三线性形式的输入是三个已经微分的因子。 |
| 三个低比率端点和可比频率环形盒 | `AnalyticNearPositiveAtlas` 使用带符号球面图，要求正物理比率上的点值公式和延伸至零比率的单侧 `C¹⁰⁰` 界。`AnalyticNearComparableBudget` 在固定归一化盒上对实际可比乘子作 `C¹⁰⁰` 延拓，覆盖所需的有限相对移位。可比分支估计保留第三因子的环形截断。 |
| 相邻薄锥帽与因子 `δ²` | `AnalyticNearAdjacentSupport` 给出三槽薄锥条件和两条投影角界。薄宽为 `η = cκδ²` 时，`AnalyticNearSignedCapProfiles` 要求每个基帽的四张带符号剖面，采用实际局域符号除以 `δ²`、延伸至零点的物理比率和同一坐标中的可比盒。扩大帽符号包含薄锥乘子。 |
| 一致的全尺度界和薄角衰减 | `AnalyticNearFormBound` 的系数分别为 `C₀*A` 和 `Cnear(pStar)*A*δ^(2*(pStar-3)/(pStar-2))`。未加帽界的常数在分割和红外窗固定之后选取。在紧度规族及帽参数固定后，角向常数先于单个度规、薄宽、帽族、符号和输入选取。右侧使用三个原因子的 `L³` 范数。 |
| 逐因子 dyadic 截断和固定红外截断 | 同一常数控制完整形式和每组三个独立的有限光滑 dyadic 截断，复权模至多为一。每槽均可使用各自固定的光滑径向高通窗。 |

四个分支的权重之和为一。在非零有向三频处，权重非零的一支通过相应图册或可比盒在邻域中确定原符号，逐支零阶界相加控制其大小。近角一侧用扩大帽平顶取得非零三频的邻域，再由有限和恢复原符号。证明在这一频率域推出连续性和一致有界性，并构造有界 Borel 代表和可测零比率迹。几乎处处相等保证原符号的形式保持相同。可比盒的前两槽落在环形窗上且第三频率为零时，可比权重逐点为零。

支持定理 `exists_analyticNear_original_allScale_Lp3_of_atlases` 把这些形式延拓到三个任意复值 `L³(ℝ⁴)` 因子。带固定窗的完整形式和每组三个独立的有限 dyadic 截断各有一个连续三线性延拓，并在对应的 Schwartz 输入上与原形式相等。算子范数在未加帽情形至多为 `C₀*A`，在近角情形至多为 `Cnear(pStar)*A*δ^(2*(pStar-3)/(pStar-2))`，两界对允许的有限指标集和权重一致。证明把各槽乘子纳入同一二频符号，再用已有的 Schwartz 稠密延拓保留原常数。

形式陈述采用满足 `0 < κ < 1/16` 及 `7κ/4 < b` 的固定光滑分割、带符号图册和环形盒，以及实际帽族和坐标图。图册半径及相对移位范围同时满足正则性证明和原形式估计，薄宽上限由一致的抛物坐标几何限制。这些具体选择与原文的数学对应仍待作者确认。 [源码绑定与核验哈希](analytic-near-source-bindings.json)
