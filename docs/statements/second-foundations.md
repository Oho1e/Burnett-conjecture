# 第二批基础证明：L² Fourier、连接差与正密度核

2026-11-16；接续第一批已复核候选 `d143c3709466bd2900e098c573c1691d987226da`，该批现已由用户合并为main `b4b27302556c62617798a46a22e744035fcd4602`且主线CI通过。本文记录本批的数学解释；实现、独立回读、机器检查、作者确认和主线合并分别记载，不据此宣告全文完成。原文、信任A及固定依赖保持不变。

## L² Fourier 的实际构造

对任意有限维实内积空间 V，使用其体积测度。`SchwartzDensity.lean` 证明真实映射

```lean
DenseRange (fun f : SchwartzMap V ℂ => f.toLp 2 (volume : Measure V))
```

证明先在 L² 中用连续紧支撑函数近似，再一致光滑近似并乘一个在原支撑上等于1的固定光滑紧截断。误差由该固定截断的有限 L² 范数控制；没有把全空间总体积当作有限，也没有把稠密性作为输入。

`L2Extension.lean` 在实际 L² 中取 Schwartz 像的线性子空间，赋予继承的 L² 范数。已证 Parseval 给出该子空间上的 Fourier 线性等距映射，再沿稠密包含连续延拓。逆 Schwartz Fourier 使延拓的像稠密，完整 L² 上等距映射的像闭，因而得到满射及实际等距同构

```lean
fourierL2Equiv : Lp ℂ 2 volume ≃ₗᵢ[ℂ] Lp ℂ 2 volume
```

正、逆映射在 Schwartz 输入上均与实际积分变换几乎处处一致，沿用原有 `2π` 归一化。没有把 Schwartz 的 Fréchet 拓扑当作 L² 范数拓扑；一般任意 L¹∩L² 输入与积分的一致性未在本批另证。

`Projection.lean` 从实际有界可测频率符号 m 构造乘法连续线性算子，再定义物理空间算子 F⁻¹mF，证明其 L² 范数界及由频域支集能量控制的估计。`SharpProjection.lean` 对可测集的特征函数构造实际锐投影，证明幂等性和正交性；几乎处处相等的符号给相同物理算子。

`OffNullProjection.lean` 将这些算子实例化于原文3193行的同一 fSequence、wSequence。对每个固定 δ>0、任意原有实 χ∈C∞c，以及固定有界可测 m（只在非零离锥区域 Eδ 上支撑），四分量的正欧氏全空间 L² 范数满足

\[
 A_m(\chi\nabla f_n),\quad A_m(\chi\nabla w_n),\quad
 A_m(\nabla(\chi f_n)),\quad A_m(\nabla(\chi w_n))\longrightarrow0.
\]

实际主声明为 `Burnett.CubicOffNull.fixed_offNull_gradient_localization_away_zero`。锐锥特征函数和离零光滑的有界符号均有具体实例。零频单点以体积零及几乎处处符号相等消去；逆变换后的物理输出仍取全空间 L²，没有截去非紧支撑尾。χ、δ、m 在 n→∞ 前固定，不宣称对变动 δ、序列相关符号或一般变系数 PDO 的一致结论。两种截断位置由真实乘积法则和幅度小量接合，没有交换非局部投影与 χ。

## F04 的真实局部连接差

`ConnectionDifference.lean` 从真实双线性度规及其坐标分量的 Fréchet 导数计算 Christoffel 系数。对两度规 g₀、g₁，令 h=g₁−g₀，背景连接取 Γ(g₀)，实际证明

\[
\Gamma(g_1)^a{}_{bc}-\Gamma(g_0)^a{}_{bc}
=\frac12 g_1^{ad}
  (\nabla_bh_{cd}+\nabla_ch_{bd}-\nabla_dh_{bc}).
\]

逆矩阵由非退化双线性形式构造，零挠及度规相容由公式证明。最终点态定理只要求选定点非退化、逐分量可微，及邻域内对称；开图版本在 U 内给出正则性，不要求整个坐标空间上的非退化或光滑。邻域等值不会改变坐标一阶 jet。

## F04 的精确坐标 Ricci 差

`CurvatureDifference.lean` 计算一个上标、两个下标的张量 C 的真实背景协变导数。对两个在 x 处零挠、逐分量可微的连接场，令 C=Γ₁−Γ₀，实际证明

\[
\operatorname{Ric}(\Gamma_1)_{bc}-\operatorname{Ric}(\Gamma_0)_{bc}
=\nabla_aC^a{}_{bc}-\nabla_cC^a{}_{ba}
 +C^a{}_{ae}C^e{}_{bc}-C^a{}_{ce}C^e{}_{ba}.
\]

导数使用实际 Fréchet 导数，未把连接差的导数独立假定成所需表达。Γ₁ 的 Ricci 数组为零时给出原文精确真空式的同号形式。

`CurvatureSymbolBridge.lean` 另实际证明：秩一 jet `ξ⊗k` 代入精确 Christoffel 构造恰给旧 F06 的 `connectionSymbol`，本节的 `quadraticDifference` 恰为旧 `quadraticSymbol`（原文 B）的负值。后续由精确式推弱 Ricci 矩时必须保留这个负号；不能把两个二次定义直接视作相等。

这是坐标连接场恒等式。把两场统一实例化为随点变化的 Levi–Civita 系数并从度规正则性推出所需连接正则性、流形自然性、Eₙ 估计、弱 Ricci 极限和局部 H⁻¹ 紧性仍需后续工作；F04 整片不能据这两个模块判为闭合。

## F05 的正密度到系统核桥

`PositiveKernel.lean` 的有限维代数桥以真实 Hermitian 半正定矩阵 M 和相容尺寸矩阵 A 为对象，实际从 AM Aᴴ=0 推出 AM=0，进而给出实际线性映射的 range(M)⊆ker(A)。M 允许奇异，系统的行指标甚至无须有限；非零奇异 M、非零 A 的例子也已实际核签。这个有限维步骤不构造缺陷测度，也不自动给出几乎处处的矩阵压缩为零。

独立回读及冻结版本见[本批复核记录](second-foundations-review.md)和源码绑定。原文协方差张量与任意 Gram 下的自同态矩阵有别；应用时仍须提供正确的正 Hermitian 表示。

## F05 的稠密测试延拓工具

`DenseTests.lean` 对真实连续线性泛函序列 uₙ:E→L[ℝ]ℝ，消费显式统一算子范数界 ‖uₙ‖≤C 及稠密集 D 上的逐点收敛，先证明每个 x 的值为 Cauchy 序列，再构造实际唯一连续线性极限 L，证明全 E 上逐点收敛且 ‖L‖≤C。E 不需要完整；结论不包含 uₙ 的算子范数收敛。

另有显式误差 errₙ(x)→0 及最终下界 −errₙ(x)≤uₙ(x) 推出 L(x)≥0 的定理。原PDO是否满足这些界、所用测试范数是否正确，以及Gårding/平方分解误差是否趋零，均须在实际消费者中证明；本工具不把有限阶符号导数界替换成 C⁰ 界，也不构造缺陷测度。下一接口见[两次延拓调查](../formalization/dependency-audit-round2.md)。

## 共同边界

本批是 F04/F05/X02 的实际证明依赖，不是二次缺陷测度、输运或主定理的证明。新增数学解释的作者确认尚未记录；旧 F06/X02 局部委托仅沿其原有范围继承。整篇继续 `development`、`verified=false`。
