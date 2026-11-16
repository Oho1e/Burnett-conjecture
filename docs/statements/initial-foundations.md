# 第一批基础证明：纤维坐标、共同子列与固定 Fourier 离锥工具

本文对应工作文件的 N1/N2/N3。所有新目标是原结果的支撑结论；没有把未完成的 `thm:quadratic`、输运、主定理或固定 Fourier 投影目标登记为已证。固定文章、Lean 4.24.0、mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` 和三公理政策保持不变。

## 1. 真实纤维度规与 F06 坐标接口

令 V 为实向量空间，b 为以 Fin 4 编号的真实基，g 为非退化双线性形式。定义 covariant 分量 `G_ij=g(b_i,b_j)`，以及左降指标映射 `flat(v)=g(v,·)` 的真实逆 `sharp`。本轮从 metric-dual basis 构造 contravariant 分量，没有把矩阵逆恒等式或 Ricci 结论放进结构假设。

**约定边界：一般非对称 g 下，该构造与左降指标约定一致，对应 G⁻ᵀ。** 真正度规应用中 g 对称；两个 `covariant_mul_contravariant` / `contravariant_mul_covariant` 定理显式要求 `g.IsSymm`，此时构造的是通常的 G⁻¹。有限和 `raiseCovector` 是真实 `sharp ξ` 的坐标，`symbolNorm` 则是 `ξ(sharp ξ)`。

再给 V 的另一个真实基 c，令 E 的列为 c 在 b 下的坐标。已证明旧变换的实际含义：协向量为 Eᵀξ，协变双线性张量为 EᵀKE，且协向量变换双射。

若给定的是对**协变形式本身**的 Lorentz 正交基等式

```text
g(c_a,c_d) = η_ad,   η = diag(-1,1,1,1),
```

则推导 contravariant 分量为 EηEᵀ，并实际构造旧 `TensorFrame.LorentzFrame`。因此可以把既有 F06 的实零锥 Ricci 核物理配对非负性用于这一真实纤维数据。前提仍有非零 ξ、对称幅度 k、零锥条件及实际 Ricci 符号核条件，未删除这些假设。

本轮还给出显式 `modelMetric c(v,w)=Σ_a η_a c^a(v)c^a(w)` 的非退化证明与标准 ℝ⁴ 实例，排除单纯声明一个没有实例的证书。`standardFiberFrame` 是实际定义，另做实际类型/传递公理核查，未伪装成论文定理目标。

尚缺：从另一套独立的惯性指数/signature 定义推出正交基存在、局部光滑选择、流形拼接、连接/Ricci、体积密度及测度协方差。不能将“给定点态正交基”表述成这些内容已经形式化。

## 2. F05 的可数测试共同子列

对可数索引 ι、一个第一可数拓扑空间 X，以及每个测试的紧取值集 K_j，若 `a_n(j)∈K_j`，则存在一个严格递增 φ 和极限 l_j，使每个测试沿**同一** φ 同时收敛，且 `l_j∈K_j`。实数推论是：若 `|a_n(j)|≤C_j` 对 n 一致成立，则极限保留同一界。

证明使用可数积中的紧性及第一可数性，没有把一般弱星紧集的紧性直接当成序列紧性。一个紧集下的收敛子网不能替代此处严格递增的序列子列。

这是 F05 原文398–403行的共同子序列步骤可消费的工具；**不是**正微局部缺陷提取定理。真实 PDO 测试有界性、可数稠密测试族的构造、向全部符号延拓、正性、测度表示和图册/丛过渡仍需各自证明。这里一般测试的有界/紧值假设没有被算作原论文已提供的 Lean 证明。

## 3. X02 频率几何与真实 Fourier 尾

沿用原 `fSequence`、`wSequence`，N=n+1，u=t−x，v=t+x。实际梯度的 f 两个余弦相位角频率为

```text
κ_f,s = (N²+sN, -N²+sN, 0, 0),  s=±1,
κ_w   = (2N, 2N, 0, 0).
q(ξ)  = -ξ₀²+ξ₁²+ξ₂²+ξ₃².
```

实际定理把这些向量与逐分量导数连接起来；不是手填频率后忽略原函数。q(κ_f,s)=−4sN³，`‖κ_f,s‖²=2N⁴+2s²N²`，w 频率严格为零锥方向，且这些频率范数趋于无穷。

对固定 δ>0，`Eδ={ξ≠0 : δ‖ξ‖²≤|q(ξ)|}`。若 κ≠0 且 `|q(κ)|≤δ‖κ‖²/8`，则对 Eδ 内**全部** ξ 有

```text
min(1/2, δ/160) ‖κ‖ ≤ ‖ξ−κ‖.
```

这提供全空间平移尾的几何输入，没有额外限制在有界频域。实际 Fourier 采用 `exp(-2π i⟪x,ξ⟫)`；已证明真实调制乘法对应 Fourier 平移，角频率的实际平移中心为 `±κ/(2π)`。

对任意固定复 Schwartz 函数 ψ，已证明 `|Fourier ψ|²` 全空间可积，及半径趋于无穷时其平方尾积分趋零；也证明了逐点逃逸可测区域的相应结论。将真实频率分离接入这些尾积分，得到同一 f/w 的各个正负归一化模态在固定 Eδ 上的 Fourier 能量趋零。

## 4. Schwartz Parseval 与 cutoff 乘积桥

对有限维实内积空间上的复 Schwartz 函数，直接从固定库的 L¹ 交换积分定理与 Schwartz Fourier 反演证明

```text
∫ |Fourier ψ|² = ∫ |ψ|².
```

这是实际全空间积分恒等式，不是引用尚未定位的 L² 扩张。调制等式在 Lean 总定义的积分上可以不带可积假设写出；本轮实际 Fourier 能量应用使用 Schwartz 函数，另有可积证明，不依赖不可积时的默认零值。

cutoff 部分对真实 χ∈C∞c、h=f_n 或 w_n 使用乘积法则：

```text
∂ᵢ(χh_n) − χ∂ᵢh_n = (∂ᵢχ)h_n.
```

右端作为实际全空间 L² 元素趋零；任意固定 L² 连续线性映射也保持这项小量。但这里的任意映射参数**没有**被冒充为已经构造的 Fourier 投影，也没有交换 χ 与非局部算子。

实际有限模态已完整拼装：对每个原有实 C∞c 截断 χ、固定 δ>0，分别取 h_n=fSequence n、wSequence n，有

```text
lim_n Σ_{i=0}^3 ∫_{Eδ} |Fourier(χ ∂ᵢh_n)(ξ)|² dξ = 0.
```

每个分量的结论也单独成立，没有固定某个支撑紧集或只证明一个分量。另已将乘积法则接到两个实际 L² 对象 `productGradientLp` 与 `localizedGradientLp`，证明任意固定 L² 连续线性映射 A 下两者之差趋零。

这些结论不自动产生全部 L² 上的 Fourier 等距扩张；固定锐/光滑投影的真实构造、相容性及相应物理 L² 结论仍须实际完成后才能闭合原3193目标。它们仍是完整父目标的已证组成部分。

## 5. 实际登记和证据

登记的每项均是 proved theorem；辅助引理通过其真实证明依赖审计，不把每个计算单独计作论文结果。准确名称、类型、输入版本和独立回读见 [initial-foundations-review.md](initial-foundations-review.md)；scope 中原始17项正式结果与3项必做未编号结果的范围未缩减。

| 支撑ID | 实际声明 | 使用片 |
| --- | --- | --- |
| `f05:countable:exists-subsequence-all-tests` | `Burnett.Analysis.Compactness.exists_subsequence_all_tests` | F05 |
| `f05:countable:exists-subsequence-of-testwise-abs-le` | `Burnett.Analysis.Compactness.exists_subsequence_of_testwise_abs_le` | F05 |
| `f06:geometry:covariant-mul-contravariant` | `Burnett.Geometry.FiberMetric.covariant_mul_contravariant` | F06 |
| `f06:geometry:contravariant-mul-covariant` | `Burnett.Geometry.FiberMetric.contravariant_mul_covariant` | F06 |
| `f06:geometry:raiseCovector-eq-sharp` | `Burnett.Geometry.FiberMetric.raiseCovector_eq_sharp` | F06 |
| `f06:geometry:symbolNorm-eq-eval-sharp` | `Burnett.Geometry.FiberMetric.symbolNorm_eq_eval_sharp` | F06 |
| `f06:geometry:covector-components` | `Burnett.Geometry.BasisFrame.covector_components` | F06 |
| `f06:geometry:tensor-components` | `Burnett.Geometry.BasisFrame.tensor_components` | F06 |
| `f06:geometry:covector-bijective` | `Burnett.Geometry.BasisFrame.covector_bijective` | F06 |
| `f06:geometry:inverseMetric-components` | `Burnett.Geometry.BasisFrame.inverseMetric_components` | F06 |
| `f06:geometry:physicalPairing-self-nonneg` | `Burnett.Geometry.BasisFrame.physicalPairing_self_nonneg` | F06 |
| `f06:geometry:modelMetric-nondegenerate` | `Burnett.Geometry.BasisFrame.modelMetric_nondegenerate` | F06 |
| `x02:offnull:D-fSequence-two-cosines` | `Burnett.CubicOffNull.D_fSequence_two_cosines` | X02 |
| `x02:offnull:D-wSequence-cosine` | `Burnett.CubicOffNull.D_wSequence_cosine` | X02 |
| `x02:offnull:offNull-separation` | `Burnett.CubicOffNull.offNull_separation` | X02 |
| `x02:offnull:fAngularFrequency-eventually-near-null` | `Burnett.CubicOffNull.fAngularFrequency_eventually_near_null` | X02 |
| `x02:offnull:tendsto-norm-fAngularFrequency` | `Burnett.CubicOffNull.tendsto_norm_fAngularFrequency` | X02 |
| `x02:offnull:tendsto-norm-wAngularFrequency` | `Burnett.CubicOffNull.tendsto_norm_wAngularFrequency` | X02 |
| `fourier:fourier-tail-tendsto-zero` | `Burnett.Fourier.fourier_tail_tendsto_zero` | X02 |
| `fourier:schwartz-parseval` | `Burnett.Fourier.schwartz_parseval` | X02 |
| `fourier:fourier-modulate` | `Burnett.Fourier.fourier_modulate` | X02 |
| `x02:offnull:cutoff-gradient-identity` | `Burnett.CubicOffNull.cutoff_gradient_identity` | X02 |
| `x02:offnull:fCutoffErrorLp-tendsto-zero` | `Burnett.CubicOffNull.fCutoffErrorLp_tendsto_zero` | X02 |
| `x02:offnull:wCutoffErrorLp-tendsto-zero` | `Burnett.CubicOffNull.wCutoffErrorLp_tendsto_zero` | X02 |
| `x02:offnull:map-fCutoffErrorLp-tendsto-zero` | `Burnett.CubicOffNull.map_fCutoffErrorLp_tendsto_zero` | X02 |
| `x02:offnull:map-wCutoffErrorLp-tendsto-zero` | `Burnett.CubicOffNull.map_wCutoffErrorLp_tendsto_zero` | X02 |
| `x02:offnull:offNull-translated-fourier-energy-tendsto-zero` | `Burnett.CubicOffNull.offNull_translated_fourier_energy_tendsto_zero` | X02 |
| `x02:offnull:f-normalized-mode-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.f_normalized_mode_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:w-normalized-mode-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.w_normalized_mode_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:compact-fGradient-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.compact_fGradient_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:compact-wGradient-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.compact_wGradient_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:compact-fGradient-total-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.compact_fGradient_total_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:compact-wGradient-total-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.compact_wGradient_total_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:f-productGradient-map-difference-tendsto-zero` | `Burnett.CubicOffNull.f_productGradient_map_difference_tendsto_zero` | X02 |
| `x02:offnull:w-productGradient-map-difference-tendsto-zero` | `Burnett.CubicOffNull.w_productGradient_map_difference_tendsto_zero` | X02 |
