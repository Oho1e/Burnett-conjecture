# Ricci 符号的首个实代数片段

原文：`paper/burnett.tex`，SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`。本片段对应415–418、432–436和452行，是二次测度构造所需的局部代数依赖。

## 数学含义

固定一点的四维实坐标，令指标取 `Fin 4`。原文逆度量的分量记为 `gInv`，余向量为 `ξ`，二阶协变张量分量为 `k`。所有重复指标均对全部有序指标求和。

$$
s=\sum_{a,b}g^{ab}\xi_a\xi_b,\qquad
t=\sum_{a,b}g^{ab}k_{ab},\qquad
q_b=\sum_a\xi^a k_{ab}.
$$

代码逐一定义升指标、上述三个收缩以及

$$
\mathcal R_\xi(k)_{ab}
=\tfrac12(sk_{ab}+\xi_a\xi_b t-\xi_aq_b-\xi_bq_a).
$$

若 `s ≠ 0` 且每个分量的 `𝓡ξ(k)` 为零，则取

$$v_b=\frac{q_b-t\xi_b/2}{s}$$

便有 `k_ab = ξ_a v_b + v_a ξ_b`。继续按原文定义

$$
c(k)^a{}_{bc}=\tfrac12(\xi_b k_c{}^a+\xi_c k_b{}^a-\xi^a k_{bc}),
$$

$$
B_{bc}(k,k)=\sum_{a,e}
\left(c(k)^a{}_{ce}c(k)^e{}_{ba}-c(k)^a{}_{ae}c(k)^e{}_{bc}\right).
$$

对纯规范张量有 `c(k)^a_bc = ξ_b ξ_c v^a`，两项在每个 `(a,e)` 上抵消，故 `B_bc(k,k)=0`。于是非特征 Ricci 符号核上的实对角二次项为零。

实现事实上允许任意实系数 `gInv` 和 `k`，不预设对称性或 Lorentz 签名；证明的这个单向结论在较大域中仍成立。将 `gInv` 取真实逆 Lorentz 度量分量、将 `k` 取原文对称张量即可应用。这里没有用欧氏单位矩阵替代逆度量，也没有实现整个流形度量求逆接口。

## 实际声明与来源

模块：[RicciSymbol.lean](../../Burnett/Algebra/RicciSymbol.lean)，命名空间 `Burnett.RicciSymbol`。

| 清单子项 | 实际定理 | 数学作用 | 原文定位 |
| --- | --- | --- | --- |
| `ricci:kernel-pure-gauge` | `kernel_eq_pureGauge` | 非特征核中构造显式规范向量 | 415–418、452 |
| `ricci:raise-pure-gauge` | `raiseSecond_pureGauge` | 纯规范张量升指标的线性展开 | 434、452的证明步骤 |
| `ricci:connection-pure-gauge` | `connectionSymbol_pureGauge` | 连接主符号等于 `ξ_b ξ_c v^a` | 434、452 |
| `ricci:quadratic-pure-gauge` | `quadraticSymbol_pureGauge` | 纯规范张量的完整有序二次收缩为零 | 435、452 |
| `ricci:quadratic-kernel` | `quadraticSymbol_eq_zero_of_noncharacteristic_kernel` | 合成核表示与二次消去 | 452 |

这些子项从属于现有 `unnum:quadratic-symbol-algebra`，没有将原文整段432–465标成完成。精确类型在本文件后半部分逐字摘自当前实现，完整定义在模块中；机器实际类型、公理与来源核对由目标审计保存。

## 当前证据与边界

固定 Lean4.24.0，Mathlib提交 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。实现者和独立复核者均已在核实版本的只读库探针下实际编译、查询类型和公理；五个定理仅依赖 `propext`、`Classical.choice`、`Quot.sound`。本项目独立依赖的构建和目标审计亦已实际通过；CI按实际固定提交另记于复核记录，不从本地探针直接推定。

[独立数学回读及比较](ricci-symbol-review.md)先读实际代码和类型，再对照原文；作者确认按实际答复记录，未发生的确认不补写。

未覆盖：原文447–448的完整二次展开、混合/Hermitian极化、零锥 `s=0` 分支、规范商的非负性、缺陷测度、输运和主定理。也没有声称任意非对称 `gInv` 下纯规范张量反向属于 Ricci 核。

## 当前 Lean 类型原文

```lean
theorem kernel_eq_pureGauge (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hs : symbolNorm gInv ξ ≠ 0) (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0) :
    k = pureGauge ξ (kernelGaugeVector gInv ξ k)
```

```lean
theorem raiseSecond_pureGauge (gInv : Tensor2) (ξ v : Covector) (c a : Index) :
    raiseSecond gInv (pureGauge ξ v) c a =
      ξ c * raiseCovector gInv v a + v c * raiseCovector gInv ξ a
```

```lean
theorem connectionSymbol_pureGauge (gInv : Tensor2) (ξ v : Covector) (a b c : Index) :
    connectionSymbol gInv ξ (pureGauge ξ v) a b c =
      ξ b * ξ c * raiseCovector gInv v a
```

```lean
theorem quadraticSymbol_pureGauge (gInv : Tensor2) (ξ v : Covector) (b c : Index) :
    quadraticSymbol gInv ξ (pureGauge ξ v) b c = 0
```

```lean
theorem quadraticSymbol_eq_zero_of_noncharacteristic_kernel
    (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hs : symbolNorm gInv ξ ≠ 0) (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0)
    (b c : Index) : quadraticSymbol gInv ξ k b c = 0
```
