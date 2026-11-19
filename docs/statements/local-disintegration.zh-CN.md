# 局部加权测度分解

[English](local-disintegration.en.md)

本包支持原文第 487–518 行的基底边缘与角向分解推论。两个生产源码模块以提交 `be653f49507fbd73a2f466cb308b3f65dd30de0e` 为基准完成独立目录的构建检查。

`Burnett.Analysis.BaseMarginal.SmoothTests` 证明两条局部事实。设实值函数在一个开坐标域上连续，且测度在该域的每个非空开子集上为正。假设对每个紧支撑于该域的光滑实值测试函数，它与原函数的乘积均可积。若对其中每个非负测试函数，该乘积的积分均非负，则原函数在域上逐点非负。若两个有限测度集中在同一个开坐标域上，且对域内所有光滑紧支撑试验的积分相等，则两个测度相等。

`Burnett.Analysis.BaseMarginal.FiberKernel` 假设有限正联合测度 ρ 和有限基底测度 dV，已知边缘恒等式 `ρ.fst = dV.withDensity w`。这里 w 是可测的广义非负实值密度，满足 `w(y) ≤ C < ∞`。另假设 ρ 集中在可测关系 Z 上。组合定理为下列各项构造同一个加权条件核 κ。

- `dV ⊗ₘ κ = ρ`。
- 每个坐标底点的纤维测度 `κ y` 有限，且 `κ y univ = w y`。
- 实值纤维质量对 dV 可积。广义非负实值纤维质量的积分等于 `ρ univ`。
- 对 dV 几乎处处的 y，纤维测度集中于 `{η | (y, η) ∈ Z}`。
- 任何对于 dV 给出同一联合测度的其他有限核，都和 κ 在 dV 下几乎处处相等。这里 Lean 的 `IsFiniteKernel` 表示纤维质量有统一有限界。

继承的证明来自已独立复核的局部证明包。唯一性定理的欧氏坐标空间改用定义等价的 `CoordinateSpace`，与同模块其余定理一致。新组合定理把已知边缘恒等式作为假设。由原度量推出实际边缘、几乎处处 Einstein 二阶矩及全局装配仍为 F08 的待证义务。

## 已登记的支持目标

| 目标标识 | 模块后缀 | 声明后缀 |
| --- | --- | --- |
| `base-marginal:smooth-test-positivity` | `SmoothTests` | `nonnegOn_of_smooth_test_integrals` |
| `base-marginal:smooth-test-measure-ext` | `SmoothTests` | `finiteMeasures_eq_of_local_smooth_tests` |
| `base-marginal:finite-kernel-unique` | `FiberKernel` | `localFiberKernel_unique` |
| `base-marginal:local-weighted-disintegration` | `FiberKernel` | `exists_localFiberDisintegration` |

模块共同前缀为 `Burnett.Analysis.BaseMarginal`，声明共同前缀为 `Burnett.F08.ActualBaseMarginal`。以上均为 `cor:base-marginal` 的支持目标。


独立目录的 Lean 原生重放检查了 14 个声明，全部只使用政策 A 的三项基础公理。[源码绑定](local-disintegration-source-bindings.json)记录核对的输入。
