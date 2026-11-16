# 第一轮按消费者核查的依赖与下一缺口

2026-11-16；Lean 4.24.0，mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。本记录沿用[原调查](library-audit.md)的证据分级；有限检索未定位不等于库内不存在。它不批准新数学假设或信任扩展。

## 已有可消费结果

- 项目新增的 CountableTests 实际证明：可数有界实测试沿同一严格递增子列同时收敛。只闭合F05的可数抽取步骤，不构造正缺陷测度。
- 固定库的真实 L¹/Schwartz Fourier、调制与反演接口经过实际探针和新证明调用；项目另从L¹交换积分与Schwartz反演证明Schwartz Parseval。实际四分量离锥能量及cutoff桥见[声明](../statements/initial-foundations.md)。
- SchwartzMap.toLpCLM 与连续紧支撑函数的 L² 逼近接口已实际核签，并在任意有限维实内积空间的复值 `Lp 2 volume` 上实例化；未添加稠密性公理。

## 最邻近的剩余任务：实际 L² Fourier 扩张

需要实际证明

```lean
DenseRange (fun f : SchwartzMap V ℂ => f.toLp 2 (volume : Measure V))
```

再利用已证Schwartz Parseval及反演，把Fourier等距延拓到真实L²并证明与原Schwartz/L¹ Fourier一致。这里不能把DenseRange当作未经证明的参数后宣称该任务已完成。

已核实的候选链是：

1. `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`：真实L²函数可由连续紧支撑函数逼近，保留其准确测度/拓扑假设。
2. `UniformContinuous.exists_contDiff_dist_le`：全空间一致的光滑逼近。该模块本轮只源码核签，未因缺少缓存断言缺少定理。
3. 为一个固定连续紧支撑函数选在其支撑上等于1的固定光滑紧截断；将第2步近似乘以此截断，既保留紧支撑，又由固定支撑体积与一致误差控制L²误差。
4. 用 `HasCompactSupport.toSchwartzMap` 接到实际Schwartz→L²映射，组合两层逼近取得稠密性，再做等距延拓。

第3步的紧支撑光滑L²误差桥仍待实际实现；准确库匹配继续核查。普通一致光滑逼近本身不保证紧支撑，不能直接跳过这一层。随后还需构造真实频率符号乘法、逆变换及锐/光滑算子，处理可测性、零频a.e.和全空间尾，才能闭合原3193父目标。

## F05 现有组件与具体缺桥

| 组件及证据 | 能提供什么 | 仍需补什么 |
| --- | --- | --- |
| RealRMK.rieszMeasure / integral_rieszMeasure；源码核签 | 已构造的正实 C_c 泛函的测度表示 | 真实PDO测试极限、正性、向C_c的延拓、局部有限Hermitian丛值密度及变换 |
| VectorMeasure.withDensityᵥ；源码核签 | 全局可积密度的向量测度 | **非全局Integrable时该定义返回零**；局部有限全丛情形须另处理紧穷竭与兼容性，不能直接套用 |
| Matrix.PosSemidef及合同变换；源码核签 | 有限维密度正性、合同变换保持正 | 由系统积分约束到a.e. `A M Aᴴ=0`，再到 `range M⊆ker A`，尚需实际桥接 |
| WeakDual.isCompact_closedBall；源码核签 | 对偶闭球的弱星紧性 | 不是序列紧性接口；本轮可数抽取绕开这一跳跃，全部符号的密度/一致连续性仍要证明 |
| IsCompactOperator；源码核签 | 已证紧算子的紧性后果 | 不自动把局部负一阶符号识别成紧算子，也不自动给出其弱零到强零 |

F05的正丛值微局部提取/定位接口，在限定Fourier、Distribution、Operator、InnerProductSpace及相关几何/向量测度路径的术语检索中未定位直接匹配；准确库匹配仍待核。精确文献版本的适用签名也未在本轮核实。

## A01 与 P01 继续分别处理

A01需要真实一阶PDO与Lipschitz标量的交换子控制及能量应用；P01需要固定全空间IR正则 `Π∂b` 的梯度型Calderón范数界，只依赖 `‖∂f‖∞`，不能额外要求完整f全局有界。二者不能以一般CLM的opNorm定义互相替代。

P01后续使用的精确恒等式为

```text
[Π,f]∂b w = [Π∂b,f]w − Π((∂b f)w).
```

当前Lp支配估计和CLM算子范数接口只作用于已构造的实际元素/映射，不提供这条Calderón估计。限定范围未定位直接匹配的PDO/交换子声明，仍保留待核，不因此启动无边界的“重写全部理论”。

本轮源码身份、限定检索参数、实际类型探针和各自退出码保存在工作区的N1/N3证据中；候选的新源码另有固定绑定及实际机器检查。新增范围清单只把EXT-HARMONIC消费者X02补入，未新增重复父目标或片间边。
