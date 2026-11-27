# 对称能量配对的 Lipschitz 交换子估计

[English](lipschitz-commutator-energy.en.md)

锁定论文的 `lem:commutator` 位于第 566–575 行。`Burnett.Analysis.CarlesonEmbedding.originalRadianScalarLipschitzEnergy` 给出实对称光滑标量系数 $r^{ab}=r^{ba}$ 的估计。$B$ 是固定、适当支撑且形式自伴的一阶矩阵伪微分算子，具有全局光滑的完整 $S^1_{1,0}$ 左符号。对紧支撑光滑向量场 $u$ 和有限 $W^{1,\infty}$ 范数的系数，结论为

$$
\bigl|2\operatorname{Im}\langle r^{ab}\partial_a\partial_b u, Bu\rangle\bigr|
\leq C_B\|r\|_{W^{1,\infty}}\|u\|_{H^1}^2.
$$

常数在系数和测试场之前选定。右端只使用系数的值和一阶导数的分量本质上界，以及测试场的非齐次坐标 $H^1$ 范数。`Burnett.Analysis.CarlesonEmbedding.originalRadianHermitianLipschitzEnergy` 实现第 573–574 行的厄米矩阵系数版本。该版本使用 $(R^{ab})^*=R^{ba}$，且 $B$ 的完整符号在所有场分量上是同一个标量符号。

`HormanderOrderOne` 用混合 Fréchet 导数表示一般 $S^1_{1,0}$ 符号类。全左量子化的作用与按原文第 539–544 行 Fourier 约定写出的左符号积分逐点相等，正变换用 $e^{-ix\cdot\xi}$，逆变换用 $e^{ix\cdot\xi}$ 和因子 $(2\pi)^{-4}$。两条结果采用 Lebesgue 配对。第 591 行的固定图密度步骤有各自的截断与对称性接口。

原生回放编译了两个精确源码模块并检查 11 条声明。两条登记目标的传递公理为 `propext`、`Classical.choice` 和 `Quot.sound`。独立复核已从实际类型与定义核对原命题的量词、符号类、配对、归一化和厄米条件。作者确认待完成。[锁定输入与验证记录](lipschitz-commutator-energy-source-bindings.json)
