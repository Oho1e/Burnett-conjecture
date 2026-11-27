# 有界 Lipschitz 系数的四次弱交换子

[English](original-lipschitz-quartic-commutator.en.md)

`Burnett.A08.exists_paperAnalyticLipschitzQuarticBound` 对应论文第 1476–1504 行
`eq:analytic-quartic-bound`。修正算子沿用 A07 的实际 $T_H$ 及其高频伴随，
系数 $d^{ab}=d^{ba}$ 为实值、有界、全局 Lipschitz。散度算子
$L_d=-\partial_a(d^{ab}\partial_b)$ 的弱型使用正向及伴随输出的实际 $L^2$ 坐标弱导数。
在 Schwartz 系数下，该弱型等于同一个修正算子及同一批场的原散度交换子。

三项分别保留低场导数、实际交换子 $[d^{ab},T_H]\partial_bu$ 和伴随槽中的低场导数。
证明通过两个物理乘积配对和相应傅里叶配对的极限，将中间项识别为原弧度频率的交换子分布。
其界使用每个系数梯度范数的本质上界。汇总得到

$$
\bigl|\langle i[L_d,T_H]u,u\rangle\bigr|
\le C_\delta\left(
D\|\partial u\|_2\|\partial H\|_4\|\partial u\|_4+
G\|\partial u\|_2\|H\|_4\|\partial u\|_4\right),
$$

其中 $D$ 控制系数的绝对值，$G$ 控制各系数梯度范数的本质上界。有限符号导数阶数和
常数先于独立变量延拓及输入场选定。投影源用于第 1516 行起的后续能量恒等式。

第 1541–1552 行和第 1558 行的三项弱角尾沿用同一球谐和 $A_L$、真实高频伴随及
Hermitian 部分 $T_L=(A_L+A_L^*)/2$。
`Burnett.A08.OriginalAngularCutoff.originalWeakDivergenceCommutatorPair_angularTail`
把有限角弱配对与原 Hermitian 修正弱配对之差识别为对应的三项角尾。
`Burnett.A08.OriginalAngularCutoff.exists_boundedLipschitzWeakDivergenceAngularTails`
为三项分别给出其原范数乘积与 $(1+L)^{-2}$ 的上界。中间项经两种高槽指数界求和，
并保留有界实 Lipschitz 系数梯度范数的本质上界。

四次界和角尾的六个普通模块已通过各自的隔离原生回放。角尾回放同时导入原四次界。
普通工程构建、独立候选复核及作者确认待完成。
[角尾源码与验证记录](original-lipschitz-quartic-angular-tail-source-bindings.json)
[源码与验证记录](original-lipschitz-quartic-commutator-source-bindings.json)
