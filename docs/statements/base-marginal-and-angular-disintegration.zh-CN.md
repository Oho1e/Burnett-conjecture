# 基底边际与角向解体

`Burnett.F08.IntrinsicBaseMarginal.baseMarginal_and_angularDisintegration` 证明锁定论文第 487–506 行的 `cor:base-marginal`。设 $B$ 为原光滑 Lorentz 背景，$r$ 为辅助黎曼度量，$(g_n)$ 为满足原容许条件的光滑真空序列。输入固定的二次测度 $\mu$，其在紧底集上方有限，集中于零锥，满足原 Einstein 二阶矩。背景标量曲率逐点为零。

记 $e_r=\operatorname{tr}_r G(B)$。它光滑且处处非负，并满足

$$
\pi_*\mu=e_r\,\mathrm dV_B.
$$

`UnitNullFiber` 取同一辅助单位余球面的依赖纤维，纤维元素是底点等于 $x$ 且 Hamiltonian 为零的单位余向量。`UnitNullFiberMeasures` 给出非负且几乎处处有限的逐纤维测度 $\mu_x$，沿实际纤维包含映射推前的测度族可测。`reconstructs_apply` 对每个 Borel 集 $S$ 给出

$$
\mu(S)=\int_M \mu_x(\iota_x^{-1}(S))\,\mathrm dV_B(x).
$$

在同一个体积满测集上，$\mu_x$ 的质量为 $e_r(x)$，且任意切向量对 $u,v\in T_xM$ 都满足可积的矩恒等式

$$
G(B)_x(u,v)=\int \xi(u)\xi(v)\,\mathrm d\mu_x(\xi).
$$

$e_r=0$ 时纤维测度几乎处处为零。固定 $\mu$ 后，任何两个按该背景体积重构它的可测纤维族几乎处处相等。基底边际对背景体积绝对连续，且 $\mu$ 在每个背景真空开区上方消失。

## 数学与核验接口

正式入口由原真空序列取得 Einstein 张量对称性，并应用已有的总空间角核和共同满测集上的矩。闭图可测性使总空间核的逐纤维限制可测。沿纤维嵌入拉回再推前，与原核在体积几乎处处相同。唯一性沿同一个联合图测度回到实际依赖纤维。

本地原生重放通过新 `Burnett` 库入口核验正式声明。单独的探针对照冻结的独立题面，并展示原二次构造的同一细化、振幅与 $\mu$ 如何传入。作者确认待登记，论文状态为 `development`。
