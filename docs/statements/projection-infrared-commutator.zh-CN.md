# 固定红外因子的梯度交换子

[English](projection-infrared-commutator.en.md)

这批登记锁定稿第 1636–1638 行固定红外截断的卷积实现，以及第 1674–1683 行梯度型交换子估计的红外部分。

- 设 $J$ 是原固定高通乘子，弧度频率下的径向截断为 $\eta(r)=\operatorname{smoothTransition}(r-1)$。普通 Fourier 变量中的低频补符号为 $1-\eta(2\pi|\nu|)\,$。其 Schwartz 逆变换为 $K$，且 $Jw=w-K*w$ 在 Schwartz 输入上逐点成立。
- 对全局 Lipschitz 的 $C^1$ 复值标量系数 $f$ 和 Schwartz 场 $w$，用 $I-K*$ 作用于交换子中的实际乘积。一次分部积分将 $[J,f]\partial_b w$ 化为作用在 $w$ 上的积分核。该核为 $(\partial_b K)(x-y)(f(x)-f(y))+K(x-y)\partial_b f(y)$，由 $\operatorname{Lip}(f)(|x-y|\,|\partial_b K(x-y)|+|K(x-y)|)$ 控制。
- 核的 $L^1$ 质量和其各方向导数的一阶矩给出固定有限常数 $C_{\mathrm{IR}}$，对所有偏导方向、系数和 Schwartz 输入统一，满足 $\|[J,f]\partial_b w\|_2\le C_{\mathrm{IR}}\operatorname{Lip}(f)\|w\|_2$。约化后的积分核估计也适用于可测 $L^1\cap L^2$ 输入。

完整矩阵投影还需接入齐次 Hodge 槽的交换子。完整 P01 命题还需真空余项、全空间散度源和角向测度保持。作者确认待记录。

- `Burnett.P01.projectionInfraredAction_eq_kernel`
- `Burnett.P01.projectionLowMoment_integrable`
- `Burnett.P01.norm_projectionInfraredCommutatorKernel_le`
- `Burnett.P01.projectionInfraredKernelAction_commutator_derivative`
- `Burnett.P01.projectionInfraredCommutatorConstant_nonneg`
- `Burnett.P01.projectionInfraredCommutatorKernel_l2`
- `Burnett.P01.projectionInfraredKernelAction_commutator_l2`

[共同源码对应](projection-infrared-commutator-source-bindings.json)
