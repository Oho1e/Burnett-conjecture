# Derivative commutator for the fixed infrared factor

[简体中文](projection-infrared-commutator.zh-CN.md)

This delivery registers the convolution realization of the fixed infrared cutoff at manuscript lines 1636–1638 and the infrared part of the derivative commutator estimate at lines 1674–1683.

- Let $J$ be the original fixed high-pass multiplier with radial cutoff $\eta(r)=\operatorname{smoothTransition}(r-1)$ in radian frequency. The complementary low-frequency symbol in ordinary Fourier variables is $1-\eta(2\pi|\nu|)\,$. Its Schwartz inverse transform $K$ gives the pointwise identity $Jw=w-K*w$ on Schwartz inputs.
- For a globally Lipschitz $C^1$ complex scalar coefficient $f$ and a Schwartz field $w$, $I-K*$ acts on the products in the commutator. Integration by parts gives the kernel of $[J,f]\partial_b w$ acting on $w$. It is $(\partial_b K)(x-y)(f(x)-f(y))+K(x-y)\partial_b f(y)$, bounded by $\operatorname{Lip}(f)(|x-y|\,|\partial_b K(x-y)|+|K(x-y)|)$.
- The mass of the kernel and the first moments of its derivatives give a finite constant $C_{\mathrm{IR}}$ shared by every derivative direction, coefficient, and Schwartz input. It gives $\|[J,f]\partial_b w\|_2\le C_{\mathrm{IR}}\operatorname{Lip}(f)\|w\|_2$. The reduced kernel bound also applies to measurable $L^1\cap L^2$ inputs.

The full matrix projection still requires the commutator estimates for its homogeneous Hodge slots. The complete P01 proposition still requires the vacuum remainder, the whole-space divergence source, and preservation of the angular measure. Author confirmation is pending.

- `Burnett.P01.projectionInfraredAction_eq_kernel`
- `Burnett.P01.projectionLowMoment_integrable`
- `Burnett.P01.norm_projectionInfraredCommutatorKernel_le`
- `Burnett.P01.projectionInfraredKernelAction_commutator_derivative`
- `Burnett.P01.projectionInfraredCommutatorConstant_nonneg`
- `Burnett.P01.projectionInfraredCommutatorKernel_l2`
- `Burnett.P01.projectionInfraredKernelAction_commutator_l2`

[Shared source bindings](projection-infrared-commutator-source-bindings.json)
