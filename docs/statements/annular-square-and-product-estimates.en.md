# Four-dimensional annular square and product estimates

[简体中文](annular-square-and-product-estimates.zh-CN.md)

These statements supply the finite-exponent estimates for the Fourier multiplier argument at lines 660–671. All spatial arguments lie in $\mathbb R^4$.

- The finite signed annular convolution satisfies an $L^p$ bound for each $1<p<\infty$. The frequency window is a compactly supported Schwartz function vanishing outside $1/2<|\xi|<2$. The bound applies to all complex $L^p$ inputs and is uniform for initial scale $t>0$, finite index set and complex coefficients of modulus at most one, with shift dependence $1+|q|$.
- For the same annular kernels, the square function over a finite list of distinct dyadic scales $2^k t$, with $k\in\mathbb N$ and common initial scale $t>0$, has the corresponding $L^p$ bound and shift dependence. For Schwartz inputs, Lean identifies it pointwise with the square function of the original shifted Fourier-window operators.
- The integral of the finite sum of absolute three-factor products is bounded by the product of the input $L^p,L^s,L^z$ norms whenever the exponents lie in $(1,\infty)$ and are Hölder-compatible with target exponent one. The annular factors use distinct dyadic scales within each family, with common initial scales $t$ and $u$ respectively. The third is a shifted Schwartz-window action on a Schwartz input at arbitrary positive scales, used for the low-frequency factor. The shift dependence is $(1+|q|)(1+|v|)(1+|l|)^5$.

The full-scale joint multiplier and the paper's cubic-energy proof are subsequent integrations. Author confirmation of these supporting correspondences is pending. [Source bindings](annular-square-and-product-estimates-source-bindings.json)
