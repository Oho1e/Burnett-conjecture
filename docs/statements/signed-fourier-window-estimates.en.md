# Signed Fourier windows in four dimensions

[简体中文](signed-fourier-window-estimates.zh-CN.md)

Let $s_k=2^kt$ with $t>0$, let $q\in\mathbb R^4$, and take a finite set of indices with complex coefficients $|c_k|\leq1$. These estimates supply the annular operators for the bilinear multiplier argument at lines 660–671.

- `signed_annular_sum_L2` gives the bound $2\,\mathrm{bound}(m)\|u\|_2$ on the finite sum of Fourier multipliers with symbols $c_km(s_k\xi)$ for every complex $L^2$ input. The bounded symbol $m$ is supported in $1/2<|\xi|<2$ in the sense that it vanishes outside that open annulus.
- `dyadic_kernel_hormander` gives the integral difference bound $C_\phi(1+|q|)$ over $2|h|\leq |z|$ for the kernel $K(z)=\sum_k c_k s_k^{-4}\phi(z/s_k+q)$ from any Schwartz $\phi$. The bound is uniform in the initial scale, finite index set, coefficients and displacement $h$.
- `signed_window_operator_estimates` takes $\phi=\mathcal F^{-1}a$ for a compactly supported Schwartz frequency window $a$ in the open annulus. On each Schwartz input the same $K$ defines the convolution and the almost-everywhere $L^2$ representative. Its $L^2$ norm is bounded by $2\,\mathrm{seminorm}_{0,0}(a)$ times the input norm.

The finite-exponent annular square estimate and joint multiplier bound are later integration steps. Author confirmation of this supporting correspondence remains pending. [Source bindings](signed-fourier-window-estimates-source-bindings.json)
