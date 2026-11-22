# Derivative commutator for the fixed matrix projection

[简体中文](projection-hodge-commutator.zh-CN.md)

This delivery covers manuscript lines 1636–1642 and 1674–1684 using the existing fixed projection. At nonzero radian frequency let $P_\xi=I-\xi\xi^{\mathsf T}/|\xi|^2$ and let $J$ denote the original infrared high pass. The matrix $L^2$ multiplier applies the two Hodge factors and $J$. On Schwartz matrix fields it realizes the original Fourier action with symbol $J P_\xi(\,\cdot\,)P_\xi$.

For a single slot $P$, set $A=Pw$ and $S_{jk}=\delta_{jb}A_k-\delta_{kb}A_j$. Transversality gives $\sum_j\partial_j S_{jk}=\partial_b A_k$. The product rule and cancellation of the contraction of a symmetric Hessian with an antisymmetric tensor give

$$
  [P,f]\partial_b w
   =-P\bigl((\nabla f)(w-A)_b\bigr)
     +(I-P)\Bigl(\bigl(\textstyle\sum_j(\partial_j f)S_{jk}\bigr)_k\Bigr).
$$

A common compact radian Fourier support avoiding zero supplies a Schwartz witness $A$. The single-slot $L^2$ constant can be chosen before the direction, coefficient, input, and compact frequency set. Composing the left and right slots with the same $J$ gives the actual matrix commutator. Annular approximation removes the spectral restriction by converging in $L^2$ both for the input and for its first derivative.

For every globally $L$-Lipschitz complex scalar coefficient $f$, the result gives a bounded complex-linear operator $T_{b,f}$ on the entire matrix $L^2$ space with

$$
  \|T_{b,f}w\|_2\le C L\,\|w\|_2 .
$$

On Schwartz matrices, $T_{b,f}w=\Pi(f\partial_b w)-f\Pi(\partial_b w)$, with both coefficient products realized in $L^2$. The matrix norm is the maximum of the fixed finite set of component $L^2$ norms. Subtracting $f(0)$ before spatial cutoff handles linearly growing smooth coefficients. Normalized smooth convolution preserves the Lipschitz bound and uniformly approximates an arbitrary Lipschitz coefficient. Density of Schwartz matrices gives the extension. The constant is uniform in all four directions, coefficients, and inputs.

The coordinate vacuum remainder, the whole-space divergence source, and preservation of the full angular measure remain to be connected to the same projected field. Author confirmation is pending.

- `Burnett.P01.skew_symmetric_contraction_zero`
- `Burnett.P01.hodgeCommutator_spectrum`
- `Burnett.P01.hodgeCommutator_action`
- `Burnett.P01.exists_hodgeCommutator_action_l2_bound`
- `Burnett.P01.exists_hodgeTransverseSchwartz_of_compactSpectrum`
- `Burnett.P01.projectionFullL2_eq_schwartz`
- `Burnett.P01.projectionFullCommutatorL2_eq_actual`
- `Burnett.P01.exists_projectionFullCommutatorL2_bound_on_annularCore`
- `Burnett.P01.projectionMatrixAnnularApproximation_tendsto`
- `Burnett.P01.projectionMatrixAnnularApproximation_derivative_tendsto`
- `Burnett.P01.exists_projectionFullCommutatorL2_bound`
- `Burnett.P01.projectionCoefficientCutoff_lipschitz`
- `Burnett.P01.projectionLipschitzCoefficientProductL2_ae`
- `Burnett.P01.projectionCoefficientCutoff_product_tendsto`
- `Burnett.P01.exists_projectionLipschitzCommutatorL2_bound`
- `Burnett.P01.exists_smooth_lipschitz_approximation`
- `Burnett.P01.exists_projectionGeneralLipschitzCommutatorL2_bound`
- `Burnett.P01.exists_projectionLipschitzCommutatorL2_extension`

[Shared source bindings](projection-hodge-commutator-source-bindings.json)
