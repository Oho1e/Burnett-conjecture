# Full real quadratic expansion and null-cone gauge elimination

This batch continues `paper/burnett.tex` lines432–463, SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`. See [ricci-symbol.md](ricci-symbol.en.md) for the earlier real noncharacteristic fragment. This page records additions from the parallel pilot; F06 remains partial and scope governs current progress.

## Actual objects and shared definitions

Indices remain `Fin 4` and all components are real. G parameterizes inverse-metric components; k/l are covariant two-tensors. `IsSymmetricTensor` explicitly states component symmetry. Raising, the Ricci symbol, gauge tensors, c, and B reuse `RicciSymbol.lean`, without Euclidean contractions.

Shared module `QuadraticDefs.lean` defines the real bilinear contraction over all ordered indices

$$
\langle k,l\rangle_G=\sum_{a,b,c,d}G^{ac}G^{bd}k_{ab}l_{cd},
\qquad (k^2)_{bc}=\sum_a k_b{}^a k_{ac},
$$

$$F_G(k,l)=\langle k,l\rangle_G-\tfrac12\operatorname{tr}_Gk\operatorname{tr}_Gl.$$

This is not yet a complex Hermitian definition. The full expansion applies to arbitrary real symmetric G/k; cross-term elimination uses the additional null-kernel assumptions below. Neither requires nondegeneracy or signature, so actual inverse Lorentz-metric components instantiate them pointwise. Geometric inversion/coordinate naturality and null-frame quotient positivity are not thereby completed.

## Four additions

| Inventory ID | Actual declaration | Source lines |
| --- | --- | --- |
| `quadratic:full-real-expansion` | `Burnett.RicciSymbol.four_quadraticSymbol_expansion` | 447–448 |
| `quadratic:null-kernel-constraint` | `Burnett.RicciSymbol.null_kernel_iff_contracted` | 454 |
| `quadratic:null-real-formula` | `Burnett.RicciSymbol.quadraticSymbol_eq_physicalPairing_of_null_kernel` | 454–457 |
| `quadratic:null-real-gauge-cross` | `Burnett.RicciSymbol.physicalPairing_pureGauge_eq_zero_of_null_kernel` | 459–463 |

For symmetric G/k, the first result assumes neither the Ricci kernel nor the null cone and proves the complete identity

$$
4B_{bc}(k,k)=\xi_b\xi_c\langle k,k\rangle_G+2q_bq_c
-2s(k^2)_{bc}-t(\xi_bq_c+\xi_cq_b-sk_{bc}).
$$

The second requires only $\xi\ne0$ and $s=0$; even without symmetric G/k,

$$\mathcal R_\xi(k)=0\quad\Longleftrightarrow\quad q=t\xi/2.$$

It selects an existing nonzero covector component, not a fixed coordinate assumed nonzero. The original unit cosphere ensures nonzero ξ. The equivalence generally fails without s=0.

The third is actually assembled by root from the two branches: for symmetric G/k, $\xi\ne0$, $s=0$, and $\mathcal R_\xi(k)=0$,

$$B_{bc}(k,k)=\tfrac14\xi_b\xi_cF_G(k,k).$$

Under the same null-kernel conditions, the fourth proves for every real v and $\ell=\xi\otimes v+v\otimes\xi$

$$F_G(k,\ell)=0.$$

The proof separately establishes outer-product contractions, the gauge contraction for symmetric k, and the gauge trace for symmetric G, then applies the kernel constraint. Cross-term elimination is not an input, and the result is not restricted to gauge self-pairing.

## Implementation, evidence, and remaining obligations

Two implementation agents exclusively owned `QuadraticExpansion.lean` and `NullKernel.lean`; root built and froze shared definitions first. The first frozen null result entered independent readback while its branch continued cross-term elimination and the other completed the B expansion. root actually assembled them in `NullQuadratic.lean`; the full combined library build passed.

Source locations:

- [Shared definitions](../../Burnett/Algebra/QuadraticDefs.lean)
- [Full real expansion](../../Burnett/Algebra/QuadraticExpansion.lean)
- [Null kernel and real gauge cross terms](../../Burnett/Algebra/NullKernel.lean)
- [Combined null-cone formula](../../Burnett/Algebra/NullQuadratic.lean)

Actual compilation, types, axioms, and independent readback are retained in `.project-verification/parallel-pilot/`. Implementer compilation is not presented as independent review. See the [engineering review](../formalization/review.en.md) and scope for final checks and confirmation status.

See [real mixed results](real-polarization.en.md) for the added mixed polarization and kernel formulas; this file retains the original real-diagonal delivery record. Complex Hermitian extension, physical-quotient nonnegativity and a general Lorentz null-frame bridge, positive Hermitian measure-density applications, and F04/F05/F07 analytic/measure closure remain unfinished. The17 numbered results and two other approved unnumbered targets remain incomplete; author mathematical confirmation is pending.
