# F06: real mixed polarization of the original Ricci quadratic form

Source: `paper/burnett.tex` lines432–463, especially450,452,454–457. Use fixed four-dimensional real coordinate indices, summing contractions over ordered indices. Reuse the [real definitions/diagonal results](quadratic-real-algebra.en.md), adding the real mixed form in `Burnett/Algebra/RealPolarization.lean`. Real results are not called complex Hermitian extension.

## Definition and normalization

Fix real inverse-metric components G and covector ξ. Write c(k) for the original connection symbol and Q_bc(k)=B_bc(k,k) for the original quadratic form. Define

\[
C_{bc}(k,l)=\sum_{a,e}\big(c(k)^a{}_{ce}c(l)^e{}_{ba}
-c(k)^a{}_{ae}c(l)^e{}_{bc}\big),\qquad
M_{bc}(k,l)=\frac{C_{bc}(k,l)+C_{bc}(l,k)}2.
\]

M is the real symmetric mixed form of original B. The code first defines it through the original connection cross product and then proves polarization, rather than defining it by the desired right-hand side. For any real G/ξ and real two-tensors k/l, with b/c fixed,

\[
M(k,l)=M(l,k),\qquad M(k,k)=Q(k),\qquad
M(k,l)=\frac{Q(k+l)-Q(k)-Q(l)}2.
\]

M is additive and linear for all real scalars in each amplitude slot. These algebraic laws require neither nonzero ξ, nondegenerate G, Lorentz signature, nor symmetric amplitudes. Symmetry here exchanges k/l, not b/c. The undivided cross sum is2M.

## Conclusions on two kernel classes

Retain s=G^{ab}ξ_aξ_b and the original Ricci symbol R_ξ.

1. **Noncharacteristic kernel.** If s≠0 and R_ξ(k)=R_ξ(l)=0, then M_bc(k,l)=0 for all b/c. k/l are independently quantified, not just l=k; neither G nor amplitudes need symmetry.
2. **Null-cone kernel.** If G/k/l are real symmetric components, ξ≠0, s=0, and R_ξ(k)=R_ξ(l)=0, then

\[
M_{bc}(k,l)=\frac14\xi_b\xi_c F(k,l),\qquad
F(k,l)=\sum_{a,b,c,d}G^{ac}G^{bd}k_{ab}l_{cd}
-\frac12\operatorname{tr}_G(k)\operatorname{tr}_G(l).
\]

F remains the original ordered contraction rather than a screen norm. The null theorem retains symmetry/nonzero ξ and does not claim nonnegative F on arbitrary tensors/covectors. Real-scalar linearity of the Ricci symbol and F is actually implemented and audited too.

## Registration and actual declarations

Nine main support targets and three independent scalar-interface audit targets are registered, not12 new formal article results.

| Manifest-ID suffix (all prefixed polarization:) | Actual declaration (all in Burnett.RicciSymbol) |
| --- | --- |
| real-symmetry | mixedQuadraticSymbol_comm |
| real-add-left / real-add-right | mixedQuadraticSymbol_add_left / mixedQuadraticSymbol_add_right |
| real-smul-left / real-smul-right | mixedQuadraticSymbol_smul_left / mixedQuadraticSymbol_smul_right |
| real-diagonal | mixedQuadraticSymbol_diag |
| real-polarization | mixedQuadraticSymbol_polarization |
| real-noncharacteristic-mixed | mixedQuadraticSymbol_eq_zero_of_noncharacteristic_kernel |
| real-null-mixed | mixedQuadraticSymbol_eq_physicalPairing_of_null_kernel |
| ricci-real-smul | ricciSymbol_smul |
| physical-real-smul-left / physical-real-smul-right | physicalPairing_smul_left / physicalPairing_smul_right |

Central queries inspected the actual types of all 29 public declarations (2 definitions and 27 theorems). Source SHA256 `5993bc6169017387715a3a3e926aa4202ffff3e45ab080414e11f2ef993b7dd4`. Machine checks, independent semantic review, and author confirmation are recorded separately. [Readback](real-polarization-review.en.md) · [Test report](../formalization/f06-workflow-test.en.md)

F06 remains partial. Complex Hermitian results, null frames/physical-quotient positivity, geometric/measure bridges, and global closure of17 numbered results are outside this batch. Compilation, agent agreement, or PR merging do not replace author confirmation or a final trust choice.
