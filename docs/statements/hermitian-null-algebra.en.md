# F06: complex Hermitian algebra and physical null-cone positivity

Source: `paper/burnett.tex:338,430–465`. This explains the batch's actual new declarations. Central target audits, independent reverse review, and confirmation of the new explanation are separate; this page does not replace them.

## Objects and conventions

Use four ordered coordinate indices. Inverse metric G/covector ξ are real; complex amplitudes are transpose-symmetric k_ab=k_ba, not required to be Hermitian matrices. As at source338, pairings are first-slot linear and second-slot conjugate-linear.

Actual complexification of the original connection symbol gives ordered cross product C; define H_B(k,l)=[C(k,conj(l))+C(conj(l),k)]/2. The physical form is directly

\[
H_F(k,l)=\sum_{a,b,c,d}G^{ac}G^{bd}k_{ab}\overline{l_{cd}}
 -\tfrac12\operatorname{tr}_G(k)\overline{\operatorname{tr}_G(l)}.
\]

The code proves bridges from these original definitions to real pairings of real/imaginary parts, rather than defining a new form by the desired conclusion. The addition, complex-scalar, and conjugate-symmetry declarations in `ComplexPolarization.lean` give an actual Hermitian form. Embedded real amplitudes recover the existing real mixed form and original B diagonal.

## Implemented mathematics

1. The complex Ricci symbol vanishes exactly when the real and imaginary amplitude parts each lie in the original real Ricci kernel.
2. For s≠0, H_B vanishes for any two amplitudes in the same complex Ricci kernel.
3. For ξ≠0 and s=0, assume symmetric G, k, and l and that k and l belong to the same complex Ricci kernel for ξ. Then H_B,bc(k,l)=ξ_bξ_c H_F(k,l)/4. The H_F cross-pairing of a kernel amplitude with an actual gauge tensor vanishes.
4. Actual real/complex pure-gauge tensors lie in the Ricci kernel. Adding independent arbitrary gauge tensors to both null-kernel amplitudes preserves the physical pairing.
5. For standard inverse metric η=diag(-1,1,1,1), ξ=(-1,1,0,0), kernel amplitudes have an explicit gauge-plus-trace-free-screen decomposition; H_F(k,k)=2(|k_22|²+|k_23|²), with zero physical norm exactly for gauge tensors. Every pair of complex screen parameters actually gives a symmetric kernel amplitude.
6. For every nonzero standard-η null covector, nullness first gives ξ_0≠0; an explicit gauge transformation removes the amplitude's time row. The kernel constraint forces zero trace, making original real F a sum of remaining-component squares. Positivity and the zero-space criterion do not require an assumed fixed null direction.
7. For an actual basis change E, trace, full ordered contraction, Ricci kernel, and physical pairing transform under G=EηEᵀ, ξ'=Eᵀξ, k'=EᵀkE. Actual basis injectivity/surjectivity pulls gauge vectors back to original coordinates.
8. A `TensorFrame.LorentzFrame G` certificate contains only a basis bijection and inverse-metric normal form. Under it, H_F(k,k) on the null kernel of general G has zero imaginary part and nonnegative real part, and vanishes exactly for an actual complex pure-gauge k. The certificate contains no desired positivity/kernel conclusion.

## Modules and principal actual declarations

| Module | Main declarations or role |
| --- | --- |
| `ComplexPolarization.lean` | `hermitianQuadraticSymbol_eq_zero_of_noncharacteristic_kernel`, `hermitianQuadraticSymbol_eq_physicalPairing_of_null_kernel`, and original-definition bridges |
| `NullScreen.lean` | `NullScreen.kernel_decomposition`、`physicalPairing_eq_screen` |
| `HermitianScreen.lean` | General gauge-kernel membership, invariance of both representatives, and complex standard-screen decomposition |
| `MinkowskiNull.lean` | `physicalPairing_self_nonneg` and `physicalPairing_self_eq_zero_iff_pureGauge` for every nonzero η-null ξ |
| `TensorFrame.lean` | Real contraction/kernel covariance and actual basis certificates |
| `ComplexFrame.lean` | Complex contraction/kernel covariance and basis-change injectivity/surjectivity |
| `LorentzPhysical.lean` | Real physical positivity and actual gauge zero space under general certificates |
| `LorentzHermitian.lean` | Complex physical positivity, real diagonals, and actual complex gauge zero space under general certificates |

Actual names are governed by the central target manifest and independent type queries. These support results do not complete any of the17 formal article results.

## Two-parameter classification and normalization

`MinkowskiNormalize.exists_normalizing_frame` constructs a normalizing frame for every nonzero standard-η null direction through actual Lorentz reflections, deriving every nonzero denominator from nullness/nonzero ξ. `NullFrame.exists_normalized_frame` composes this with a supplied general Lorentz basis rather than adding normalization as a final hypothesis.

`PhysicalQuotient.coordinates` chooses one frame depending only on G, the original basis, and ξ, using the same complex-linear map to ℂ×ℂ for all amplitudes. Equal coordinates are proved equivalent to a pure-gauge difference; every pair of complex parameters is realized by a genuine symmetric Ricci-kernel amplitude in original coordinates, and

\[
H_F(k,l)=2(a\overline c+b\overline d).
\]

These equivalence, surjectivity, and linear pairing identities give two free complex parameters for physical classes, not only a dimension upper bound. No existing quotient object is assumed, and no finrank theorem for an unconstructed quotient type is additionally claimed.

## Current integration boundaries

Two-dimensional classification, actual pointwise normalization, and original-coordinate realization of all parameter pairs are proved by those two-way contracts. Later modeling must actually supply/derive pointwise frame certificates from general Lorentz geometric objects; arbitrary real symmetric G is not treated as Lorentz-signature. Pointwise choices claim neither global smoothness in position/frequency nor uniform estimates; V06 and other consumers need their own contracts.

Measures, measure pairing of positive Hermitian covariance, subsequences, quadratic-theorem assembly, and transport remain future work. On2026-11-16 the user explicitly chose “Delegate confirmation to you and an independent agent (recommended)” for this pointwise complex algebra/two-dimensional classification. Root confirmed the local correspondence using actual declarations and independent frozen-source/type readback, not personal line-by-line Lean review by the user/author. The batch review records the confirmation version/source bindings. The user separately choseA for closed final mathematical dependencies and the three-foundational-axiom policy.
