# Mathematical interface review of the main theorem

This corresponds to `paper/burnett.tex`, SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`. Review date:2026-11-15. References use source lines/labels of that byte snapshot. Scope/progress remain governed by `../formalization/scope.json`; no separate acceptance checklist is created here.

This pass independently read statements/consumers of the main theorem, quadratic-measure construction, and transport. The following explains mathematical targets/proof-route interfaces. No actual Lean types yet exist for reverse review; the main theorem, whole-paper correctness, applicability of external citations, and user/author confirmation are not established. The source's proposed-proof status is unchanged, and truth/falsity is not decided here.

## 1. Input objects and every explicit assumption

Sources: `eq:admissible`,90–108; `eq:hamiltonian`,110–120.

1. `M` is a smooth Hausdorff second-countable four-manifold.
2. `g` is a smooth time-oriented Lorentz metric on `M`, with signature `(-,+,+,+)`.
3. `r` is a fixed smooth auxiliary Riemannian metric; `D = ∇ʳ`. Covector `|ξ|ᵣ` uses inverse `r`. Completeness of `r` is not assumed.
4. `(gₙ)ₙ∈ℕ` are smooth Lorentz metrics on `M`. Put `hₙ = gₙ − g`; require `Ric(gₙ)=0` for each `n`.
5. `hₙ → 0` in `C⁰_loc(M)`: uniform convergence on each compact set in a fixed positive-definite norm.
6. For each `K ⊂⊂ M`, a finite `C_K` bounds `‖Dhₙ‖_{L∞(K;r)} ≤ C_K` for all `n`. The order is `∀ K ∃ C_K < ∞ ∀ n`, not separate bounds for individual `n`.
7. The cosmological constant is zero and `8πG_N=1`.

There is no extra coordinate gauge, symmetry, number-of-phases restriction, convergence rate, or second-derivative scale. Global hyperbolicity is not assumed for `gₙ`, nor for `g` in the global-ray conclusion. Time orientation of `gₙ` is not separately assumed. Eventual uniform inverse bounds on fixed compacts should follow from the smooth nondegenerate limit and uniform convergence, not be new theorem inputs (360–369).

## 2. Phase space, tests, and finiteness

Write

$$
S_r^*M=\{(x,\xi)\in T^*M:|\xi|_r=1\},\qquad
P(x,\xi)=\tfrac12g^{ab}(x)\xi_a\xi_b,
$$

$$
H_P=g^{ab}\xi_b\partial_{x^a}
-\tfrac12\partial_{x^c}g^{ab}\xi_a\xi_b\partial_{\xi_c}.
$$

Source: `eq:hamiltonian`,110–120. `S_r^*M` is the nonzero cotangent bundle modulo **positive** scaling: `ξ`/`−ξ` stay distinct, retaining both time directions. Temporary projective caps in Section5 do not replace the target by a space identifying `±ξ` (928–951,1015–1016).

For nonnegative Radon `μ`, local finiteness over the base means

$$
\mu\bigl(\pi^{-1}(K)\cap S_r^*M\bigr)<\infty
\quad\text{for every compact }K\Subset M.
$$

Unit fibers over compact bases are compact; this is compatible with Radon local finiteness on the smooth finite-dimensional unit cosphere bundle, not finite total mass on `S_r^*M`. Smooth compact-base-support tests are bounded on the unit section, giving well-defined integrals below.

Moment tests are all real smooth compactly supported symmetric contravariant two-tensors
`S ∈ C_c^∞(M; Sym² TM)`. `G(g)` has lower indices in the identity; volume is the density
`dV_g=√|det g| dx`, requiring no volume-form orientation. Sum index pairs as ordered pairs (331–350).

Transport tests are all real smooth functions

$$
a:T^*M\setminus0\longrightarrow\mathbb R,
\qquad a(x,t\xi)=t\,a(x,\xi)\ (t>0),
$$

with compact `K ⊂⊂ M` such that `a(x,ξ)=0` for all nonzero `ξ` when `x∉K`. This is compact **base** support, not compact total-cotangent support. Positive homogeneity does not mean `a≥0`. Compute `H_Pa` on the punctured bundle before unit restriction; it is two-homogeneous, not an undefined derivative of a unit-section function alone (128–135). Homogeneity and `H_PP=0` follow from the formula, but do not prove transport.

## 3. Exact targets and quantifier order

Sources: `thm:main`,139–168; concluding proof3046–3060.

For every data set satisfying Section1, the target is **one common subsequence** and a global nonnegative Radon `μ` on `S_r^*M` satisfying together:

1. `μ` is base-locally finite and supported on `Z={P=0}∩S_r^*M`.
2. For all such `S`,

   $$
   \int_M G(g)_{ab}S^{ab}\,dV_g
   =\int_{S_r^*M}S^{ab}(x)\xi_a\xi_b\,d\mu,
   \qquad \operatorname{Scal}(g)=0.
   $$

3. **The same `μ`** satisfies, for all such `a`,

   $$
   \int_{S_r^*M}H_Pa\,d\mu=0.
   $$

Then for **each** open subspacetime `U⊂M` globally hyperbolic for induced `g|_U`, there is a nonnegative Radon `ν_U` on `T^*U\setminus0`, supported on the nonzero null cone, satisfying together

$$
\forall K\Subset U,\qquad
\int_{\pi^{-1}(K)}|\xi|_r^2\,d\nu_U<\infty,
$$

$$
\forall S\in C_c^\infty(U;\operatorname{Sym}^2TU),\qquad
\int_U G(g)_{ab}S^{ab}\,dV_g
=\int_{T^*U\setminus0}S^{ab}\xi_a\xi_b\,d\nu_U,
$$

$$
\forall b\in C_c^\infty(T^*U\setminus0),\qquad
\int_{T^*U\setminus0}H_Pb\,d\nu_U=0.
$$

`H_P`, `r`, `g` restrict to `U`. `b` has compact **total-space** support with no homogeneity. Second moments need only be finite over compact bases, not globally; finite total mass is not required. Local second moments ensure moment-test integrability, while Radon regularity ensures integrability of compactly supported `H_Pb`.

The quantifier skeleton is

```text
∀ admissible (M,g,r,(gₙ)),
  ∃ strictly increasing subsequence selector φ, ∃ μ,
    [one extracted defect witness along φ for the proof route]
    ∧ [support, local base finiteness, every tensor moment, Scal(g)=0]
    ∧ [∀ degree-one compact-base a, transport for this μ]
    ∧ [∀ globally hyperbolic open U, ∃ ν_U,
         every local moment bound, every tensor moment, every compact-total-space b].
```

The bracketed defect witness belongs to the proof route; displayed `thm:main` does not separately state all quadratic-test limits. It may later be passed as a constructed witness, but cannot become an extra existence/transport input while claiming the original theorem proved.

Subsequence selection precedes `S`, `a`, atlas, localization parameters, and `U`. Different tests/charts cannot select different measures, nor may another equal-moment measure replace constructed `μ`: second moments do not determine the angular measure (481–485,501–502). `ν_U` may depend on `U`/characteristic section; cross-U compatibility or uniqueness is not claimed.

## 4. Quadratic and same-measure transport interfaces

`thm:quadratic` (354–356) gives global `μ` on the same subsequence, moments, null support, and zero scalar curvature, explicitly without transport. The construction is

$$
d\mu=\tfrac14\mathbf1_Z
\left(g^{ac}g^{bd}-\tfrac12g^{ab}g^{cd}\right)d\sigma_{ab,cd}.
$$

Source: `eq:mu-invariant`,469–485. `σ` comes from the same full tensor microlocal defect, not an arbitrary moment representation. Its coordinate components are covariance tensors, not endomorphism matrices after identification via `r` (421–428). Raw defects may have gauge components off the cone; positive physical contraction follows restriction to `Z`.

`thm:variational-transport` (1729–1735) receives this same `μ` and gives transport for all one-homogeneous tests. Its core identity is

$$
4\int H_Pa\,d\mu
=-\lim_n\operatorname{Im}\langle E''_g[h_n,h_n],B_ah_n\rangle.
$$

Source: `eq:var-cubic-residual`,1811–1903. `E(g)^{ab}=√|det g| G(g)^{ab}`. The right side uses fixed Lebesgue density, lower-index metric variations, and self-adjoint order-one `B_a` scalar at every symbol order. Density conversion `σ_{dx}=w^{-1}σ` and factor4 have explicit consumers at1811–1835; the factor2 of a reduced scalar-wave identity cannot replace them. Only the total cubic residual needs a limit; individual summands need not converge (2955–2960).

This pass checked identity transmission/source locations, not the residual identity or its vanishing independently. Open obligations and finite executable order are in `../formalization/dependencies.md`.

## 5. Complete globally hyperbolic lift interface

Source: `lem:lift`,2989–3043. Inputs: smooth globally hyperbolic background and a nonnegative, base-locally-finite, null-supported ray measure **already satisfying both moments and transport**, not necessarily from a vacuum sequence. Outputs must expand into all three conclusion groups for `ν` in Section3, not an undefined “full null cotangent representation” field.

The proof chooses a smooth spacelike Cauchy hypersurface `Σ`, records `ξ_Σ` at the unique crossing of each inextendible null geodesic, and defines

$$
\mathcal E(x,\xi)=|\xi_\Sigma|_r,
\quad \mathcal E(x,t\xi)=t\mathcal E(x,\xi),
\quad H_P\mathcal E=0,
$$

$$
s(x,\omega)=\mathcal E(x,\omega)^{-1},
\quad L(x,\omega)=(x,s(x,\omega)\omega),
\quad \nu=L_*(s^{-2}\mu).
$$

`s`/`s⁻¹` are bounded on the unit null bundle over compact bases; the source uses this for Radon regularity and the exact identity

$$
\int_{\pi^{-1}(K)}|\xi|_r^2\,d\nu
=\mu(\pi^{-1}(K)\cap S_r^*M).
$$

For compact-total-support `b`, first define on the null cone

$$
a(x,\rho\omega)=\frac{\rho}{s(x,\omega)}
b(x,s(x,\omega)\omega),
$$

then take a smooth angular extension preserving compact base support. The image of `L` is `H_P`-invariant; two-homogeneous scaling cancels `s⁻²`, giving full transport from ray transport (3013–3039). Existence/smoothness of the geometric section, initial-data dependence of intersections, and extension still need proof; this pass only identifies/checks their uses.

No affine completeness or compact Cauchy surface is needed (3006–3007). Arbitrary radial product `ρ⁻³ dρ dμ` has divergent second moment and cannot substitute (3043). Nor may `thm:quadratic` alone enter `lem:lift` while bypassing transport.

## 6. Modeling decisions and verified boundaries

No substantive ambiguity requiring a user choice was found in the main inputs, test classes, same-measure condition, or globally hyperbolic-region quantifiers. These retain stated objects/quantifiers. All compact sets versus equivalent relatively-compact-open formulations is a representation choice, not a stronger assumption.

Two distinctions remain necessary before modeling, without rewriting the source first:

- **Displayed target versus proof witness.** The main display requires only moments/transport for `ν_U`; the construction also supplies weighted pushforward and exact local second moments. Those may be stronger internal lift outputs; promoting them to extra user-confirmed main conclusions requires explanation/confirmation separately. The displayed target remains unchanged here.
- **All smooth tests versus local quantized definitions.** Main tests are all smooth one-homogeneous functions. The proof reduces via antipodal invariance to real odd tests (1906–1915), then quantizes in a finite atlas. Local compatible data/global functions are possible, but equivalence to all tests must be proved. Odd tests alone leave a gap without antipodal invariance/even-test vanishing.

Unread original external theorems, unreconstructed analytic proofs, and unchecked library interfaces remain separately pending in dependencies. They are neither automatic article errors nor reasons automatically to strengthen main assumptions.
