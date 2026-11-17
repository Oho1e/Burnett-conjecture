# Auxiliary metrics, physical tensor norms, and local L∞ control

This batch serves locked source lines 91–105 and 352–389. It constructs actual auxiliary connections, physical covariant-tensor norms, positive-density measures, and a genuine L∞ model for connection errors in local coordinates. Pullback from the original manifold charts, the physical norm of the mixed error tensor, and complete F04 closure remain separate proofs. Support results do not close parent `thm:quadratic`; the whole paper remains in development.

## Actual norms and indices

`GramCoordinateBound` defines the actual energy `gramEnergy G x = xᵀGx` and its square root, proves equality with the Hilbert norm constructed from a positive-definite matrix, and uses Cauchy–Schwarz in that inner product to prove

\[
 |x_i|^2\le (G^{-1})_{ii}\,x^TGx.
\]

`CovariantTensorNorm` takes R as the **covariant** auxiliary metric matrix and S as its actual matrix inverse. The energies of covariant order-two and order-three tensors are

\[
 Q_2(H)=\sum_{i,j,a,b}S_{ia}S_{jb}H_{ij}H_{ab},\qquad
 Q_3(T)=\sum_{i,j,k,a,b,c}S_{ia}S_{jb}S_{kc}T_{ijk}T_{abc}.
\]

The module actually proves that their Gram matrices are S⊗S and (S⊗S)⊗S, including positive definiteness and inverses. `flatten2/3` explicitly uses row-major indices; the transpose required by mathlib's `Matrix.vec` cannot be omitted. These norms are `Real.sqrt Q₂/₃`, not renamed Pi sup norms. The coordinate bound uses diagonal entries of R:

\[
 |T_{ijk}|\le\sqrt{R_{ii}R_{jj}R_{kk}}\,|T|_r.
\]

Continuity of the R diagonal on a fixed compact set gives an actual uniform C>0 such that every tensor satisfies `‖T‖Pi ≤ C * norm3 R T`; C is independent of T and sequence index n. The order-two version is also implemented. This comparison does not include the reverse physical-norm bound or naturality under basis change.

## The actual auxiliary derivative and a larger neighborhood

`AuxiliaryConnection.auxiliaryPerturbationJet r g₀ g₁` actually computes

\[
 (D^r h)_{bcd}=\partial_bh_{cd}
  -\Gamma(r)^e{}_{bc}h_{ed}-\Gamma(r)^e{}_{bd}h_{ce},\qquad h=g_1-g_0.
\]

Γ(r) is constructed from the actual inverse of r and first Fréchet derivatives of its components. C¹ components and compactness give a uniform connection bound. Substitution of minus the same Γ solves for the raw first jet; Dᵣ is not identified with coordinate partial differentiation, and the Γ bound is not an extra source assumption.

For open O and K⊆O⊆S, `LocalAeBound` upgrades an a.e. bound under the measure restricted to S to a pointwise bound on K, assuming continuity of the norm on O and positive measure for nonempty open subsets of O. In particular, K itself may be null. An a.e. bound only under μ.restrict K cannot give a bound at every point of K. An actual F-valued continuous function on a measurable compact set belongs to L∞ without requiring μ(K)<∞; a separate arbitrary-p result concerns only the scalar norm and explicitly requires finite mass. These results are not conflated.

## Actual assembly of local connection errors

`AuxiliaryPhysicalBound` first derives nondegeneracy and symmetry of the actual bilinear r from positive definiteness of R. On every compact S⊆U, it assumes a uniform actual `eLpNorm ... ∞` bound for physical `norm3(Dʳhₙ)` of the same sequence under μ.restrict S. μ need only give positive measure to nonempty open subsets of U; no support condition outside U is required.

From compact K⊆U, the final theorem **constructs** S with K⊆interior S⊆S⊆U. It then obtains physical-to-coordinate bounds, pointwise auxiliary-derivative bounds on K, a uniform raw-jet bound, and uniform vanishing of the actual connection error Eₙ. It also actually constructs `MemLp ... ∞` and `toLp` classes for every Eₙ under μ.restrict K and proves norm convergence of these genuine L∞ elements to zero. Callers need not separately supply MemLp or a representative. `ConnectionErrorLInfinity` supplies the required continuity and L∞ construction.

The local C¹ components of gₙ, g₀, and r follow from original smoothness, without a uniform second-derivative estimate. Nondegeneracy and neighborhood symmetry of gₙ, and uniform component convergence, still explicitly come from the original geometric data. The output L∞ currently uses the Pi sup norm of connection arrays; the physical-r norm of the mixed (1,2) tensor remains to be identified.

## Positive densities and coordinate volume

`PositiveDensity` proves restricted-measure null-set, a.e., and L∞ comparisons for actual `μ.withDensity w`. Local measurability and positivity must come from the actual density; assumed mutual absolute continuity does not replace the construction. `RiemannianVolume` uses the actual

\[
 \rho_R(x)=\sqrt{\det R(x)},\qquad d\mu_R=\rho_R\,dx
\]

to construct the coordinate measure of positive-definite R, proving local measurability, positivity, and positive mass of open sets, then instantiating the physical assembly at R=metricComponents r. This measure is defined by an explicit density; no claim is made that the original manifold volume has already been proved to push forward to it.

## Scope of proofs and completion

See the [source bindings](auxiliary-r-control-source-bindings.json) for actual declarations and frozen inputs, and the [review record](auxiliary-r-control-review.en.md) for independent readback. Machine checks bind the actual candidate and logs; a development merge does not supply author confirmation or a whole-paper tag.

Next, the original manifold r, D=∇r, and volume must be represented in charts, with naturality of tensor norms/local C⁰ and the mixed-error physical norm, followed by fixed-test integration by parts, weak Ricci identification, and H⁻¹ compactness. Actual F05 uniform PDO bounds, vanishing-error positivity, and common-measure construction remain open; proved local norm tools do not replace them.
