# Connection-error tests under the original assumptions

Module `Burnett.Analysis.LocalWeakRicci` adds 8 support theorems and registers 4 actual consumers, corresponding to source lines 358–381. See the [bindings](intrinsic-dh-geometry-source-bindings.json) and [review](local-weak-ricci-review.en.md) for source and reviewer identities. This step does not close the complete weak Ricci result, H⁻¹, F04/F05, or the whole paper; author confirmation of the new explanation has not been recorded.

The exact decomposition Cₙ=Γ(gₙ)−Γ(g₀)=L(D^{g₀}Hₙ)+Eₙ is retained, where Hₙ=gₙ−g₀ and L is the Christoffel contraction with the background g₀ inverse matrix. The linear term always uses D^{g₀}Hₙ.

From actual smoothness and nondegeneracy of the fields, the proof establishes smoothness of each Eₙ component within chart.target, including the actual computedΓ, matrix inverse, genuine first Fréchet jet, and auxiliary covariant jet. Smoothness of E is not a caller input. The original physical C⁰loc convergence and locally uniform L∞ bound for Dh under the same μ₀ then give uniform convergence of the Eₙ components to zero on compact sets.

For fixed whole-space smooth compactly supported ψ with tsupportψ⊆this chart.target, a fixed coefficient A smooth within the chart, and a fixed direction v, the terms are integrable and the proof establishes

    ∫ ψ A Eₙ → 0,   ∫ ψ A D_v Eₙ → 0,
    ∫ ψ ρ₀ A D_v Eₙ → 0,   ∫ ψ ρ₀ Γ₀ Eₙ → 0.

ρ₀ and Γ₀ are the actual density and connection of the same g₀. Finally, the partial derivative and three classes of Γ₀E terms are assembled into the actual `CurvatureDifference.covariantDerivative`, whose jet is exactly `coordinateConnectionJet`, to prove vanishing of the ρ₀ test integral of each actual ∇^{g₀}Eₙ component. Integrability of every term is derived before interchanging integrals and finite sums.

These are Lebesgue integrals with coefficient ρ₀; tests and coefficients are fixed before n. No additional uniform D²gₙ, global frame, or hidden small-error assumption is used.

The existing exact Ricci difference identity contains Q(C)=Σ(Cᵃ_ae Cᵉ_bc−Cᵃ_ce Cᵉ_ba). The existing rank-one symbol identification gives Q=−old B; that symbol-specific theorem cannot be applied to arbitrary jets without proof. This batch preserves the minus sign and does not claim a general quadratic limit or defect-measure representation.

The next consumer must contract these components, assemble vanishing tests of the linear term L(D^{g₀}Hₙ), prove quadratic-error replacement for C=L+E, and derive the complete weak Ricci identity from actual Ricci-flat geometric data. Phase-space measures, H⁻¹ compactness, and transport remain separate work.
