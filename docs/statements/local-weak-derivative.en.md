# Local weak derivatives against fixed tests

This supplies support for linear weak vanishing at source lines 376–388. Module `Burnett.Analysis.LocalWeakDerivative` retains all 19 declarations and registers 6 semantic endpoints. Parent results, F04/F05, and the whole article remain OPEN; author confirmation is pending. See the [shared bindings](intrinsic-dh-geometry-source-bindings.json) and [review](local-weak-derivative-review.en.md) for input identity and independent review.

U is an actual open four-dimensional coordinate domain. The fixed ψ is smooth on the whole space and compactly supported, with tsupportψ⊂U. The sequence fₙ and fixed coefficient a need only be smooth within U; their total-function values outside the chart are arbitrary. ψ, a, the directions v/w, and the chart are fixed before n.

Using the zero germ of ψ outside U, the proof establishes whole-space smoothness and compact support of ψf and ψa. After proving integrability term by term, it integrates by parts once or twice. If fₙ tends uniformly to zero on every fixed compact subset of U, then

    ∫ ψ a D_v fₙ → 0,   ∫ ψ a D_v D_w fₙ → 0.

The second integration by parts moves D_vD_w to D_wD_v on the test, without invoking an unproved derivative-commutation result or a uniform second-derivative bound.

The original geometric instance derives vanishing first- and second-derivative test integrals of the actual coordinate components of gₙ−g₀ from the same physical r-based C⁰loc convergence and actual smooth fields. Callers need not additionally supply coordinate convergence. This linear step itself does not require the Dh bound.

Smoothness within the chart of ρ₀=√|detG₀| for the same g₀ is proved from its actual nonzero determinant. Γ₀ is the actual computedConnection of that same g₀; existing identification results interpret it as the Levi-Civita coefficients for the original symmetric nondegenerate background. The final conclusions give vanishing fixed tests of ρ₀Γ₀∂hₙ and ρ₀a∂²hₙ.

These actual Lean types express Lebesgue integrals with the coefficient ρ₀; no new withDensity integral identity is introduced here. One cannot directly substitute the n-dependent inverse coefficients of gₙ for the fixed a, or infer full weak* L∞, weak L², or strong H⁻¹ convergence. The complete vacuum Ricci test identity, nonlinear quadratic terms, and exact correction by minus the old B still require actual assembly.
