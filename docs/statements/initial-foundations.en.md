# First foundations batch: fiber coordinates, a common subsequence, and fixed Fourier off-cone tools

This corresponds to work-file tasks N1/N2/N3. Every new target supports an original result; unfinished `thm:quadratic`, transport, main theorem, and fixed Fourier projection targets are not registered as proved. The fixed article, Lean4.24.0, mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and three-axiom policy are unchanged.

## 1. Actual fiber metrics and the F06 coordinate interface

Let V be a real vector space, b an actual Fin4-indexed basis, and g a nondegenerate bilinear form. Define covariant components `G_ij=g(b_i,b_j)` and the actual inverse `sharp` of left lowering `flat(v)=g(v,·)`. Contravariant components are constructed from the metric-dual basis, without inverse identities or Ricci conclusions as structure assumptions.

**Convention boundary: for general nonsymmetric g, this follows left lowering and gives G⁻ᵀ.** Actual metric applications have symmetric g; `covariant_mul_contravariant` and `contravariant_mul_covariant` explicitly assume `g.IsSymm`, giving ordinary G⁻¹. The finite sum `raiseCovector` is the coordinate representation of actual `sharp ξ`, and `symbolNorm` is `ξ(sharp ξ)`.

For another actual basis c, let E have columns equal to c's coordinates in b. The earlier transformations are identified as Eᵀξ for covectors and EᵀKE for covariant bilinear tensors; the covector transformation is bijective.

Given a Lorentz orthonormal-basis identity for the **covariant form itself**,

```text
g(c_a,c_d) = η_ad,   η = diag(-1,1,1,1),
```

contravariant components are derived as EηEᵀ and the old `TensorFrame.LorentzFrame` is actually constructed. Existing real null-kernel physical-pairing nonnegativity from F06 then applies to these actual fiber data. Nonzero ξ, symmetric k, nullness, and the actual Ricci-symbol kernel remain premises; none is dropped.

An explicit nondegeneracy proof for `modelMetric c(v,w)=Σ_a η_a c^a(v)c^a(w)` and a standard ℝ⁴ instance prevent a mere uninstantiated certificate. `standardFiberFrame` is an actual definition with additional actual type/transitive-axiom checks, not disguised as an article-theorem target.

Still missing: orthonormal-basis existence from an independent inertia/signature definition, local smooth selection, manifold gluing, connection/Ricci, volume densities, and measure covariance. A given pointwise orthonormal basis does not formalize these.

## 2. A common subsequence for countable F05 tests

For countable index ι, first-countable topological X, and compact value sets K_j, if `a_n(j)∈K_j`, there are one strictly increasing φ and limits l_j with simultaneous convergence along **the same** φ and `l_j∈K_j`. For real values, a uniform `|a_n(j)|≤C_j` bound is retained by the limit.

The proof uses compactness and first countability in a countable product. General weak-star compactness is not simply treated as sequential compactness; a convergent subnet in a compact set does not replace this strictly increasing subsequence.

This tool supports the common-subsequence step at source398–403; it is **not** positive microlocal-defect extraction. Actual PDO-test bounds, a countable dense test family, extension to all symbols, positivity, measure representation, and atlas/bundle transitions require separate proofs. Explicit bounded/compact-value assumptions of general tests are not treated as Lean proofs already supplied by the original article.

## 3. X02 frequency geometry and actual Fourier tails

Retain original `fSequence`/`wSequence`, N=n+1, u=t−x, v=t+x. The two cosine-phase angular frequencies in the actual f gradient are

```text
κ_f,s = (N²+sN, -N²+sN, 0, 0),  s=±1,
κ_w   = (2N, 2N, 0, 0).
q(ξ)  = -ξ₀²+ξ₁²+ξ₂²+ξ₃².
```

Actual theorems connect these vectors with component derivatives, rather than inserting frequencies by hand and ignoring the functions. q(κ_f,s)=−4sN³ and `‖κ_f,s‖²=2N⁴+2s²N²`; w frequency is exactly null, and all these frequency norms tend to infinity.

For fixed δ>0, `Eδ={ξ≠0 : δ‖ξ‖²≤|q(ξ)|}`. If κ≠0 and `|q(κ)|≤δ‖κ‖²/8`, then for **every** ξ∈Eδ,

```text
min(1/2, δ/160) ‖κ‖ ≤ ‖ξ−κ‖.
```

This gives geometric input for whole-space translated tails, without restricting to bounded frequency domains. Actual Fourier normalization is `exp(-2π i⟪x,ξ⟫)`; actual modulation gives Fourier translation, with angular-frequency centers `±κ/(2π)`.

For any fixed complex Schwartz ψ, `|Fourier ψ|²` is proved integrable on the whole space and its squared tail integral tends to zero as radius grows; the corresponding result for pointwise-escaping measurable regions is also proved. Combining actual separation with these tails gives vanishing Fourier energy on fixed Eδ for every positive/negative normalized mode of the same f/w.

## 4. Schwartz Parseval and the cutoff-product bridge

For complex Schwartz functions on a finite-dimensional real inner-product space, the fixed library's L¹ integral-interchange theorem and Schwartz Fourier inversion directly prove

```text
∫ |Fourier ψ|² = ∫ |ψ|².
```

This is an actual full-space integral identity, not an unidentified L² extension. Modulation identities can be written for Lean's total integrals without integrability assumptions, but this batch's energy applications use Schwartz functions with separate integrability proofs, not default zero values for nonintegrable integrals.

The cutoff argument applies the product rule to actual χ∈C∞c and h=f_n or w_n:

```text
∂ᵢ(χh_n) − χ∂ᵢh_n = (∂ᵢχ)h_n.
```

The right side tends to zero as an actual whole-space L² element; every fixed L² CLM preserves this smallness. Such an arbitrary-map parameter is **not** presented as a constructed Fourier projection, and χ is not commuted with a nonlocal operator.

Actual finite modes are fully assembled: for every original real C∞c cutoff χ and fixed δ>0, separately for h_n=fSequence n and wSequence n,

```text
lim_n Σ_{i=0}^3 ∫_{Eδ} |Fourier(χ ∂ᵢh_n)(ξ)|² dξ = 0.
```

Each component also satisfies its own conclusion; no single support compact set or component is fixed as a restriction. The product rule is also connected to actual L² objects `productGradientLp` and `localizedGradientLp`, whose difference tends to zero under every fixed L² CLM A.

These conclusions do not automatically give a Fourier isometric extension on all L². Actual fixed sharp/smooth projections, compatibility, and their physical L² conclusions must still be completed to close source3193. These remain proved parts of the full parent target.

## 5. Actual registration and evidence

Each registered item is a proved theorem; auxiliary lemmas are audited through actual proof dependencies, not every calculation counted as an article result. See [initial-foundations-review.md](initial-foundations-review.en.md) for names, types, input versions, and independent readback. Scope retains all17 original formal results and3 required unnumbered results.

| Support ID | Actual declaration | Consumer slice |
| --- | --- | --- |
| `f05:countable:exists-subsequence-all-tests` | `Burnett.Analysis.Compactness.exists_subsequence_all_tests` | F05 |
| `f05:countable:exists-subsequence-of-testwise-abs-le` | `Burnett.Analysis.Compactness.exists_subsequence_of_testwise_abs_le` | F05 |
| `f06:geometry:covariant-mul-contravariant` | `Burnett.Geometry.FiberMetric.covariant_mul_contravariant` | F06 |
| `f06:geometry:contravariant-mul-covariant` | `Burnett.Geometry.FiberMetric.contravariant_mul_covariant` | F06 |
| `f06:geometry:raiseCovector-eq-sharp` | `Burnett.Geometry.FiberMetric.raiseCovector_eq_sharp` | F06 |
| `f06:geometry:symbolNorm-eq-eval-sharp` | `Burnett.Geometry.FiberMetric.symbolNorm_eq_eval_sharp` | F06 |
| `f06:geometry:covector-components` | `Burnett.Geometry.BasisFrame.covector_components` | F06 |
| `f06:geometry:tensor-components` | `Burnett.Geometry.BasisFrame.tensor_components` | F06 |
| `f06:geometry:covector-bijective` | `Burnett.Geometry.BasisFrame.covector_bijective` | F06 |
| `f06:geometry:inverseMetric-components` | `Burnett.Geometry.BasisFrame.inverseMetric_components` | F06 |
| `f06:geometry:physicalPairing-self-nonneg` | `Burnett.Geometry.BasisFrame.physicalPairing_self_nonneg` | F06 |
| `f06:geometry:modelMetric-nondegenerate` | `Burnett.Geometry.BasisFrame.modelMetric_nondegenerate` | F06 |
| `x02:offnull:D-fSequence-two-cosines` | `Burnett.CubicOffNull.D_fSequence_two_cosines` | X02 |
| `x02:offnull:D-wSequence-cosine` | `Burnett.CubicOffNull.D_wSequence_cosine` | X02 |
| `x02:offnull:offNull-separation` | `Burnett.CubicOffNull.offNull_separation` | X02 |
| `x02:offnull:fAngularFrequency-eventually-near-null` | `Burnett.CubicOffNull.fAngularFrequency_eventually_near_null` | X02 |
| `x02:offnull:tendsto-norm-fAngularFrequency` | `Burnett.CubicOffNull.tendsto_norm_fAngularFrequency` | X02 |
| `x02:offnull:tendsto-norm-wAngularFrequency` | `Burnett.CubicOffNull.tendsto_norm_wAngularFrequency` | X02 |
| `fourier:fourier-tail-tendsto-zero` | `Burnett.Fourier.fourier_tail_tendsto_zero` | X02 |
| `fourier:schwartz-parseval` | `Burnett.Fourier.schwartz_parseval` | X02 |
| `fourier:fourier-modulate` | `Burnett.Fourier.fourier_modulate` | X02 |
| `x02:offnull:cutoff-gradient-identity` | `Burnett.CubicOffNull.cutoff_gradient_identity` | X02 |
| `x02:offnull:fCutoffErrorLp-tendsto-zero` | `Burnett.CubicOffNull.fCutoffErrorLp_tendsto_zero` | X02 |
| `x02:offnull:wCutoffErrorLp-tendsto-zero` | `Burnett.CubicOffNull.wCutoffErrorLp_tendsto_zero` | X02 |
| `x02:offnull:map-fCutoffErrorLp-tendsto-zero` | `Burnett.CubicOffNull.map_fCutoffErrorLp_tendsto_zero` | X02 |
| `x02:offnull:map-wCutoffErrorLp-tendsto-zero` | `Burnett.CubicOffNull.map_wCutoffErrorLp_tendsto_zero` | X02 |
| `x02:offnull:offNull-translated-fourier-energy-tendsto-zero` | `Burnett.CubicOffNull.offNull_translated_fourier_energy_tendsto_zero` | X02 |
| `x02:offnull:f-normalized-mode-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.f_normalized_mode_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:w-normalized-mode-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.w_normalized_mode_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:compact-fGradient-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.compact_fGradient_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:compact-wGradient-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.compact_wGradient_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:compact-fGradient-total-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.compact_fGradient_total_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:compact-wGradient-total-offNull-energy-tendsto-zero` | `Burnett.CubicOffNull.compact_wGradient_total_offNull_energy_tendsto_zero` | X02 |
| `x02:offnull:f-productGradient-map-difference-tendsto-zero` | `Burnett.CubicOffNull.f_productGradient_map_difference_tendsto_zero` | X02 |
| `x02:offnull:w-productGradient-map-difference-tendsto-zero` | `Burnett.CubicOffNull.w_productGradient_map_difference_tendsto_zero` | X02 |
