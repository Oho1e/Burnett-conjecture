# Second foundations batch: L² Fourier, connection differences, and positive-density kernels

2026-11-16; continued from reviewed first-batch candidate `d143c3709466bd2900e098c573c1691d987226da`, now user-merged as main `b4b27302556c62617798a46a22e744035fcd4602` with main CI passed. This document records the batch's mathematical explanation. Implementation, independent readback, machine checks, author confirmation, and merging into main are recorded separately; no whole-paper completion is declared. The source, trust policy A, and fixed dependencies are unchanged.

## Actual construction of L² Fourier

For any finite-dimensional real inner-product space V with its volume measure, `SchwartzDensity.lean` proves the actual map

```lean
DenseRange (fun f : SchwartzMap V ℂ => f.toLp 2 (volume : Measure V))
```

The proof first approximates in L² by continuous compactly supported functions, then approximates uniformly by smooth functions and multiplies by a fixed smooth compact cutoff equal to one on the original support. The error is controlled by the finite L² norm of that fixed cutoff. Neither finite whole-space volume nor density is assumed.

`L2Extension.lean` takes the linear subspace of actual L² consisting of Schwartz images, with its inherited L² norm. Proved Parseval gives a Fourier linear isometry on this subspace, extended continuously along the dense inclusion. Inverse Schwartz Fourier makes the extended range dense; the range of an isometry on complete L² is closed, giving surjectivity and the actual isometric equivalence

```lean
fourierL2Equiv : Lp ℂ 2 volume ≃ₗᵢ[ℂ] Lp ℂ 2 volume
```

On Schwartz inputs, both forward and inverse maps agree almost everywhere with the actual integral transforms, retaining the original `2π` normalization. The Schwartz Fréchet topology is not treated as the L² norm topology. Agreement with the integral for general arbitrary L¹∩L² inputs is not separately proved in this batch.

`Projection.lean` constructs an actual multiplication CLM from a bounded measurable frequency symbol m, then defines the physical-space F⁻¹mF operator and proves its L² bound and a frequency-support energy bound. `SharpProjection.lean` constructs actual sharp projections from measurable-set indicators, proving idempotence and orthogonality; a.e.-equal symbols give the same physical operator.

`OffNullProjection.lean` instantiates these operators for the same fSequence and wSequence at source line3193. For every fixed δ>0, every original real χ∈C∞c, and a fixed bounded measurable m supported only on the nonzero off-cone region Eδ, the four components satisfy the following positive Euclidean whole-space L² convergence:

\[
 A_m(\chi\nabla f_n),\quad A_m(\chi\nabla w_n),\quad
 A_m(\nabla(\chi f_n)),\quad A_m(\nabla(\chi w_n))\longrightarrow0.
\]

The actual main declaration is `Burnett.CubicOffNull.fixed_offNull_gradient_localization_away_zero`. Sharp-cone indicators and bounded symbols smooth away from zero have concrete instances. The zero-frequency singleton is removed by its zero volume and a.e. symbol equality. Physical inverse-transform outputs still use full-space L², without cutting off noncompact tails. χ, δ, and m are fixed before n→∞; no uniform conclusion for varying δ, sequence-dependent symbols, or general variable-coefficient PDOs is claimed. The two cutoff positions are connected by the actual product rule and small amplitude, without commuting the nonlocal projection with χ.

## The actual local connection difference for F04

`ConnectionDifference.lean` computes Christoffel coefficients from actual bilinear metrics and Fréchet derivatives of their coordinate components. For two metrics g₀/g₁, let h=g₁−g₀ and take background Γ(g₀). It actually proves

\[
\Gamma(g_1)^a{}_{bc}-\Gamma(g_0)^a{}_{bc}
=\frac12 g_1^{ad}
  (\nabla_bh_{cd}+\nabla_ch_{bd}-\nabla_dh_{bc}).
\]

The inverse matrix is constructed from a nondegenerate bilinear form; zero torsion and metric compatibility follow from the formula. The final pointwise theorem requires only nondegeneracy at the selected point, componentwise differentiability, and symmetry in a neighborhood. The open-chart version requires regularity on U, not nondegeneracy or smoothness on the whole coordinate space. Neighborhood equality does not change the first coordinate jet.

## The exact coordinate Ricci difference for F04

`CurvatureDifference.lean` computes the actual background covariant derivative of a tensor C with one upper and two lower indices. For two componentwise differentiable connection fields torsion-free at x, and C=Γ₁−Γ₀, it proves

\[
\operatorname{Ric}(\Gamma_1)_{bc}-\operatorname{Ric}(\Gamma_0)_{bc}
=\nabla_aC^a{}_{bc}-\nabla_cC^a{}_{ba}
 +C^a{}_{ae}C^e{}_{bc}-C^a{}_{ce}C^e{}_{ba}.
\]

Derivatives are actual Fréchet derivatives; the derivative of the connection difference is not independently assumed to have the desired form. When the Ricci array of Γ₁ vanishes, this gives the original exact vacuum identity with the same signs.

`CurvatureSymbolBridge.lean` additionally proves that inserting the rank-one jet `ξ⊗k` into the exact Christoffel construction yields old F06 `connectionSymbol`, while this section's `quadraticDifference` is exactly minus the old `quadraticSymbol` (the source's B). This minus sign must be retained when deriving weak Ricci moments from the exact identity; the quadratic definitions cannot simply be identified.

These are coordinate-connection identities. Instantiating both fields as point-varying Levi–Civita coefficients, deriving the required connection regularity from metric regularity, manifold naturality, Eₙ estimates, weak Ricci limits, and local H⁻¹ compactness remain later work. These two modules do not close all of F04.

## The positive-density to system-kernel bridge for F05

The finite-dimensional algebraic bridge in `PositiveKernel.lean` uses an actual Hermitian positive-semidefinite M and a compatible-size matrix A. It derives AM=0 from AM Aᴴ=0, then proves range(M)⊆ker(A) for actual linear maps. M may be singular and the system row index need not even be finite; examples with nonzero singular M and nonzero A were actually checked. This finite-dimensional step neither constructs a defect measure nor automatically proves a.e. vanishing of matrix compression.

See the [batch review record](second-foundations-review.en.md) and source bindings for independent readback and frozen versions. The original covariance tensor differs from an endomorphism matrix under an arbitrary Gram form; applications must still supply the correct positive Hermitian representation.

## Dense-test extension tools for F05

For an actual sequence of CLMs uₙ:E→L[ℝ]ℝ, `DenseTests.lean` consumes an explicit uniform operator-norm bound ‖uₙ‖≤C and pointwise convergence on a dense D. It first proves the values at each x are Cauchy, then constructs the actual unique continuous linear limit L, proving pointwise convergence on all E and ‖L‖≤C. E need not be complete, and convergence of uₙ in operator norm is not asserted.

A further theorem derives L(x)≥0 from an explicit error errₙ(x)→0 and eventual lower bound −errₙ(x)≤uₙ(x). Whether original PDOs satisfy these bounds, whether the chosen test norm is correct, and whether Gårding/square-decomposition errors vanish must be proved by actual consumers. This tool does not replace finite-order symbol-derivative bounds with a C⁰ bound or construct a defect measure. See the [second extension investigation](../formalization/dependency-audit-round2.en.md) for the next interface.

## Shared scope boundaries

This batch supplies actual F04/F05/X02 proof dependencies, not a proof of quadratic defect measures, transport, or the main theorem. Author confirmation of the new explanations has not been recorded; earlier local F06/X02 delegation carries over only within its original scope. The whole paper remains `development`, `verified=false`.
