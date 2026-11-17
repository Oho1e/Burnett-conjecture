# Intrinsic Dh, the physical three-tensor norm, and coordinate control from the original assumptions

This batch supports the geometry and local estimates at source lines 333–369; it does not close `thm:quadratic`, F04/F05, or the whole paper. The article and trust policy A remain locked. Sources, all declarations, and independent-review identities are in the [bindings](intrinsic-dh-geometry-source-bindings.json) and [review](intrinsic-dh-geometry-review.en.md). Author confirmation of the new explanation has not been recorded. A complete Lorentz/time-orientation/vacuum-data wrapper remains to be instantiated by later consumers.

## The actual induced derivative and chart independence

For the original smooth four-manifold, auxiliary Riemannian metric r, and smooth bilinear Hom-bundle section H, the proved global connection constructs

    (∇ʳH)(V,U,W) = V[H(U,W)] − H(∇ʳ_VU,W) − H(U,∇ʳ_VW).

The scalar derivative actually uses mfderiv. U/W, which are differentiated, are smooth; only the point value of V is needed. H need not be symmetric. The construction gives an actual continuous trilinear tensor on the tangent fiber. Between arbitrary preferred charts, two Hessian terms in the actual Jacobian/Hessian transformation cancel; expansion in bases of all three slots then proves chart independence for all fiber vectors. There is no global smooth-frame assumption, nor an unproved global smooth extension used in place of an arbitrary point vector.

For the same r and H=gₙ−g₀, evaluation of the tensor on three actual frame basis vectors in any preferred chart containing the point agrees exactly with the existing `auxiliaryPerturbationJet(r,g₀,gₙ)`. The first slot is the differentiation direction and the other two are the bilinear-tensor slots; raw partial and covariant derivatives are kept distinct throughout.

## Physical length and the original local L∞ assumption

The physical length uses the full ordered contraction with the actual inverse r:

    |T|²_r = Σ r^{ia} r^{jb} r^{kc} T_ijk T_abc.

It is independent of the preferred chart, equals the Hilbert norm of an actual 64-dimensional positive-definite Gram space, and vanishes exactly when T=0. It differs from the operator norm of a continuous trilinear map; the original tangent-space Norm instance is unchanged. For fixed r, chart, and compact K within the target, one common A>0 controls component sup≤A|T|r for every T, independently of T and n.

Using the actual inverse r, connection, and first jet of H, the proof establishes that `normScalar r H=|∇ʳH|r` is continuous and Borel measurable on all M. It does not require prior higher smoothness of the full tensor-bundle section or claim differentiability of the length at zero.

The original assumption is explicitly expanded as follows: for every compact S⊂M there is a finite D_S≥0 such that, for every n and under the same background geometric volume μ₀=dV_g₀, `eLpNorm(normScalar r(gₙ−g₀),∞,μ₀|S)≤ofReal D_S`. Smooth nondegeneracy of g₀ gives genuine positivity of μ₀ on open sets.

For compact K in a fixed chart, first take its actual compact inverse-chart image J, then construct a common compact S with J⊂interior S, before considering all n. Continuity upgrades the a.e. bound on the larger μ₀|S to a pointwise bound on J, yielding a uniform auxiliary coordinate-jet bound. No pointwise bound is inferred from an a.e. bound on K itself, which may have measure zero. The same S, D_S, and comparison constant work for all n.

## The actual connection-error consumer of the original assumptions

The original r-physical C⁰loc convergence and the Dh bound, with the fixed Γ(r)·H correction, give an eventual uniform bound on raw coordinate ∂H. The actual connection error is

    Eₙ = Γ(gₙ) − Γ(g₀) − Christoffel(g₀⁻¹, D^{g₀}(gₙ−g₀)).

The linear term uses the background g₀ connection, rather than auxiliary r or raw partial derivatives. Actual smooth, symmetric, nondegenerate fields and the existing connection-difference identity give uniform convergence of Eₙ to zero on every fixed chart compact set. For every n, a MemLp∞ representative under the actual coordinate measure of the same g₀ is constructed internally, and its toLp norm tends to zero. Raw-jet bounds, MemLp, and convergence of E are not extra caller assumptions.

The four modules retain all 64 declarations and register 16 semantic consumers; auxiliary definitions and rearrangements are included in the complete source/type/axiom review. The production modules are `IntrinsicCov2`, `ManifoldCov3Norm`, `IntrinsicDhMeasure`, and `OriginalAdmissibleLocalControl`.

The subsequent [local weak derivatives](local-weak-derivative.en.md) and [connection-error tests](local-weak-ricci.en.md) consume these actual objects. A complete global mixed-E physical model, all quantitative eq:E bounds, the full weak Ricci identity, H⁻¹ compactness, and phase-space defect measures still require their actual consumers. This batch does not require an extra uniform D²gₙ assumption, a general bundle-Lp isomorphism, or a global frame.
