# Actual manifold charts, tensor norms, and geometric coordinate volume

This batch continues necessary dependencies at source lines 91–105, 333–340, and 352–389. The macro at source line 34 and line 337 explicitly give `dV=dV_g=√|det g| dx`; `|·|r` is the tensor length induced by the auxiliary positive-definite metric. They are modeled separately: Lorentz g cannot be substituted into the earlier positive-definite density `√det R`. These are support results, not closure of F04 or `thm:quadratic`; new human mathematical confirmation remains pending.

## Tensor length and the actual error

`MixedTensorNorm` actually defines, for an array E with one upper and two lower indices,

\[
 |E|_r^2=\sum_{a,b,c,d,e,f}R_{ad}(R^{-1})_{be}(R^{-1})_{cf}
 E^a{}_{bc}E^d{}_{ef}.
\]

The Gram matrix is `(R⊗R⁻¹)⊗R⁻¹`; its positive definiteness, inverse, correspondence with an actual Hilbert norm, continuity for variable coefficients, and two-way compact-set comparison are proved. Comparison constants are derived from continuity and compactness of actual R, R⁻¹, and finite contraction coefficients, rather than assumed norm-equivalence fields. For R=4I a pure component has this norm 1/2, whereas its fully covariant order-three norm is 1/8; these must not be confused.

`TensorCoordinateChange` actually constructs `Rnew=AᵀRA` for invertible A (old rows/new columns), pulls back all slots of covariant two- and three-tensors, and proves exact invariance of energy and norm2/norm3. The actual Kronecker, flattening, inverse cancellations, and general Gram identities are proved internally. T here is covariant: raw partial derivatives are not simply treated as tensors under nonlinear chart changes, and a Hom operator norm does not replace the Hilbert tensor length.

`MixedConnectionError` connects uniform vanishing of the existing actual connection error E to the physical (1,2) norm, constructs an actual scalar `|E|r` Lp∞ element for the restricted measure, and proves norm convergence to zero. It does not assume an unconstructed bundle-valued normed Lp space. `LorentzConnectionError` further uses the fixed background g₀ volume `√|det g₀| dx`. Nondegeneracy of g₀ on U implies nonzero density through actual BilinForm.toMatrix. The local physical Dʳh bound, E conclusion, and actual Lp elements all use the same g₀ measure, independent of n.

## From the genuine tangent bundle to one chart

`ManifoldMetric` takes an actual smooth four-manifold and mathlib's `Bundle.ContMDiffRiemannianMetric`. The model/metric abbrevs are also checked. `tangentFrame` uses the inverse linear map of the preferred tangent-bundle trivialization, with base point given by the same `chart.symm`; it does not misuse definitional equality of TangentSpace and model space as an identity map. It is proved equal to the actual inverse-chart mfderivWithin.

Evaluation of r.inner on two frame vectors is an actual smooth scalar section. Composition with the actual inverse chart gives ContDiffOn∞ coordinate components on chart.target and a C1 interface. Injectivity comes from an actual continuous linear equivalence, so positive definiteness, symmetry, and nondegeneracy are also derived in the actual chart. No toCore/RiemannianBundle instance is registered to reselect existing norms, and no nondegeneracy or smoothness of the total extension outside the domain is required. `ManifoldConnectionError` actually consumes these chart data for r, eliminating separate C1 and PosDef premises for r; its g₀/gₙ and physical-derivative assumptions remain explicitly coordinate data.

## Two charts for the same field

`ManifoldMetricTransition` sets φ to the actual `chart_c.symm.trans chart_d`. The actual tangent-bundle cocycle gives frame_c=frame_d∘Dφ; identifying the same base point then proves, for any actual continuous fiber-bilinear field B,

\[
 G_c(x)=A(x)^T G_d(\phi(x))A(x),\qquad A=D\phi.
\]

B need not be positive definite, symmetric, or smooth in the base variable; these are pointwise algebraic identities. The matrix law is proved with the actual canonical basis and BilinForm.toMatrix_comp, rather than assumed. r.inner is an actual instance, giving two-chart measure compatibility for the same r.

`ChartVolume` derives the Jacobian formula for the positive-definite auxiliary density from actual matrix pullback, then proves pushforward with actual HasFDerivWithinAt, InjOn, and restricted measures. C1 for the actual-chart version comes from the atlas. Its computed-pullback version has no hR premise; consumers for arbitrary existing R/S still explicitly need the proved tensor relation, and those cases must not be conflated.

`LorentzVolume` independently defines the actual `√|det G|` density, local measurability and nonvanishing, a.e.-filter and ∞-seminorm transport, and the corresponding Jacobian pushforward. `ManifoldLorentzVolume` applies the proved same-B matrix law to the absolute-determinant density, proving `φ_*(μc|source)=μd|target` on an actual chart overlap without positive-definite B or assumed density/measure identities. Thus this batch includes **local** chart compatibility for the original dV_g, rather than only auxiliary r.

## Precise remaining tasks

Global geometric volume on M and its chart pushforward identification are not yet constructed; local compatibility does not automatically supply them. Naturality of the original intrinsic Levi-Civita D with computedΓ, and full instantiation of the original global Lorentz g₀/gₙ and C⁰/derivative assumptions in the present coordinate interface, also remain unfinished. D=∇r has not been renamed as a raw jet, nor has the current local consumer been called closure of the original admissibility assumptions.

Next are fixed-test integration by parts, weak Ricci identification, H⁻¹ compactness, and actual F05 PDO/positivity/common-measure constructions. The exact quadratic-correction sign, minus the old B, is retained. No uniform D²gₙ bound or global smooth frame is added. See the [source bindings](chart-geometry-source-bindings.json) for actual versions and registered targets, and the [review](chart-geometry-review.en.md) for independent readback and roles. Whole-paper verified remains false.
