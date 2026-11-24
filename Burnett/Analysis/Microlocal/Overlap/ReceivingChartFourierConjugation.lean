import Burnett.Analysis.Microlocal.Overlap.ReceivingChartKernelGeometry
import Burnett.Analysis.Microlocal.Overlap.FrozenShellSymbol
import Burnett.Analysis.Microlocal.Overlap.KernelRemainder

/-! Actual kernel change of variables and frozen inverse-adjoint symbol
for arbitrary compatible fixed charts. -/

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open MeasureTheory Set Burnett.Fourier
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel Burnett.Microlocal.OverlapGradient
open Burnett.Geometry.MaximalChart (AtlasChart chartTransition_fderiv_leftInverse)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

private theorem chartTransition_symm_eq (c d : AtlasChart M) :
    (c.transition d).symm = d.transition c := by
  simp only [AtlasChart.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]

private theorem reverse_overlap_source (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) :
    c.transition d x ∈ (d.transition c).source := by
  rw [← chartTransition_symm_eq c d]
  exact (c.transition d).mapsTo hx

theorem overlapTransition_reverse_apply (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) :
    overlapTransition d c (c.transition d x) = x := by
  rw [overlapTransition_eq d c (reverse_overlap_source c d hx), ← chartTransition_symm_eq c d]
  exact (c.transition d).left_inv hx

theorem overlapJacobianWeight_sq_on_source (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) :
    (overlapJacobianWeight c d x)^2 = |(fderiv ℝ (c.transition d) x).det| := by
  rw [overlapJacobianWeight_eq c d hx, Real.sq_sqrt (abs_nonneg _)]

/-- Transport on one source window, with zero extension off its actual
image in the target chart. -/
def transportedHalfDensity (c d : AtlasChart M) (S : Set E) (f : E → ℂ) : E → ℂ :=
  ((c.transition d) '' S).indicator
    (fun z => overlapJacobianWeight d c z • f (overlapTransition d c z))


private theorem overlapTransition_det_mul_reverse (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) :
    (fderiv ℝ (d.transition c) (c.transition d x)).det *
      (fderiv ℝ (c.transition d) x).det = 1 := by
  let e := c.transition d
  have hL : (fderiv ℝ (d.transition c) (e x)).toLinearMap.comp (fderiv ℝ e x).toLinearMap =
      LinearMap.id :=
    congrArg ContinuousLinearMap.toLinearMap (chartTransition_fderiv_leftInverse c d hx)
  have hDet := congrArg LinearMap.det hL
  rwa [LinearMap.det_comp, LinearMap.det_id] at hDet

theorem overlapTransition_fderiv_det_ne_zero (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) :
    (fderiv ℝ (overlapTransition c d) x).det ≠ 0 := by
  rw [overlapTransition_fderiv c d hx]
  intro h
  have hd := overlapTransition_det_mul_reverse c d hx
  rw [h, mul_zero] at hd
  exact zero_ne_one hd

theorem overlapJacobianWeight_inverse_mul (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) :
    overlapJacobianWeight c d x * overlapJacobianWeight d c (c.transition d x) = 1 := by
  rw [overlapJacobianWeight_eq c d hx, overlapJacobianWeight_eq d c (reverse_overlap_source c d hx),
    mul_comm, ← Real.sqrt_mul (abs_nonneg _), ← abs_mul,
    overlapTransition_det_mul_reverse c d hx, abs_one, Real.sqrt_one]

theorem overlapJacobianWeight_continuousOn (c d : AtlasChart M) :
    ContinuousOn (overlapJacobianWeight c d) (c.transition d).source := by
  have hD : ContDiffOn ℝ 0 (fderiv ℝ (overlapTransition c d))
      (c.transition d).source :=
    (overlapTransition_contDiffOn c d).fderiv_of_isOpen (c.transition d).open_source (by simp)
  unfold overlapJacobianWeight
  exact (Real.continuous_sqrt.comp continuous_abs).comp_continuousOn
    (ContinuousLinearMap.continuous_det.comp_continuousOn hD.continuousOn)

theorem integrable_transportedHalfDensity (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) {f : E → ℂ} (hf : Continuous f) :
    Integrable (transportedHalfDensity c d K f) := by
  let U := c.transition d '' K
  let V := (d.transition c).source
  have hU : IsCompact U := hK.image_of_continuousOn ((c.transition d).continuousOn.mono hKU)
  have hUV : U ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact reverse_overlap_source c d (hKU hz)
  have hΦ : ContDiffOn ℝ ∞ (overlapTransition d c) V := overlapTransition_contDiffOn d c
  have hLoc : ContinuousOn
      (fun z => overlapJacobianWeight d c z • f (overlapTransition d c z)) U :=
    ((overlapJacobianWeight_continuousOn d c).mono hUV).smul
      (hf.comp_continuousOn (hΦ.continuousOn.mono hUV))
  exact (hLoc.integrableOn_compact hU).integrable_indicator hU.measurableSet

/-- Change variables in the target convolution pairing. One inverse
half-density cancels one of the two forward factors in the Jacobian. -/
theorem overlap_halfDensityKernel_changeVariables
    (c d : AtlasChart M) (S : Set E) (hS : MeasurableSet S)
    (hSU : S ⊆ (c.transition d).source) (k f : E → ℂ) (x : E) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    w x • (∫ z in c.transition d '' S, k (Φ x - z) *
      (overlapJacobianWeight d c z • f (overlapTransition d c z))) =
      ∫ y in S, ((w x * w y) • k (Φ x - Φ y)) * f y := by
  intro Φ w
  let e := c.transition d
  let g (z : E) := k (Φ x - z) * (overlapJacobianWeight d c z • f (overlapTransition d c z))
  have hD (y : E) (hy : y ∈ S) : HasFDerivWithinAt e (fderiv ℝ e y) S y :=
    ((((c.smooth_transition d).differentiableOn (by simp)) y (hSU hy)).differentiableAt
      (e.open_source.mem_nhds (hSU hy))).hasFDerivAt.hasFDerivWithinAt
  change w x • (∫ z in e '' S, g z) = _
  rw [integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure E) hS hD
    (e.injOn.mono hSU) g, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) hS] with y hy
  have hy' := hSU hy
  have hΦ : Φ y = e y := overlapTransition_eq c d hy'
  rw [hΦ]
  unfold g
  rw [overlapTransition_reverse_apply c d hy', ← overlapJacobianWeight_sq_on_source c d hy']
  have hW : w y * overlapJacobianWeight d c (e y) = 1 :=
    overlapJacobianWeight_inverse_mul c d hy'
  have hWeights : (w x * (w y)^2) * overlapJacobianWeight d c (e y) = w x * w y := by
    calc
      _ = (w x * w y) * (w y * overlapJacobianWeight d c (e y)) := by ring
      _ = _ := by rw [hW, mul_one]
  change w x • ((w y)^2 • (k (Φ x-e y) * (overlapJacobianWeight d c (e y) • f y))) = _
  rw [mul_smul_comm, smul_smul, smul_smul, hWeights, smul_mul_assoc]

/-- With zero extension of the transported input, the full target
convolution pulls back to an integral over the source window. -/
theorem overlap_kernel_conjugation
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (k f : E → ℂ) (x : E) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    w x • (∫ z, k (Φ x - z) * transportedHalfDensity c d K f z) =
      ∫ y in K, ((w x * w y) • k (Φ x - Φ y)) * f y := by
  intro Φ w
  let U := c.transition d '' K
  have hU : MeasurableSet U := (hK.image_of_continuousOn
    ((c.transition d).continuousOn.mono hKU)).measurableSet
  let g (z : E) := k (Φ x-z) * (overlapJacobianWeight d c z • f (overlapTransition d c z))
  have he : (fun z => k (Φ x-z) * transportedHalfDensity c d K f z) = U.indicator g := by
    funext z
    by_cases hz : z ∈ U
    · simp only [transportedHalfDensity, U, g, Set.indicator_of_mem hz]
    · simp only [transportedHalfDensity, U, g, Set.indicator_of_notMem hz, mul_zero]
  rw [he, integral_indicator hU]
  exact overlap_halfDensityKernel_changeVariables c d K hK.measurableSet hKU k f x

/-- The full target convolution of the actual inverse Fourier shell,
pulled back to the source. -/
theorem overlap_shellKernel_conjugation
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (j : ℕ) (f : E → ℂ) (x : E) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let k := shellKernel m hm j
    w x • (∫ z, k (Φ x - z) * transportedHalfDensity c d K f z) =
      ∫ y in K, ((w x * w y) • k (Φ x - Φ y)) * f y :=
  overlap_kernel_conjugation c d K hK hKU (shellKernel m hm j) f x

end Burnett.Microlocal.AtlasOverlapKernel

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.CapFourier
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel Burnett.Microlocal.OverlapGradient
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ContDiff FourierTransform Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The invertible chart derivative at the output point of the kernel. -/
def frozenChartDerivative (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) : E ≃L[ℝ] E :=
  (fderiv ℝ (overlapTransition c d) x).toContinuousLinearEquivOfDetNeZero
    (overlapTransition_fderiv_det_ne_zero c d hx)

/-- The frequency transformation associated to the same frozen
spatial derivative. -/
def frozenChartFrequency (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) : E ≃L[ℝ] E :=
  (physicalDualEquiv (frozenChartDerivative c d hx)).symm

theorem frozenChartFrequency_inverse_adjoint (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) (ξ : E) :
    (fderiv ℝ (overlapTransition c d) x).adjoint (frozenChartFrequency c d hx ξ) = ξ := by
  let A := frozenChartDerivative c d hx
  have hA : A.toContinuousLinearMap = fderiv ℝ (overlapTransition c d) x :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  rw [← hA, ← physicalDualEquiv_apply]
  exact (physicalDualEquiv A).apply_symm_apply ξ

theorem inverseFourier_frozenChartFrequency (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) (p : E → ℂ) (z : E) :
    (𝓕⁻ (p ∘ frozenChartFrequency c d hx)) z =
      (overlapJacobianWeight c d x)^2 •
        (𝓕⁻ p) (fderiv ℝ (overlapTransition c d) x z) := by
  let A := frozenChartDerivative c d hx
  have hA : A.toContinuousLinearMap = fderiv ℝ (overlapTransition c d) x :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  have hJ : linearJacobian A = (overlapJacobianWeight c d x)^2 := by
    rw [linearJacobian, hA, overlapTransition_fderiv c d hx, overlapJacobianWeight_sq_on_source c d hx]
  change (𝓕⁻ (p ∘ (physicalDualEquiv A).symm)) z = _
  rw [Burnett.Microlocal.OverlapKernel.inverseFourier_comp_inverseAdjoint, hJ]
  rfl

/-- The actual annular shell uses the inverse adjoint on its full
frequency symbol, including its radial cutoff. -/
theorem overlap_frozen_shellKernel_symbol (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) (z : E) :
    (overlapJacobianWeight c d x)^2 •
        shellKernel m hm j (fderiv ℝ (overlapTransition c d) x z) =
      (𝓕⁻ (fun ξ => annularSymbol m ((dyadicScale j)⁻¹ • frozenChartFrequency c d hx ξ))) z := by
  rw [shellKernel_eq_inverseFourier]
  exact (inverseFourier_frozenChartFrequency c d hx
    (fun ξ => annularSymbol m ((dyadicScale j)⁻¹ • ξ)) z).symm

/-- The same exact identity holds for the finite partial angular multiplier
at every cutoff index. -/
theorem overlap_frozen_partialAngularKernel_symbol (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (z : E) :
    (overlapJacobianWeight c d x)^2 •
        partialAngularKernel m hm N (fderiv ℝ (overlapTransition c d) x z) =
      (𝓕⁻ (fun ξ => partialAngularSymbol m N (frozenChartFrequency c d hx ξ))) z := by
  unfold partialAngularKernel
  rw [← inverseFourier_partialAngular_eq_sum m hm hd]
  exact (inverseFourier_frozenChartFrequency c d hx (partialAngularSymbol m N) z).symm

end Burnett.Microlocal.AtlasOverlapKernel

set_option autoImplicit false
set_option maxHeartbeats 1100000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.CapFourier (pullbackSchwartz pullbackSchwartz_apply)
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel Burnett.Microlocal.OverlapGradient
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.OverlapKernel (halfDensityKernelDifference)
open scoped BigOperators ContDiff FourierTransform Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The conjugation formula for an actual Fourier product on the
compact-window transported input. -/
theorem overlap_fourier_kernel_conjugation
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (p f : E → ℂ) (hp : Integrable p) (hf : Continuous f) (x : E) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let g := transportedHalfDensity c d K f
    w x • (𝓕⁻ (fun ξ => p ξ * (𝓕 g) ξ)) (Φ x) =
      ∫ y in K, ((w x * w y) • (𝓕⁻ p) (Φ x - Φ y)) * f y := by
  intro Φ w g
  rw [inverseFourier_mul_fourier_eq_convolution p g hp
    (integrable_transportedHalfDensity c d K hK hKU hf)]
  exact overlap_kernel_conjugation c d K hK hKU (𝓕⁻ p) f x

/-- The actual finite angular Fourier action on the target field, pulled
back to the source window at the same finite cutoff index. -/
theorem overlap_partialAngularFourier_conjugation
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (f : E → ℂ) (hf : Continuous f) (x : E) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let g := transportedHalfDensity c d K f
    w x • (𝓕⁻ (fun ξ => partialAngularSymbol m N ξ * (𝓕 g) ξ)) (Φ x) =
      ∫ y in K, ((w x * w y) • partialAngularKernel m hm N (Φ x - Φ y)) * f y := by
  have hp : Integrable (partialAngularSymbol m N : E → ℂ) := by
    rw [← show (partialAngularSchwartz m hm N : E → ℂ) = (partialAngularSymbol m N : E → ℂ) from
      funext (partialAngularSchwartz_apply m hm hd N)]
    exact (partialAngularSchwartz m hm N).integrable
  simpa only [inverseFourier_partialAngular_eq_sum m hm hd, partialAngularKernel] using
    overlap_fourier_kernel_conjugation c d K hK hKU (partialAngularSymbol m N) f hp hf x

/-- The variable frequency transform is held fixed at the output point
when evaluating its Fourier action on the source-window field. -/
theorem overlap_frozen_partialAngular_convolution
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) {x : E} (hx : x ∈ (c.transition d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (f : E → ℂ) (hf : Continuous f) :
    let p (ξ : E) := partialAngularSymbol m N (frozenChartFrequency c d hx ξ)
    let A := fderiv ℝ (overlapTransition c d) x
    let w := overlapJacobianWeight c d
    (𝓕⁻ (fun ξ => p ξ * (𝓕 (K.indicator f)) ξ)) x =
      ∫ y in K, ((w x)^2 • partialAngularKernel m hm N (A (x-y))) * f y := by
  intro p A w
  let p₀ := pullbackSchwartz (frozenChartFrequency c d hx) (partialAngularSchwartz m hm N)
  have hep : (p₀ : E → ℂ) = p := by
    funext ξ
    rw [pullbackSchwartz_apply]
    exact partialAngularSchwartz_apply m hm hd N _
  have hp : Integrable p := hep ▸ p₀.integrable
  have hfi : Integrable (K.indicator f) :=
    (hf.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  rw [inverseFourier_mul_fourier_eq_convolution p (K.indicator f) hp hfi]
  have hCut :
      (fun y => (𝓕⁻ p) (x-y) * K.indicator f y) =
        K.indicator (fun y => (𝓕⁻ p) (x-y) * f y) := by
    funext y
    by_cases hy : y ∈ K
    · simp only [indicator_of_mem hy]
    · simp only [indicator_of_notMem hy, mul_zero]
  rw [hCut, integral_indicator hK.measurableSet]
  apply integral_congr_ae
  filter_upwards with y
  rw [← overlap_frozen_partialAngularKernel_symbol c d hx m hm hd N (x-y)]

theorem overlap_partialAngularFourier_difference
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    {x : E} (hx : x ∈ (c.transition d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (f : E → ℂ) (hf : Continuous f) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let g := transportedHalfDensity c d K f
    w x • (𝓕⁻ (fun ξ => partialAngularSymbol m N ξ * (𝓕 g) ξ)) (Φ x) -
      (𝓕⁻ (fun ξ => partialAngularSymbol m N (frozenChartFrequency c d hx ξ) *
        (𝓕 (K.indicator f)) ξ)) x =
      ∫ y in K, halfDensityKernelDifference Φ w (partialAngularKernel m hm N) x y * f y := by
  intro Φ w g
  let k := partialAngularKernel m hm N
  let A := fderiv ℝ Φ x
  have hk : Continuous k :=
    continuous_iff_continuousAt.mpr fun z => (partialAngularKernel_hasFDerivAt m hm N z).continuousAt
  have hΦ : ContinuousOn Φ K := (overlapTransition_contDiffOn c d).continuousOn.mono hKU
  have hw : ContinuousOn w K := (overlapJacobianWeight_continuousOn c d).mono hKU
  have h₁ : ContinuousOn (fun y => ((w x * w y) • k (Φ x - Φ y)) * f y) K :=
    ((continuousOn_const.mul hw).smul
      (hk.comp_continuousOn (continuousOn_const.sub hΦ))).mul hf.continuousOn
  have h₂ : Continuous (fun y => ((w x)^2 • k (A (x-y))) * f y) :=
    (continuous_const.smul (hk.comp (A.continuous.comp (continuous_const.sub continuous_id)))).mul hf
  rw [overlap_partialAngularFourier_conjugation c d K hK hKU m hm hd N f hf x,
    overlap_frozen_partialAngular_convolution c d K hK hx m hm hd N f hf,
    ← integral_sub (h₁.integrableOn_compact hK) (h₂.continuousOn.integrableOn_compact hK)]
  simp only [halfDensityKernelDifference, sub_mul, A, k]

/-- On the compact output window the difference is exactly the finite
sum of the product-window-localized single-shell differences. -/
theorem overlap_partialAngularFourier_difference_localized
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    {x : E} (hx : x ∈ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (f : E → ℂ) (hf : Continuous f) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let g := transportedHalfDensity c d K f
    w x • (𝓕⁻ (fun ξ => partialAngularSymbol m N ξ * (𝓕 g) ξ)) (Φ x) -
      (𝓕⁻ (fun ξ => partialAngularSymbol m N (frozenChartFrequency c d (hKU hx) ξ) *
        (𝓕 (K.indicator f)) ξ)) x =
      ∫ y, (∑ j ∈ Finset.range N, (K ×ˢ K).indicator
        (fun Pair => halfDensityKernelDifference Φ w (shellKernel m hm j) Pair.1 Pair.2)
        (x, y)) * f y := by
  intro Φ w g
  let R (y : E) := halfDensityKernelDifference Φ w (partialAngularKernel m hm N) x y * f y
  rw [overlap_partialAngularFourier_difference c d K hK hKU (hKU hx) m hm hd N f hf]
  rw [← integral_indicator hK.measurableSet]
  apply integral_congr_ae
  filter_upwards with y
  change K.indicator R y = _
  by_cases hy : y ∈ K
  · simp only [indicator_of_mem hy, indicator_of_mem (show (x,y) ∈ K ×ˢ K from ⟨hx, hy⟩),
      R, halfDensityKernelDifference, partialAngularKernel, Finset.smul_sum, Finset.sum_sub_distrib]
  · have hy' : (x,y) ∉ K ×ˢ K := fun h => hy h.2
    simp only [indicator_of_notMem hy, indicator_of_notMem hy', Finset.sum_const_zero, zero_mul]

/-- The same finite difference as a sum of the individual shell actions,
in the order needed for the corresponding finite sum of L² elements. -/
theorem overlap_partialAngularFourier_difference_sum_actions
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    {x : E} (hx : x ∈ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (f : E → ℂ) (hf : Continuous f) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let g := transportedHalfDensity c d K f
    w x • (𝓕⁻ (fun ξ => partialAngularSymbol m N ξ * (𝓕 g) ξ)) (Φ x) -
      (𝓕⁻ (fun ξ => partialAngularSymbol m N (frozenChartFrequency c d (hKU hx) ξ) *
        (𝓕 (K.indicator f)) ξ)) x =
      ∑ j ∈ Finset.range N, ∫ y, (K ×ˢ K).indicator
        (fun p => halfDensityKernelDifference Φ w (shellKernel m hm j) p.1 p.2)
        (x, y) * f y := by
  intro Φ w g
  rw [overlap_partialAngularFourier_difference_localized c d K hK hKU hx m hm hd N f hf]
  simp only [Finset.sum_mul]
  apply integral_finset_sum
  intro j _
  let k := shellKernel m hm j
  let A := fderiv ℝ Φ x
  let H (y : E) := halfDensityKernelDifference Φ w k x y * f y
  have hk : Continuous k :=
    continuous_iff_continuousAt.mpr fun z => (shellKernel_hasFDerivAt m hm j z).continuousAt
  have hΦ : ContinuousOn Φ K := (overlapTransition_contDiffOn c d).continuousOn.mono hKU
  have hw : ContinuousOn w K := (overlapJacobianWeight_continuousOn c d).mono hKU
  have hActual : ContinuousOn (fun y => (w x * w y) • k (Φ x - Φ y)) K :=
    (continuousOn_const.mul hw).smul (hk.comp_continuousOn (continuousOn_const.sub hΦ))
  have hFrozen : Continuous (fun y => (w x)^2 • k (A (x-y))) :=
    continuous_const.smul (hk.comp (A.continuous.comp (continuous_const.sub continuous_id)))
  have hH : ContinuousOn H K := (hActual.sub hFrozen.continuousOn).mul hf.continuousOn
  have hCut : (fun y => (K ×ˢ K).indicator
      (fun p => halfDensityKernelDifference Φ w k p.1 p.2) (x,y) * f y) = K.indicator H := by
    funext y
    by_cases hy : y ∈ K
    · simp only [indicator_of_mem hy, indicator_of_mem (show (x,y) ∈ K ×ˢ K from ⟨hx, hy⟩), H]
    · have hy' : (x,y) ∉ K ×ˢ K := fun h => hy h.2
      simp only [indicator_of_notMem hy, indicator_of_notMem hy', zero_mul]
  change Integrable (fun y => (K ×ˢ K).indicator
    (fun p => halfDensityKernelDifference Φ w k p.1 p.2) (x,y) * f y)
  rw [hCut]
  exact (hH.integrableOn_compact hK).integrable_indicator hK.measurableSet

end Burnett.Microlocal.AtlasOverlapKernel
