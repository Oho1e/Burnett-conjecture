import Burnett.Analysis.Microlocal.Overlap.ReceivingChartFourierConjugation
import Burnett.Geometry.MetricJetNaturality

/-! The exact smooth half-density transport and pairing on one fixed-chart window. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.MetricJetNaturality (derivativeMatrix_apply)
open Burnett.Geometry.SmoothMetricConnection (contDiffOn_det)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.OverlapGradient
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- A source field supported in the compact window is transported smoothly
across its target support boundary and has the indicated compact support. -/
theorem transportedHalfDensity_smooth_compact_support
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (f : SchwartzMap E ℂ) (hfS : tsupport (f : E → ℂ) ⊆ K) :
    ContDiff ℝ ∞ (transportedHalfDensity c d K f) ∧
      HasCompactSupport (transportedHalfDensity c d K f) ∧
      tsupport (transportedHalfDensity c d K f) ⊆ c.transition d '' K := by
  let e := c.transition d
  let U := e '' K
  let F := transportedHalfDensity c d K f
  let g (z : E) := overlapJacobianWeight d c z • f (overlapTransition d c z)
  have hU : IsCompact U := hK.image_of_continuousOn (e.continuousOn.mono hKU)
  have hUT : U ⊆ e.target := image_subset_iff.mpr (e.mapsTo.mono_left hKU)
  have hF : tsupport F ⊆ U := by
    apply closure_minimal _ hU.isClosed
    intro z hz
    by_contra hn
    exact hz (Set.indicator_of_notMem hn g)
  have hsymm : e.symm = d.transition c := by
    simp only [e, AtlasChart.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hV : e.target = (d.transition c).source := by
    change e.symm.source = _
    rw [hsymm]
  have hLocal : ContDiffOn ℝ ∞ F e.target := by
    have hg : ContDiffOn ℝ ∞ g (d.transition c).source :=
      (overlapJacobianWeight_contDiffOn d c).smul
        (f.smooth'.comp_contDiffOn (overlapTransition_contDiffOn d c))
    rw [hV]
    refine hg.congr ?_
    intro z hz
    by_cases hzu : z ∈ U
    · exact Set.indicator_of_mem hzu g
    · have hzt : z ∈ e.target := hV.symm ▸ hz
      have hInv : overlapTransition d c z = e.symm z := overlapTransition_eq d c hz |>.trans
        (congrArg (fun a : OpenPartialHomeomorph E E => a z) hsymm.symm)
      have hOutside : e.symm z ∉ K := fun hzK => hzu ⟨e.symm z, hzK, e.right_inv hzt⟩
      have hZero : f (e.symm z) = 0 := image_eq_zero_of_notMem_tsupport
        (fun h : e.symm z ∈ tsupport (f : E → ℂ) => hOutside (hfS h))
      change U.indicator g z = _
      rw [Set.indicator_of_notMem hzu]
      simp only [g, hInv, hZero, smul_zero]
  have hSmooth : ContDiff ℝ ∞ F := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ e.target
    · exact hLocal.contDiffAt (e.open_target.mem_nhds hz)
    · have hOff : z ∉ tsupport F := fun h => hz (hUT (hF h))
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℂ)) z).congr_of_eventuallyEq
      exact notMem_tsupport_iff_eventuallyEq.mp hOff
  exact ⟨hSmooth, hU.of_isClosed_subset isClosed_closure hF, hF⟩

/-- A Schwartz witness for exactly the zero-extended transported field. -/
def transportedHalfDensitySchwartz
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (f : SchwartzMap E ℂ) (hfS : tsupport (f : E → ℂ) ⊆ K) : SchwartzMap E ℂ :=
  let h := transportedHalfDensity_smooth_compact_support c d K hK hKU f hfS
  h.2.1.toSchwartzMap h.1

@[simp]
theorem coe_transportedHalfDensitySchwartz
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (f : SchwartzMap E ℂ) (hfS : tsupport (f : E → ℂ) ⊆ K) :
    (transportedHalfDensitySchwartz c d K hK hKU f hfS : E → ℂ) =
      transportedHalfDensity c d K f := rfl

end Burnett.Microlocal.AtlasOverlapKernel

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter MeasureTheory Set
open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ComplexConjugate ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The half-density pullback moves the target scalar pairing onto the
same source overlap window. The zero extensions use the actual image. -/
theorem integral_transportHalfDensity_pairing (c d : AtlasChart M) (S : Set E) (hS : IsCompact S)
    (hSU : S ⊆ (c.transition d).source) (f a v : E → ℂ) :
    (∫ y, conj (transportedHalfDensity c d S f y) * (a y * v y)) =
      ∫ x, conj (f x) * (a (overlapTransition c d x) *
        S.indicator (fun z => overlapJacobianWeight c d z • v (overlapTransition c d z)) x) := by
  let e := c.transition d
  let U := e '' S
  let F (y : E) := conj (overlapJacobianWeight d c y • f (overlapTransition d c y)) * (a y * v y)
  let G (x : E) := conj (f x) * (a (overlapTransition c d x) *
    (overlapJacobianWeight c d x • v (overlapTransition c d x)))
  have hU : IsCompact U := hS.image_of_continuousOn (e.continuousOn.mono hSU)
  have hL : (fun y => conj (transportedHalfDensity c d S f y) * (a y * v y)) = U.indicator F := by
    funext y
    by_cases hy : y ∈ U
    · simp only [transportedHalfDensity, U, e, F, indicator_of_mem hy]
    · simp only [transportedHalfDensity, U, e, indicator_of_notMem hy, map_zero, zero_mul]
  have hR : (fun x => conj (f x) * (a (overlapTransition c d x) *
      S.indicator (fun z => overlapJacobianWeight c d z • v (overlapTransition c d z)) x)) =
      S.indicator G := by
    funext x
    by_cases hx : x ∈ S
    · simp only [G, indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero]
  have hD (x : E) (hx : x ∈ S) : HasFDerivWithinAt e (fderiv ℝ e x) S x :=
    ((((c.smooth_transition d).differentiableOn (by simp)) x (hSU hx)).differentiableAt
      (e.open_source.mem_nhds (hSU hx))).hasFDerivAt.hasFDerivWithinAt
  rw [hL, hR, integral_indicator hU.measurableSet, integral_indicator hS.measurableSet,
    integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure E) hS.measurableSet hD
      (e.injOn.mono hSU) F]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) hS.measurableSet] with x hx
  let W := overlapJacobianWeight c d x
  let V := overlapJacobianWeight d c (e x)
  have hW : W * V = 1 := overlapJacobianWeight_inverse_mul c d (hSU hx)
  have hWc : (W : ℂ) * (V : ℂ) = 1 := by exact_mod_cast hW
  change |(fderiv ℝ e x).det| • F (e x) = G x
  rw [← overlapJacobianWeight_sq_on_source c d (hSU hx)]
  unfold F G
  rw [overlapTransition_reverse_apply c d (hSU hx), overlapTransition_eq c d (hSU hx)]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, Complex.ofReal_pow]
  change (W : ℂ)^2 * ((V : ℂ) * conj (f x) * (a (e x) * v (e x))) =
    conj (f x) * (a (e x) * ((W : ℂ) * v (e x)))
  calc
    _ = (W : ℂ) * ((W : ℂ) * (V : ℂ)) * (conj (f x) * (a (e x) * v (e x))) := by ring
    _ = _ := by rw [hWc, mul_one]; ring

end Burnett.Microlocal.AtlasOverlapKernel

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ComplexConjugate ContDiff InnerProduct Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

private theorem transportedHalfDensity_recover (c d : AtlasChart M) (S : Set E)
    (hSU : S ⊆ (c.transition d).source) (f : E → ℂ) {x : E} (hx : x ∈ S) :
    overlapJacobianWeight c d x • transportedHalfDensity c d S f (overlapTransition c d x) = f x := by
  rw [overlapTransition_eq c d (hSU hx)]
  have hImg : c.transition d x ∈ c.transition d '' S := mem_image_of_mem _ hx
  rw [transportedHalfDensity, indicator_of_mem hImg, overlapTransition_reverse_apply c d (hSU hx),
    smul_smul, overlapJacobianWeight_inverse_mul c d (hSU hx), one_smul]

/-- Half-density transport preserves the actual L² inner product on the
overlap-supported Schwartz inputs. -/
theorem transportedHalfDensitySchwartz_inner_toLp (c d : AtlasChart M) (S : Set E) (hS : IsCompact S)
    (hSU : S ⊆ (c.transition d).source) (f g : SchwartzMap E ℂ)
    (hf : tsupport (f : E → ℂ) ⊆ S) (hg : tsupport (g : E → ℂ) ⊆ S) :
    inner ℂ ((transportedHalfDensitySchwartz c d S hS hSU f hf).toLp 2 volume)
      ((transportedHalfDensitySchwartz c d S hS hSU g hg).toLp 2 volume) =
      inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  let F := transportedHalfDensitySchwartz c d S hS hSU f hf
  let G := transportedHalfDensitySchwartz c d S hS hSU g hg
  have hPair (u v : SchwartzMap E ℂ) : inner ℂ (u.toLp 2 volume) (v.toLp 2 volume) =
      ∫ y, conj (u y) * v y := by
    rw [L2.inner_def]
    exact integral_congr_ae (by
      filter_upwards [u.coeFn_toLp 2 volume, v.coeFn_toLp 2 volume] with x hx hy
      simp only [RCLike.inner_apply', hx, hy])
  change inner ℂ (F.toLp 2 volume) (G.toLp 2 volume) = _
  rw [hPair, hPair]
  have h := integral_transportHalfDensity_pairing c d S hS hSU
    f (fun _ => 1) (transportedHalfDensity c d S g)
  simp only [one_mul] at h
  change (∫ y, conj (transportedHalfDensity c d S f y) * transportedHalfDensity c d S g y) = _
  rw [h]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx, transportedHalfDensity_recover c d S hSU g hx]
  · have hz : f x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := (f : E → ℂ)) (fun h => hx (hf h))
    simp only [hz, map_zero, zero_mul]

theorem transportedHalfDensitySchwartz_norm_toLp (c d : AtlasChart M) (S : Set E) (hS : IsCompact S)
    (hSU : S ⊆ (c.transition d).source) (f : SchwartzMap E ℂ)
    (hf : tsupport (f : E → ℂ) ⊆ S) :
    ‖(transportedHalfDensitySchwartz c d S hS hSU f hf).toLp 2 volume‖ =
      ‖f.toLp 2 volume‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ), transportedHalfDensitySchwartz_inner_toLp]

end Burnett.Microlocal.AtlasOverlapKernel
