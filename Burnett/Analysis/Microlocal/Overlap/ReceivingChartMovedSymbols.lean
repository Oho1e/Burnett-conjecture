import Burnett.Analysis.Microlocal.Overlap.ReceivingChartFourierConjugation
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartGeometricBridge
import Burnett.Analysis.Microlocal.Overlap.BaseFourierAngularRegularity
import Burnett.Analysis.Microlocal.Overlap.CompactFrequencyLeftAction

/-! The actual inverse-adjoint principal symbol and the compact-frequency
correction for its fixed infrared normalization on one chart window. -/

/-!
# Smooth frequency change for the frozen chart derivative

On the actual overlap the inverse adjoint is the adjoint of the
derivative of the reverse chart evaluated at the image point.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Set Matrix Burnett.Analysis.CapFourier Burnett.RicciSymbol
open Burnett.Geometry.ActualChartSecondJet (contDiffOn_chartTransition_infty)
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.UnitNullCompactness (cotangentTransitionMatrix)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.OverlapGradient
open Burnett.Geometry.MaximalChart (AtlasChart chartTransition_fderiv_leftInverse)
open scoped ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

theorem chartTransitionFrequency_eq_frozen (c d : AtlasChart M) {x : E}
    (hx : x ∈ (c.transition d).source) (ξ : E) :
    receivingFrequency c d x ξ = frozenChartFrequency c d hx ξ := by
  let A := frozenChartDerivative c d hx
  let J := fderiv ℝ (overlapTransition c d) x
  let K := fderiv ℝ (d.transition c) (c.transition d x)
  have hA : A.toContinuousLinearMap = J :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  have hComp : K.comp J = ContinuousLinearMap.id ℝ E := by
    change K.comp (fderiv ℝ (overlapTransition c d) x) = _
    rw [overlapTransition_fderiv c d hx]
    exact chartTransition_fderiv_leftInverse c d hx
  have hDual : J.adjoint.comp K.adjoint = ContinuousLinearMap.id ℝ E := by
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
      congrArg (fun L : E →L[ℝ] E => L.adjoint) hComp
  apply (physicalDualEquiv A).injective
  change (physicalDualEquiv A) (K.adjoint ξ) = (physicalDualEquiv A) ((physicalDualEquiv A).symm ξ)
  rw [ContinuousLinearEquiv.apply_symm_apply, physicalDualEquiv_apply, hA]
  exact congrArg (fun L : E →L[ℝ] E => L ξ) hDual

private def realAdjointCLM : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap

theorem contDiffOn_receivingFrequency (c d : AtlasChart M) :
    ContDiffOn ℝ ∞ (receivingFrequency c d) (c.transition d).source := by
  let e := c.transition d
  let f := d.transition c
  have hs : e.symm = f := by
    simp only [e, f, AtlasChart.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hm : MapsTo e e.source f.source := by
    rw [← hs]
    exact e.mapsTo
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) f.source :=
    (d.smooth_transition c).fderiv_of_isOpen f.open_source (by simp)
  exact realAdjointCLM.contDiff.comp_contDiffOn
    (hD.comp (c.smooth_transition d) hm)

/-- On a fixed compact overlap window, both frequency maps have bounded
operator norm, uniformly over all input covectors. -/
theorem exists_frozenChartFrequency_norm_bounds (c d : AtlasChart M) (K : Set E)
    (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source) :
    ∃ l u : ℝ, 0 < l ∧ 0 < u ∧ ∀ x (hx : x ∈ K) (ξ : E),
      l * ‖ξ‖ ≤ ‖frozenChartFrequency c d (hKU hx) ξ‖ ∧
        ‖frozenChartFrequency c d (hKU hx) ξ‖ ≤ u * ‖ξ‖ := by
  let D (x : E) : E →L[ℝ] E := (fderiv ℝ (c.transition d) x).adjoint
  have hDiff : ContDiffOn ℝ 0 (fderiv ℝ (c.transition d)) (c.transition d).source :=
    (c.smooth_transition d).fderiv_of_isOpen (c.transition d).open_source (by simp)
  have hD : ContinuousOn D (c.transition d).source :=
    realAdjointCLM.continuous.comp_continuousOn hDiff.continuousOn
  obtain ⟨L, hL, hDL⟩ := (hK.image_of_continuousOn (hD.mono hKU)).isBounded.exists_pos_norm_le
  obtain ⟨U, hU, hFU⟩ := (hK.image_of_continuousOn
    ((contDiffOn_receivingFrequency c d).continuousOn.mono hKU)).isBounded.exists_pos_norm_le
  refine ⟨L⁻¹, U, inv_pos.mpr hL, hU, fun x hx ξ => ⟨?_, ?_⟩⟩
  · let η := frozenChartFrequency c d (hKU hx) ξ
    have hInv : D x η = ξ := by
      unfold D
      rw [← overlapTransition_fderiv c d (hKU hx)]
      exact frozenChartFrequency_inverse_adjoint c d (hKU hx) ξ
    have hB : ‖ξ‖ ≤ L * ‖η‖ := by
      rw [← hInv]
      exact ((D x).le_opNorm η).trans
        (mul_le_mul_of_nonneg_right (hDL _ (mem_image_of_mem _ hx)) (norm_nonneg _))
    rwa [inv_mul_eq_div, div_le_iff₀ hL, mul_comm]
  · rw [← chartTransitionFrequency_eq_frozen c d (hKU hx)]
    exact ((receivingFrequency c d x).le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right (hFU _ (mem_image_of_mem _ hx)) (norm_nonneg _))

end Burnett.Microlocal.AtlasOverlapKernel

/-!
# The angular symbol in the source chart

The new symbol uses the actual inverse adjoint on frequency and the
prescribed compact base factor. Its principal part is homogeneous of
degree zero. The transformed infrared normalization differs from a
fixed source-coordinate normalization only on a compact frequency set.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter Set Burnett.Fourier
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The compactly based principal symbol after changing charts. -/
def movingChartAngularSymbol (c d : AtlasChart M) (a m : E → ℂ) (p : E × E) : ℂ :=
  a p.1 * m (receivingFrequency c d p.1 p.2)

theorem movingChartAngularSymbol_eq_frozen (c d : AtlasChart M) (a m : E → ℂ)
    {x : E} (hx : x ∈ (c.transition d).source) (ξ : E) :
    movingChartAngularSymbol c d a m (x, ξ) = a x * m (frozenChartFrequency c d hx ξ) := by
  rw [movingChartAngularSymbol, chartTransitionFrequency_eq_frozen c d hx]

private theorem contDiffOn_frequency_apply (c d : AtlasChart M) {s : Set (E × E)}
    (hs : MapsTo Prod.fst s (c.transition d).source) :
    ContDiffOn ℝ ∞ (fun p : E × E => receivingFrequency c d p.1 p.2) s :=
  ((contDiffOn_receivingFrequency c d).comp contDiffOn_fst hs).clm_apply contDiffOn_snd

private theorem contDiffOn_movingChartAngularSymbol_overlap (c d : AtlasChart M) (a m : E → ℂ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) :
    ContDiffOn ℝ ∞ (movingChartAngularSymbol c d a m)
      ((c.transition d).source ×ˢ ({0}ᶜ : Set E)) := by
  have hfreq := contDiffOn_frequency_apply c d
    (s := (c.transition d).source ×ˢ ({0}ᶜ : Set E)) (fun _ hp => hp.1)
  have hMaps : MapsTo (fun p : E × E => receivingFrequency c d p.1 p.2)
      ((c.transition d).source ×ˢ ({0}ᶜ : Set E)) ({0}ᶜ : Set E) := by
    intro p hp
    change receivingFrequency c d p.1 p.2 ≠ 0
    rw [chartTransitionFrequency_eq_frozen c d hp.1]
    intro hz
    apply hp.2
    exact (frozenChartFrequency c d hp.1).injective (hz.trans (map_zero _).symm)
  exact ((ha.comp contDiff_fst).contDiffOn).mul (hm.comp hfreq hMaps)

theorem contDiffAt_movingChartAngularSymbol (c d : AtlasChart M) (a m : E → ℂ)
    (ha : ContDiff ℝ ∞ a) (hSupp : tsupport a ⊆ (c.transition d).source)
    (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) {p : E × E} (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (movingChartAngularSymbol c d a m) p := by
  by_cases hx : p.1 ∈ (c.transition d).source
  · exact (contDiffOn_movingChartAngularSymbol_overlap c d a m ha hm).contDiffAt
      (((c.transition d).open_source.prod isOpen_compl_singleton).mem_nhds ⟨hx, hp⟩)
  · have ha0 : a =ᶠ[𝓝 p.1] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hp' => hx (hSupp hp'))
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E × E => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [ha0.comp_tendsto (continuous_fst.continuousAt :
      ContinuousAt (Prod.fst : E × E → E) p)] with q hq
    change a q.1 = (0 : ℂ) at hq
    simp only [movingChartAngularSymbol, hq, zero_mul]

theorem contDiffOn_movingChartAngularSymbol (c d : AtlasChart M) (a m : E → ℂ)
    (ha : ContDiff ℝ ∞ a) (hSupp : tsupport a ⊆ (c.transition d).source)
    (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) :
    ContDiffOn ℝ ∞ (movingChartAngularSymbol c d a m) (univ ×ˢ ({0}ᶜ : Set E)) :=
  fun _ hp => (contDiffAt_movingChartAngularSymbol c d a m ha hSupp hm hp.2).contDiffWithinAt

theorem movingChartAngularSymbol_degreeZero (c d : AtlasChart M) (a m : E → ℂ) (hm : DegreeZero m)
    (x : E) : DegreeZero (fun ξ => movingChartAngularSymbol c d a m (x, ξ)) := by
  intro t ht ξ
  simp only [movingChartAngularSymbol, map_smul, hm t ht]

theorem movingChartAngularSymbol_tsupport_base (c d : AtlasChart M) (a m : E → ℂ) :
    tsupport (movingChartAngularSymbol c d a m) ⊆ Prod.fst ⁻¹' tsupport a := by
  have hClosed : IsClosed (tsupport a) := isClosed_closure
  apply closure_minimal _ (hClosed.preimage continuous_fst)
  intro p hp
  by_contra h
  exact hp (by simp only [movingChartAngularSymbol, image_eq_zero_of_notMem_tsupport h, zero_mul])

theorem movingChartAngularSymbol_norm_le (c d : AtlasChart M) (a m : BoundedSymbol E) (p : E × E) :
    ‖movingChartAngularSymbol c d a m p‖ ≤ a.bound * m.bound := by
  rw [movingChartAngularSymbol, norm_mul]
  exact mul_le_mul (a.norm_le p.1) (m.norm_le _) (norm_nonneg _) a.bound_nonneg

/-- Use the fixed source-frequency core on the moving homogeneous symbol. -/
def movingChartFixedCoreSymbol (c d : AtlasChart M) (a m : E → ℂ) (p : E × E) : ℂ :=
  ((1 - radialCore p.2 : ℝ) : ℂ) * movingChartAngularSymbol c d a m p

/-- The explicit correction between the two infrared treatments. -/
def movingChartInfraredRemainder (c d : AtlasChart M) (a m : E → ℂ) (p : E × E) : ℂ :=
  ((radialCore p.2 - radialCore (receivingFrequency c d p.1 p.2) : ℝ) : ℂ) *
    movingChartAngularSymbol c d a m p

theorem movingChartNormalizedSymbol_eq_fixedCore_add (c d : AtlasChart M) (a : E → ℂ)
    (m : BoundedSymbol E) {x : E} (hx : x ∈ (c.transition d).source) (ξ : E) :
    a x * normalizedAngularSymbol m (frozenChartFrequency c d hx ξ) =
      movingChartFixedCoreSymbol c d a m (x, ξ) + movingChartInfraredRemainder c d a m (x, ξ) := by
  simp only [movingChartFixedCoreSymbol, movingChartInfraredRemainder, movingChartAngularSymbol,
    chartTransitionFrequency_eq_frozen c d hx]
  let η := frozenChartFrequency c d hx ξ
  have hNormalized : normalizedAngularSymbol m η = (1 - (radialCore η : ℂ)) * m η := by
    change (1 - (radialCore ((1 : ℝ) • η) : ℂ)) * m η = _
    rw [one_smul]
  change a x * normalizedAngularSymbol m η = _
  rw [hNormalized]
  push_cast
  ring

/-- The difference is supported on a uniform frequency ball over the same compact base. -/
theorem exists_movingChartInfraredRemainder_tsupport_subset
    (c d : AtlasChart M) (a m : E → ℂ) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (hSupp : tsupport a ⊆ K) :
    ∃ R : ℝ, 0 < R ∧ tsupport (movingChartInfraredRemainder c d a m) ⊆
      K ×ˢ Metric.closedBall (0 : E) R := by
  obtain ⟨l, u, hl, _, hNorm⟩ := exists_frozenChartFrequency_norm_bounds c d K hK hKU
  let R := max 2 (2 / l)
  have hR : 0 < R := zero_lt_two.trans_le (le_max_left _ _)
  refine ⟨R, hR, closure_minimal ?_ (hK.isClosed.prod Metric.isClosed_closedBall)⟩
  intro p hp
  have hBase : p.1 ∈ K := by
    by_contra h
    exact hp (by simp only [movingChartInfraredRemainder, movingChartAngularSymbol,
      image_eq_zero_of_notMem_tsupport (fun hs => h (hSupp hs)), zero_mul, mul_zero])
  refine ⟨hBase, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  have hFar : R < ‖p.2‖ := lt_of_not_ge h
  have hLarge : 2 ≤ ‖p.2‖ := (le_max_left _ _).trans hFar.le
  have hf : 2 ≤ ‖frozenChartFrequency c d (hKU hBase) p.2‖ := by
    have hb := (le_max_right (2 : ℝ) (2 / l)).trans hFar.le
    exact ((div_le_iff₀ hl).mp hb).trans (by
      rw [mul_comm]; exact (hNorm p.1 hBase p.2).1)
  exact hp (by simp only [movingChartInfraredRemainder, radialCore_eq_zero p.2 hLarge,
    chartTransitionFrequency_eq_frozen c d (hKU hBase), radialCore_eq_zero _ hf,
    sub_self, Complex.ofReal_zero, zero_mul])

end Burnett.Microlocal.AtlasOverlapKernel

/-!
# Smoothness of the infrared correction

Both radial cores equal one in a uniform neighborhood of zero frequency
over the compact chart window. Their difference is a smooth compactly
supported joint symbol.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter Set
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

theorem exists_movingChartInfraredRemainder_zero_near (c d : AtlasChart M) (a m : E → ℂ)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (hSupp : tsupport a ⊆ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ξ, ‖ξ‖ ≤ ε → movingChartInfraredRemainder c d a m (x, ξ) = 0 := by
  obtain ⟨l, u, _, hu, hNorm⟩ := exists_frozenChartFrequency_norm_bounds c d K hK hKU
  let ε : ℝ := min 1 (1 / u)
  have hε : 0 < ε := lt_min zero_lt_one (div_pos zero_lt_one hu)
  refine ⟨ε, hε, fun x ξ hξ => ?_⟩
  by_cases hx : x ∈ K
  · have hSmall : ‖ξ‖ ≤ 1 := hξ.trans (min_le_left _ _)
    have hMoved : ‖frozenChartFrequency c d (hKU hx) ξ‖ ≤ 1 := by
      calc
        _ ≤ u * ‖ξ‖ := (hNorm x hx ξ).2
        _ ≤ u * (1 / u) := mul_le_mul_of_nonneg_left (hξ.trans (min_le_right _ _)) hu.le
        _ = 1 := by field_simp [hu.ne']
    simp only [movingChartInfraredRemainder, radialCore_eq_one _ hSmall,
      chartTransitionFrequency_eq_frozen c d (hKU hx), radialCore_eq_one _ hMoved,
      sub_self, Complex.ofReal_zero, zero_mul]
  · simp only [movingChartInfraredRemainder, movingChartAngularSymbol,
      image_eq_zero_of_notMem_tsupport (fun hs => hx (hSupp hs)), zero_mul, mul_zero]

private theorem frequencyBall_eventually {p : E × E} (hp : p.2 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : E × E in 𝓝 p, ‖q.2‖ ≤ ε := by
  have hBall : (Prod.snd ⁻¹' Metric.ball (0 : E) ε : Set (E × E)) ∈ 𝓝 p :=
    (Metric.isOpen_ball.preimage continuous_snd).mem_nhds (by
      change p.2 ∈ Metric.ball (0 : E) ε
      rw [hp]
      exact Metric.mem_ball_self hε)
  filter_upwards [hBall] with q hq
  have hdist : dist q.2 (0 : E) < ε := hq
  simpa only [dist_zero_right] using hdist.le

theorem contDiff_movingChartFixedCoreSymbol (c d : AtlasChart M) (a m : E → ℂ)
    (ha : ContDiff ℝ ∞ a) (hSupp : tsupport a ⊆ (c.transition d).source)
    (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) :
    ContDiff ℝ ∞ (movingChartFixedCoreSymbol c d a m) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.2 = 0
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E × E => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [frequencyBall_eventually hp zero_lt_one] with q hq
    simp only [movingChartFixedCoreSymbol, radialCore_eq_one _ hq, sub_self,
      Complex.ofReal_zero, zero_mul]
  · have hCore : ContDiff ℝ ∞ (fun q : E × E => ((1 - radialCore q.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (radialCore_contDiff.comp contDiff_snd))
    exact hCore.contDiffAt.mul (contDiffAt_movingChartAngularSymbol c d a m ha hSupp hm hp)

theorem contDiff_movingChartInfraredRemainder (c d : AtlasChart M) (a m : E → ℂ)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (hSupp : tsupport a ⊆ K) (ha : ContDiff ℝ ∞ a)
    (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) :
    ContDiff ℝ ∞ (movingChartInfraredRemainder c d a m) := by
  obtain ⟨ε, hε, hZero⟩ := exists_movingChartInfraredRemainder_zero_near c d a m K hK hKU hSupp
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.2 = 0
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E × E => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [frequencyBall_eventually hp hε] with q hq
    exact hZero q.1 q.2 hq
  · by_cases hx : p.1 ∈ (c.transition d).source
    · have hΦ : ContDiffOn ℝ ∞ (fun q : E × E => receivingFrequency c d q.1 q.2)
          ((c.transition d).source ×ˢ univ) :=
        ((contDiffOn_receivingFrequency c d).comp contDiffOn_fst
          (fun _ hq => hq.1)).clm_apply contDiffOn_snd
      have hΦ_at := hΦ.contDiffAt
        (((c.transition d).open_source.prod isOpen_univ).mem_nhds ⟨hx, trivial⟩)
      have hCore : ContDiffAt ℝ ∞ (fun q : E × E =>
          ((radialCore q.2 - radialCore (receivingFrequency c d q.1 q.2) : ℝ) : ℂ)) p :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp p
          ((radialCore_contDiff.comp contDiff_snd).contDiffAt.sub
            (radialCore_contDiff.contDiffAt.comp p hΦ_at))
      exact hCore.mul (contDiffAt_movingChartAngularSymbol c d a m ha (hSupp.trans hKU) hm hp)
    · have ha0 : a =ᶠ[𝓝 p.1] fun _ => 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hKU (hSupp h)))
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E × E => (0 : ℂ)) p).congr_of_eventuallyEq
      filter_upwards [ha0.comp_tendsto (continuous_fst.continuousAt :
        ContinuousAt (Prod.fst : E × E → E) p)] with q hq
      change a q.1 = (0 : ℂ) at hq
      simp only [movingChartInfraredRemainder, movingChartAngularSymbol, hq, zero_mul, mul_zero]

/-- The infrared difference is an actual joint Schwartz profile. -/
def movingChartInfraredRemainderSchwartz (c d : AtlasChart M) (a m : E → ℂ)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (hSupp : tsupport a ⊆ K) (ha : ContDiff ℝ ∞ a)
    (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) : SchwartzMap (E × E) ℂ :=
  have hCompact : HasCompactSupport (movingChartInfraredRemainder c d a m) := by
    obtain ⟨R, _, hSupport⟩ :=
      exists_movingChartInfraredRemainder_tsupport_subset c d a m K hK hKU hSupp
    exact (hK.prod (isCompact_closedBall (0 : E) R)).of_isClosed_subset isClosed_closure hSupport
  hCompact.toSchwartzMap (contDiff_movingChartInfraredRemainder c d a m K hK hKU hSupp ha hm)

end Burnett.Microlocal.AtlasOverlapKernel

set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter Function MeasureTheory Metric Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.OverlapKernel
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.Overlap (measurable_baseAngularSymbol contDiff_baseAngularSection exists_compactFrequency_leftAction_strongZero)
open scoped ContDiff FourierTransform InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The low frequency portion of the moving homogeneous symbol. -/
def movingChartLowSymbol (c d : AtlasChart M) (a m : E → ℂ) (x ξ : E) : ℂ :=
  (↑(radialCore (receivingFrequency c d x ξ)) : ℂ) * movingChartAngularSymbol c d a m (x,ξ)

private theorem movingChartLowSymbol_eq (c d : AtlasChart M) (a m : E → ℂ) (x ξ : E) :
    movingChartLowSymbol c d a m x ξ =
      (↑(radialCore ξ) : ℂ) * movingChartAngularSymbol c d a m (x,ξ) -
        movingChartInfraredRemainder c d a m (x,ξ) := by
  unfold movingChartLowSymbol movingChartInfraredRemainder
  push_cast
  ring

theorem measurable_movingChartLowSymbol (c d : AtlasChart M) (a m : E → ℂ)
    (S : Set E) (hS : IsCompact S) (hSU : S ⊆ (c.transition d).source)
    (hSupport : tsupport a ⊆ S) (ha : ContDiff ℝ ∞ a)
    (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) :
    Measurable (uncurry (movingChartLowSymbol c d a m)) := by
  let p (x ξ : E) := movingChartAngularSymbol c d a m (x,ξ)
  have hJoint : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)) :=
    contDiffOn_movingChartAngularSymbol c d a m ha (hSupport.trans hSU) hm
  have hZero : ContDiff ℝ ∞ (fun x => p x 0) := by
    simp only [p, movingChartAngularSymbol, map_zero]
    exact ha.mul contDiff_const
  have hp : Measurable (uncurry p) :=
    measurable_baseAngularSymbol
      (fun ξ => (contDiff_baseAngularSection p hJoint hZero ξ).continuous)
      (fun x => hJoint.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hξ => ⟨mem_univ x, hξ⟩))
  have hrad : Measurable (fun q : E × E => (↑(radialCore q.2) : ℂ)) :=
    (Complex.continuous_ofReal.comp (radialCore_contDiff.continuous.comp continuous_snd)).measurable
  have hrem : Measurable (movingChartInfraredRemainder c d a m) :=
    (contDiff_movingChartInfraredRemainder c d a m S hS hSU hSupport ha hm).continuous.measurable
  have heq : uncurry (movingChartLowSymbol c d a m) =
      (fun q : E × E => (↑(radialCore q.2) : ℂ) * p q.1 q.2 -
        movingChartInfraredRemainder c d a m q) := by
    funext q
    exact movingChartLowSymbol_eq c d a m q.1 q.2
  rw [heq]
  exact (hrad.mul hp).sub hrem

theorem movingChartLowSymbol_norm_le (c d : AtlasChart M) (a m : BoundedSymbol E) (x ξ : E) :
    ‖movingChartLowSymbol c d a m x ξ‖ ≤ a.bound * m.bound := by
  rw [movingChartLowSymbol, norm_mul, Complex.norm_real, Real.norm_of_nonneg (radialCore_nonneg _)]
  exact ((mul_le_mul_of_nonneg_right (radialCore_le_one _) (norm_nonneg _)).trans_eq
    (one_mul _)).trans (movingChartAngularSymbol_norm_le c d a m (x,ξ))

/-- The exact infrared term in the moving coordinate has strong L²
limit zero on the original weakly null input. -/
theorem exists_movingChartLowAction_strongZero (c d : AtlasChart M) (a m : BoundedSymbol E)
    (S : Set E) (hS : IsCompact S) (hSU : S ⊆ (c.transition d).source)
    (hSupport : tsupport (a : E → ℂ) ⊆ S) (ha : ContDiff ℝ ∞ (a : E → ℂ))
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (f : ℕ → SchwartzMap E ℂ) (B : ℝ) (hB : ∀ n, ‖(f n).toLp 2 volume‖ ≤ B)
    (hw : ∀ w : ComplexL2 E,
      Tendsto (fun n => inner ℂ w ((f n).toLp 2 volume)) atTop (𝓝 0)) :
    ∃ A : ℕ → ComplexL2 E,
      (∀ n, A n =ᵐ[volume] firstOrderAction (movingChartLowSymbol c d a m) (f n)) ∧
      Tendsto A atTop (𝓝 0) := by
  obtain ⟨L, U, hL, _, hLU⟩ := exists_frozenChartFrequency_norm_bounds c d S hS hSU
  have hM := measurable_movingChartLowSymbol c d a m S hS hSU hSupport ha hm
  refine exists_compactFrequency_leftAction_strongZero _ hM S (closedBall 0 (2 / L))
    hS (isCompact_closedBall _ _) ?_ (a.bound * m.bound)
    (mul_nonneg a.bound_nonneg m.bound_nonneg) (movingChartLowSymbol_norm_le c d a m) f B hB hw
  · intro x ξ hxξ
    by_cases hx : x ∈ S
    · have hξ : 2 / L < ‖ξ‖ := by
        simpa only [mem_closedBall, dist_zero_right, not_le] using
          (hxξ.resolve_left (not_not_intro hx))
      have hz : 2 ≤ ‖receivingFrequency c d x ξ‖ := by
        rw [chartTransitionFrequency_eq_frozen c d (hSU hx)]
        have h := (div_le_iff₀ hL).mp hξ.le
        rw [mul_comm] at h
        exact h.trans (hLU x hx ξ).1
      simp only [movingChartLowSymbol, radialCore_eq_zero _ hz, Complex.ofReal_zero, zero_mul]
    · have h0 : a x = 0 :=
        image_eq_zero_of_notMem_tsupport (f := (a : E → ℂ)) (fun h => hx (hSupport h))
      simp only [movingChartLowSymbol, movingChartAngularSymbol, h0, zero_mul, mul_zero]

/-- Pointwise decomposition of the transformed normalized symbol on the overlap. -/
theorem movingChart_normalizedAngular_eq_principal_sub_low (c d : AtlasChart M) (a : E → ℂ)
    (m : BoundedSymbol E) {x : E} (hx : x ∈ (c.transition d).source) (ξ : E) :
    a x * normalizedAngularSymbol m (frozenChartFrequency c d hx ξ) =
      movingChartAngularSymbol c d a m (x,ξ) - movingChartLowSymbol c d a m x ξ := by
  rw [movingChartNormalizedSymbol_eq_fixedCore_add c d a m hx ξ, movingChartLowSymbol_eq]
  unfold movingChartFixedCoreSymbol
  push_cast
  ring

end Burnett.Microlocal.AtlasOverlapKernel
