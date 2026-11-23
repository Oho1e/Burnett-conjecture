import Burnett.Analysis.Microlocal.Overlap.MovingChartFrequency

/-!
# The angular symbol in the source chart

The new symbol uses the actual inverse adjoint on frequency and the
prescribed compact base factor. Its principal part is homogeneous of
degree zero. The transformed infrared normalization differs from a
fixed source-coordinate normalization only on a compact frequency set.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.OverlapKernel

open Filter Set Burnett.Fourier
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The compactly based principal symbol after changing charts. -/
def movingChartAngularSymbol (c d : M) (a m : E → ℂ) (p : E × E) : ℂ :=
  a p.1 * m (chartTransitionFrequency c d p.1 p.2)

theorem movingChartAngularSymbol_eq_frozen (c d : M) (a m : E → ℂ)
    {x : E} (hx : x ∈ (chartTransition c d).source) (ξ : E) :
    movingChartAngularSymbol c d a m (x, ξ) = a x * m (frozenChartFrequency c d hx ξ) := by
  rw [movingChartAngularSymbol, chartTransitionFrequency_eq_frozen c d hx]

private theorem contDiffOn_frequency_apply (c d : M) {s : Set (E × E)}
    (hs : MapsTo Prod.fst s (chartTransition c d).source) :
    ContDiffOn ℝ ∞ (fun p : E × E => chartTransitionFrequency c d p.1 p.2) s :=
  ((contDiffOn_chartTransitionFrequency c d).comp contDiffOn_fst hs).clm_apply contDiffOn_snd

private theorem contDiffOn_movingChartAngularSymbol_overlap (c d : M) (a m : E → ℂ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) :
    ContDiffOn ℝ ∞ (movingChartAngularSymbol c d a m)
      ((chartTransition c d).source ×ˢ ({0}ᶜ : Set E)) := by
  have hfreq := contDiffOn_frequency_apply c d
    (s := (chartTransition c d).source ×ˢ ({0}ᶜ : Set E)) (fun _ hp => hp.1)
  have hMaps : MapsTo (fun p : E × E => chartTransitionFrequency c d p.1 p.2)
      ((chartTransition c d).source ×ˢ ({0}ᶜ : Set E)) ({0}ᶜ : Set E) := by
    intro p hp
    change chartTransitionFrequency c d p.1 p.2 ≠ 0
    rw [chartTransitionFrequency_eq_frozen c d hp.1]
    intro hz
    apply hp.2
    exact (frozenChartFrequency c d hp.1).injective (hz.trans (map_zero _).symm)
  exact ((ha.comp contDiff_fst).contDiffOn).mul (hm.comp hfreq hMaps)

theorem contDiffAt_movingChartAngularSymbol (c d : M) (a m : E → ℂ)
    (ha : ContDiff ℝ ∞ a) (hSupp : tsupport a ⊆ (chartTransition c d).source)
    (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) {p : E × E} (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (movingChartAngularSymbol c d a m) p := by
  by_cases hx : p.1 ∈ (chartTransition c d).source
  · exact (contDiffOn_movingChartAngularSymbol_overlap c d a m ha hm).contDiffAt
      (((chartTransition c d).open_source.prod isOpen_compl_singleton).mem_nhds ⟨hx, hp⟩)
  · have ha0 : a =ᶠ[𝓝 p.1] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hp' => hx (hSupp hp'))
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E × E => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [ha0.comp_tendsto (continuous_fst.continuousAt :
      ContinuousAt (Prod.fst : E × E → E) p)] with q hq
    change a q.1 = (0 : ℂ) at hq
    simp only [movingChartAngularSymbol, hq, zero_mul]

theorem contDiffOn_movingChartAngularSymbol (c d : M) (a m : E → ℂ)
    (ha : ContDiff ℝ ∞ a) (hSupp : tsupport a ⊆ (chartTransition c d).source)
    (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) :
    ContDiffOn ℝ ∞ (movingChartAngularSymbol c d a m) (univ ×ˢ ({0}ᶜ : Set E)) :=
  fun _ hp => (contDiffAt_movingChartAngularSymbol c d a m ha hSupp hm hp.2).contDiffWithinAt

omit [IsManifold Model ∞ M] in
theorem movingChartAngularSymbol_degreeZero (c d : M) (a m : E → ℂ) (hm : DegreeZero m)
    (x : E) : DegreeZero (fun ξ => movingChartAngularSymbol c d a m (x, ξ)) := by
  intro t ht ξ
  simp only [movingChartAngularSymbol, map_smul, hm t ht]

omit [IsManifold Model ∞ M] in
theorem movingChartAngularSymbol_tsupport_base (c d : M) (a m : E → ℂ) :
    tsupport (movingChartAngularSymbol c d a m) ⊆ Prod.fst ⁻¹' tsupport a := by
  have hClosed : IsClosed (tsupport a) := isClosed_closure
  apply closure_minimal _ (hClosed.preimage continuous_fst)
  intro p hp
  by_contra h
  exact hp (by simp only [movingChartAngularSymbol, image_eq_zero_of_notMem_tsupport h, zero_mul])

omit [IsManifold Model ∞ M] in
theorem movingChartAngularSymbol_norm_le (c d : M) (a m : BoundedSymbol E) (p : E × E) :
    ‖movingChartAngularSymbol c d a m p‖ ≤ a.bound * m.bound := by
  rw [movingChartAngularSymbol, norm_mul]
  exact mul_le_mul (a.norm_le p.1) (m.norm_le _) (norm_nonneg _) a.bound_nonneg

/-- Use the fixed source-frequency core on the moving homogeneous symbol. -/
def movingChartFixedCoreSymbol (c d : M) (a m : E → ℂ) (p : E × E) : ℂ :=
  ((1 - radialCore p.2 : ℝ) : ℂ) * movingChartAngularSymbol c d a m p

/-- The explicit correction between the two infrared treatments. -/
def movingChartInfraredRemainder (c d : M) (a m : E → ℂ) (p : E × E) : ℂ :=
  ((radialCore p.2 - radialCore (chartTransitionFrequency c d p.1 p.2) : ℝ) : ℂ) *
    movingChartAngularSymbol c d a m p

theorem movingChartNormalizedSymbol_eq_fixedCore_add (c d : M) (a : E → ℂ)
    (m : BoundedSymbol E) {x : E} (hx : x ∈ (chartTransition c d).source) (ξ : E) :
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
    (c d : M) (a m : E → ℂ) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (chartTransition c d).source) (hSupp : tsupport a ⊆ K) :
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

end Burnett.Microlocal.OverlapKernel
