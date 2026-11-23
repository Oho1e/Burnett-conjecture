import Burnett.Analysis.Microlocal.Overlap.MovingChartAngularSymbol

/-!
# Smoothness of the infrared correction

Both radial cores equal one in a uniform neighborhood of zero frequency
over the compact chart window. Their difference is a smooth compactly
supported joint symbol.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.OverlapKernel

open Filter Set
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem exists_movingChartInfraredRemainder_zero_near (c d : M) (a m : E → ℂ)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
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

theorem contDiff_movingChartFixedCoreSymbol (c d : M) (a m : E → ℂ)
    (ha : ContDiff ℝ ∞ a) (hSupp : tsupport a ⊆ (chartTransition c d).source)
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

theorem contDiff_movingChartInfraredRemainder (c d : M) (a m : E → ℂ)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
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
  · by_cases hx : p.1 ∈ (chartTransition c d).source
    · have hΦ : ContDiffOn ℝ ∞ (fun q : E × E => chartTransitionFrequency c d q.1 q.2)
          ((chartTransition c d).source ×ˢ univ) :=
        ((contDiffOn_chartTransitionFrequency c d).comp contDiffOn_fst
          (fun _ hq => hq.1)).clm_apply contDiffOn_snd
      have hΦ_at := hΦ.contDiffAt
        (((chartTransition c d).open_source.prod isOpen_univ).mem_nhds ⟨hx, trivial⟩)
      have hCore : ContDiffAt ℝ ∞ (fun q : E × E =>
          ((radialCore q.2 - radialCore (chartTransitionFrequency c d q.1 q.2) : ℝ) : ℂ)) p :=
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
def movingChartInfraredRemainderSchwartz (c d : M) (a m : E → ℂ)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (hSupp : tsupport a ⊆ K) (ha : ContDiff ℝ ∞ a)
    (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) : SchwartzMap (E × E) ℂ :=
  have hCompact : HasCompactSupport (movingChartInfraredRemainder c d a m) := by
    obtain ⟨R, _, hSupport⟩ :=
      exists_movingChartInfraredRemainder_tsupport_subset c d a m K hK hKU hSupp
    exact (hK.prod (isCompact_closedBall (0 : E) R)).of_isClosed_subset isClosed_closure hSupport
  hCompact.toSchwartzMap (contDiff_movingChartInfraredRemainder c d a m K hK hKU hSupp ha hm)

end Burnett.Microlocal.OverlapKernel
