import Burnett.Analysis.TransportWard.Weyl.PalatiniSmoothPath
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation under a fixed compact coordinate integral. -/

set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option maxRecDepth 4600

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Metric Set
open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open scoped ContDiff Topology

local notation "E" => CoordinateSpace
local notation "P" => MetricParameterSpace

theorem continuousOn_parameterSlice_compact (F : P → ℝ) {Ω : Set P}
    (hF : ContinuousOn F Ω) {K : Set E} (t : ℝ) (hK : ∀ y ∈ K, (t, y) ∈ Ω) :
    ContinuousOn (fun y => F (t, y)) K :=
  hF.comp (continuous_const.prodMk continuous_id).continuousOn hK

/-- The time derivative under the actual Lebesgue integral. The required
compact parameter rectangle lies in the genuine joint smoothness domain. -/
theorem hasDerivAt_integral_compact_parameter (F : P → ℝ) {Ω : Set P} (hΩ : IsOpen Ω)
    (hF : ContDiffOn ℝ ∞ F Ω) {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (hSub : closedBall (0 : ℝ) ε ×ˢ K ⊆ Ω) :
    HasDerivAt (fun t => ∫ x in K, F (t, x)) (∫ x in K, fderiv ℝ F (0, x) (1, 0)) 0 := by
  let μ := (volume : Measure E).restrict K
  let D (z : P) := fderiv ℝ F z (1, 0)
  letI : IsFiniteMeasure μ := ⟨by
    dsimp [μ]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact hK.measure_lt_top⟩
  have hDWithin : ContDiffOn ℝ ∞ (fderiv ℝ F) Ω := hF.fderiv_of_isOpen hΩ (by simp)
  have hD : ContinuousOn D Ω := (hDWithin.clm_apply contDiffOn_const).continuousOn
  have hC : IsCompact (closedBall (0 : ℝ) ε ×ˢ K) := (isCompact_closedBall _ _).prod hK
  obtain ⟨M, hM⟩ := (hC.image_of_continuousOn (hD.mono hSub)).isBounded.exists_norm_le
  have hNear : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ ball (0 : ℝ) ε := ball_mem_nhds 0 hε
  have htime (t : ℝ) (ht : t ∈ closedBall (0 : ℝ) ε) :
      ContinuousOn (fun x => F (t, x)) K :=
    continuousOn_parameterSlice_compact F hF.continuousOn t (fun _ hx => hSub ⟨ht, hx⟩)
  have h0 : (0 : ℝ) ∈ closedBall (0 : ℝ) ε := mem_closedBall_self hε.le
  have hDm : AEStronglyMeasurable (fun x => D (0, x)) μ :=
    ((continuousOn_parameterSlice_compact D hD 0 (fun _ hx => hSub ⟨h0, hx⟩)).integrableOn_compact
      hK).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun t x => F (t, x)) (F' := fun t x => D (t, x)) (bound := fun _ : E => M)
    hε ?_ ((htime 0 h0).integrableOn_compact hK) hDm ?_ (integrable_const M) ?_).2
  · exact hNear.mono fun t ht => ((htime t (ball_subset_closedBall ht)).integrableOn_compact
      hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure E)) hK.measurableSet] with x hx
    intro t ht
    exact hM _ (mem_image_of_mem _ ⟨ball_subset_closedBall ht, hx⟩)
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure E)) hK.measurableSet] with x hx
    intro t ht
    exact hasDerivAt_parameterSlice F t x
      ((hF.contDiffAt (hΩ.mem_nhds (hSub ⟨ball_subset_closedBall ht, hx⟩))).differentiableAt (by simp))

end Burnett.V03.Palatini
