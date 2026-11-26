import Burnett.Geometry.Causality.ChartCausalConeMargin
import Burnett.Geometry.Causality.ChartMetricLipschitz
import Burnett.Geometry.Causality.CausalPushUpEstimate

set_option autoImplicit false
set_option maxHeartbeats 4350000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set
open scoped ContDiff Manifold
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Moving the point in an actual chart and adding a sufficiently dominant
future velocity makes the shifted velocity strictly timelike. -/
theorem chart_causalCone_stable_under_time_push {g : Field (M := M)} (hg : IsSmooth g)
    (hL : HasLorentzSignature g) (c : M) (n : E) {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K)
    (htarget : K ⊆ (chartAt E c).target) (hn : ∀ y ∈ K, coordinateBilinear g c y n n < 0) :
    ∃ κ > (0 : ℝ), ∃ L ≥ (0 : ℝ), let B := coordinateBilinear g c
      ∀ y ∈ K, ∀ z ∈ K, ∀ v : E, ∀ α > (0 : ℝ),
      B y v v ≤ 0 → B y n v ≤ 0 → L * ‖z - y‖ * ‖n‖ ≤ κ → L * ‖z - y‖ * ‖v‖ ≤ κ * α →
      B z (v + α • n) (v + α • n) < 0 ∧ B z n (v + α • n) < 0 := by
  obtain ⟨a, ha, hCone⟩ := uniform_chart_causal_pairing hg hL c n hK htarget hn
  obtain ⟨L, hL0, hLip⟩ := chart_metric_lipschitz_on_compact_convex hg c hK hc htarget
  let κ := a / 2
  have hκ : 0 < κ := half_pos ha
  refine ⟨κ, hκ, L, hL0, ?_⟩
  intro B y hy z hz v α hα hSelf hMix hSmall hDom
  have hS : (B z).IsSymm := coordinateBilinear_symmetric g hL.isSymmetric c z
  have h1 := (le_abs_self (B z n v - B y n v)).trans (hLip z hz y hy n v)
  have h2 := (le_abs_self (B z v v - B y v v)).trans (hLip z hz y hy v v)
  have h3 : B z n v ≤ -κ * ‖v‖ := by
    have hClose := mul_le_mul_of_nonneg_right hSmall (norm_nonneg v)
    have hNeg : B y n v ≤ -a * ‖v‖ := hCone y hy v hSelf hMix
    dsimp only [κ] at hClose ⊢
    linarith
  have h4 : B z v v ≤ (L * ‖z - y‖) * ‖v‖ ^ 2 := by
    rw [pow_two, ← mul_assoc]
    linarith
  exact timelike_of_dominating_time_push (B z) hS n v hκ hα (hn z hz) h3 h4 hDom

end Burnett.Geometry.FiniteCausalVolume
