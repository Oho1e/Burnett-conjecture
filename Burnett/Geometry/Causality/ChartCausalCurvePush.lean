import Burnett.Geometry.Causality.ChartCausalPushUp
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option maxHeartbeats 5100000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set
open scoped ContDiff Manifold
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- A bounded-speed causal curve on a compact chart window has timelike
perturbations with the same final point and arbitrarily small initial shift. -/
theorem chartCausalCurve_time_push {g : Field (M := M)} (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (c : M) (x n : E) {r R a b V : ℝ} (hRad : r < R)
    (hTarget : Metric.closedBall x R ⊆ (chartAt E c).target)
    (hn : ∀ z ∈ Metric.closedBall x R, coordinateBilinear g c z n n < 0)
    (y v : ℝ → E) (hV : 0 ≤ V)
    (hpath : ∀ t ∈ Icc a b, y t ∈ Metric.closedBall x r ∧ HasDerivAt y (v t) t ∧
      coordinateBilinear g c (y t) (v t) (v t) ≤ 0 ∧
      coordinateBilinear g c (y t) n (v t) ≤ 0 ∧ ‖v t‖ ≤ V) :
    ∃ k > (0 : ℝ), ∃ e₀ > (0 : ℝ), ∀ ε > (0 : ℝ), ε < e₀ →
      let z := fun t => y t + (ε * endpointTimePush k b t) • n
      z b = y b ∧ ∀ t ∈ Icc a b,
        let w := v t + (ε * (k * Real.exp (k * (b - t)))) • n
        z t ∈ Metric.closedBall x R ∧ HasDerivAt z w t ∧
          coordinateBilinear g c (z t) w w < 0 ∧ coordinateBilinear g c (z t) n w < 0 := by
  let K := Metric.closedBall x R
  obtain ⟨κ, hκ, L, hL0, hPush⟩ := chart_causalCone_stable_under_time_push hg hL c n
    (isCompact_closedBall x R) (convex_closedBall x R) hTarget hn
  let k := 1 + (L * ‖n‖ * V) / κ
  have hk : 0 < k := by dsimp only [k]; positivity
  have hkDom : L * ‖n‖ * V ≤ κ * k := by
    dsimp only [k]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hκ.ne']
    linarith
  let G := Real.exp (k * (b - a))
  have hG : 0 < G := Real.exp_pos _
  let D := 1 + G * ‖n‖ + L * G * ‖n‖ * ‖n‖
  have hD : 0 < D := by dsimp only [D]; positivity
  have hD₁ : G * ‖n‖ ≤ D := by dsimp only [D]; linarith [show 0 ≤ L * G * ‖n‖ * ‖n‖ by positivity]
  have hD₂ : L * G * ‖n‖ * ‖n‖ ≤ D := by dsimp only [D]; linarith [show 0 ≤ G * ‖n‖ by positivity]
  refine ⟨k, hk, min (R - r) κ / D, div_pos (lt_min (sub_pos.mpr hRad) hκ) hD, ?_⟩
  intro ε hε hε0 z
  have hεD : ε * D < min (R - r) κ := (lt_div_iff₀ hD).mp hε0
  refine ⟨by simp [z, endpointTimePush], ?_⟩
  intro t ht w
  obtain ⟨hyt, hDeriv, hSelf, hMix, hv⟩ := hpath t ht
  let f := endpointTimePush k b t
  let T := Real.exp (k * (b - t))
  obtain ⟨_, hf0, hP, hf⟩ := endpointTimePush_dominates hk ht.2
  have hTG : T ≤ G := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 b) hk.le)
  have hfT : |f| ≤ T := by
    rw [abs_of_nonpos hf0]
    change -(1 - T) ≤ T
    linarith
  have hDiff : ‖z t - y t‖ = ε * |f| * ‖n‖ := by
    change ‖y t + (ε * f) • n - y t‖ = _
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hε]
  have hDiffG : ‖z t - y t‖ ≤ ε * G * ‖n‖ := by
    rw [hDiff]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfT.trans hTG) hε.le) (norm_nonneg n)
  have hy : y t ∈ K := (Metric.closedBall_subset_closedBall hRad.le) hyt
  have hz : z t ∈ K := by
    apply Metric.mem_closedBall.mpr
    calc
      dist (z t) x ≤ dist (z t) (y t) + dist (y t) x := dist_triangle _ _ _
      _ ≤ ε * D + r := add_le_add
        ((dist_eq_norm (z t) (y t)).trans_le (hDiffG.trans (by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hD₁ hε.le))) hyt
      _ ≤ R := by linarith [hεD.trans_le (min_le_left _ _)]
  have hSmall : L * ‖z t - y t‖ * ‖n‖ ≤ κ := by
    have hEst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDiffG hL0) (norm_nonneg n)
    have hReorder : L * (ε * G * ‖n‖) * ‖n‖ = ε * (L * G * ‖n‖ * ‖n‖) := by ring
    rw [hReorder] at hEst
    exact hEst.trans ((mul_le_mul_of_nonneg_left hD₂ hε.le).trans (hεD.le.trans (min_le_right _ _)))
  have hDom : L * ‖z t - y t‖ * ‖v t‖ ≤ κ * (ε * (k * T)) := by
    rw [hDiff]
    calc
      _ = ε * |f| * (L * ‖n‖ * ‖v t‖) := by ring
      _ ≤ ε * |f| * (κ * k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans hkDom
      _ = ε * κ * (k * |f|) := by ring
      _ ≤ ε * κ * (k * T) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ = _ := by ring
  have hDerivZ : HasDerivAt z w t := hDeriv.add
    (((endpointTimePush_hasDeriv k b t).const_mul ε).smul_const n)
  have hCones := hPush (y t) hy (z t) hz (v t) (ε * (k * T)) (mul_pos hε hP)
    hSelf hMix hSmall hDom
  exact ⟨hz, hDerivZ, hCones⟩

end Burnett.Geometry.FiniteCausalVolume
