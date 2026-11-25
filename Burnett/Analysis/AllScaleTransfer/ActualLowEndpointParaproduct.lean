import Burnett.Analysis.AllScaleTransfer.LowEndpointWindows
import Burnett.Analysis.AllScaleTransfer.ActualRadialWindowSum

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.A05
open Burnett.Analysis.ShiftedFourierWindow

open MeasureTheory Finset
open Burnett.A02.FrequencySplit
open scoped ENNReal BigOperators

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- The actual low-pass/high-annulus/thick-output paraproduct at arbitrary
finite integer scales. The inputs of the first two slots may already
include the angular operators. -/
theorem integer_low_endpoint_paraproduct_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gap n : ℕ) (j : Fin n ↪ ℤ) (f g w : SchwartzMap E ℂ),
        let scale (i : Fin n) : ℝ := (2 : ℝ)^(-j i) * tau
        let T (i : Fin n) (x : E) :=
          shiftedWindowOperator endpointLowProfile f ((2 : ℝ)^gap * scale i) 0 x *
          shiftedWindowOperator endpointHighProfile g (scale i) 0 x *
          shiftedWindowOperator endpointThickProfile w (scale i) 0 x
        (∀ i, Integrable (T i)) ∧
          ‖∑ i, ∫ x, T i x‖ ≤ C *
            ‖f.toLp (ENNReal.ofReal 3) volume‖ * ‖g.toLp (ENNReal.ofReal 3) volume‖ *
            ‖w.toLp (ENNReal.ofReal 3) volume‖ := by
  classical
  choose constants finite window using fun k : Fin 6 =>
    integer_radial_window_trilinear_bound endpointHighProfile (endpointThickPart k) endpointLowProfile
      endpointHighProfile_properties.2.1 (endpointThickPart_properties k).1
      endpointHighProfile_properties.2.2 (endpointThickPart_properties k).2
  let C : ℝ≥0∞ := ∑ k, constants k
  have hC : C < ⊤ := ENNReal.sum_lt_top.2 (fun k _ => finite k)
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro gap n j f g w scale T
  have htau : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have scale_pos (i : Fin n) : 0 < scale i :=
    mul_pos (by positivity : 0 < (2 : ℝ)^(-j i)) htau
  let X (k : Fin 6) (i : Fin n) (x : E) :=
    shiftedWindowOperator endpointHighProfile g (scale i) 0 x *
    shiftedWindowOperator (endpointThickPart k) w (endpointPartScale k*scale i) 0 x *
    shiftedWindowOperator endpointLowProfile f ((2 : ℝ)^gap*scale i) 0 x
  have hEach (k : Fin 6) :
      (∀ i, Integrable (X k i)) ∧
        ‖∑ i, ∫ x, X k i x‖ₑ ≤ constants k * triLpMass g w f 3 3 3 := by
    have H := window k tau (endpointPartScale k*tau) htau (mul_pos (endpointPartScale_pos k) htau)
      0 0 n j (fun i => (2 : ℝ)^gap*scale i) (fun i => mul_pos (by positivity) (scale_pos i))
      g w f
    have dilation (i : Fin n) :
        (2 : ℝ)^(-j i) * (endpointPartScale k*tau) = endpointPartScale k*scale i := by
      dsimp only [scale]
      ring
    simpa only [dilation, scale, X, norm_zero, add_zero, ENNReal.ofReal_one, mul_one] using H
  have split (i : Fin n) : T i = fun x => ∑ k : Fin 6, X k i x := by
    funext x
    dsimp only [T]
    rw [shiftedEndpointThickWindow_six_parts w (scale_pos i) x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [X]
    ring
  refine ⟨fun i => ?_, ?_⟩
  · rw [split i]
    exact integrable_finset_sum _ (fun k _ => (hEach k).1 i)
  have regroup :
      (∑ i, ∫ x, T i x) = ∑ k : Fin 6, ∑ i, ∫ x, X k i x := by
    have term (i : Fin n) : (∫ x, T i x) = ∑ k : Fin 6, ∫ x, X k i x := by
      rw [split i, integral_finset_sum _ (fun k _ => (hEach k).1 i)]
    simp_rw [term]
    rw [Finset.sum_comm]
  have hBound : ‖∑ i, ∫ x, T i x‖ₑ ≤ C * triLpMass f g w 3 3 3 := by
    rw [regroup]
    calc
      _ ≤ ∑ k : Fin 6, ‖∑ i, ∫ x, X k i x‖ₑ := enorm_sum_le _ _
      _ ≤ ∑ k : Fin 6, constants k * triLpMass g w f 3 3 3 :=
        Finset.sum_le_sum fun k _ => (hEach k).2
      _ = _ := by rw [← Finset.sum_mul]; unfold C triLpMass; ac_rfl
  have hn (v : SchwartzMap E ℂ) : eLpNorm (v : E → ℂ) (ENNReal.ofReal 3) volume < ⊤ :=
    (v.memLp (ENNReal.ofReal 3) volume).eLpNorm_lt_top
  have hm : triLpMass f g w 3 3 3 < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (hn f) (hn g)) (hn w)
  have result := ENNReal.toReal_mono (ENNReal.mul_lt_top hC hm).ne hBound
  simpa only [toReal_enorm, triLpMass, ENNReal.toReal_mul, SchwartzMap.norm_toLp, mul_assoc] using result

end Burnett.A05
