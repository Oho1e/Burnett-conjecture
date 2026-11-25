import Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
import Burnett.Analysis.Fourier.Projection

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A07

open Burnett.A02.FrequencySplit Burnett.A06 Burnett.Fourier MeasureTheory Filter ContinuousLinearMap
open scoped ENNReal ComplexConjugate

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Actual multiplication of a complex Schwartz field by a real Schwartz coefficient. -/
def realSchwartzMultiply (d : SchwartzMap E ℝ) (v : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.bilinLeftCLM (lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip d.hasTemperateGrowth v

@[simp] theorem realSchwartzMultiply_apply (d : SchwartzMap E ℝ) (v : SchwartzMap E ℂ) (x : E) :
    realSchwartzMultiply d v x = (d x : ℂ) * v x := rfl

/-- The same real coefficient as actual pointwise multiplication on L². -/
def realSchwartzCoefficient (d : SchwartzMap E ℝ) : BoundedSymbol E where
  toFun x := d x
  measurable := (Complex.continuous_ofReal.comp d.continuous).aestronglyMeasurable
  bound := SchwartzMap.seminorm ℝ 0 0 d
  bound_nonneg := apply_nonneg _ _
  norm_le x := by simpa only [Complex.norm_real] using d.norm_le_seminorm ℝ x

private theorem inner_realSchwartzCoefficient (d : SchwartzMap E ℝ) (w : SchwartzMap E ℂ)
    (y : FirstOrderLp 2) :
    inner ℂ (w.toLp 2 volume) (symbolCLM (realSchwartzCoefficient d) y) =
      inner ℂ ((realSchwartzMultiply d w).toLp 2 volume) y := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [w.coeFn_toLp 2 volume, (realSchwartzMultiply d w).coeFn_toLp 2 volume,
    symbolL2_ae (realSchwartzCoefficient d) y] with x hx hw hd
  change inner ℂ ((w.toLp 2 volume) x) (symbolL2 (realSchwartzCoefficient d) y x) =
    inner ℂ (((realSchwartzMultiply d w).toLp 2 volume) x) (y x)
  rw [hx, hw, hd, realSchwartzMultiply_apply]
  simp only [RCLike.inner_apply', map_mul, realSchwartzCoefficient, Complex.conj_ofReal]
  ring

/-- A real coefficient on the physical output moves onto the same conjugate
Schwartz test. The sign is that of `[d,T] = d T - T d`. -/
theorem schwartzHighSlotCommutator_pair_eq
    (b : Joint → ℂ) (d : SchwartzMap E ℝ) (v : SchwartzMap E ℂ)
    (T Td : FirstOrderLp 4 →L[ℂ] FirstOrderLp 2)
    (hT : ∀ f w : SchwartzMap E ℂ, inner ℂ (w.toLp 2 volume) (T (f.toLp 4 volume)) = radianHighPair b f v w)
    (hTd : ∀ f w : SchwartzMap E ℂ, inner ℂ (w.toLp 2 volume) (Td (f.toLp 4 volume)) =
      radianHighPair b f (realSchwartzMultiply d v) w)
    (f w : SchwartzMap E ℂ) :
    inner ℂ (w.toLp 2 volume) (symbolCLM (realSchwartzCoefficient d) (T (f.toLp 4 volume)) - Td (f.toLp 4 volume)) =
      -radianHighCommutatorPair b d f v w := by
  rw [inner_sub_right, inner_realSchwartzCoefficient, hT, hTd, radianHighCommutatorPair, neg_sub]
  rfl

/-- The original three-Schwartz-test bound controls the actual paired
high-slot commutator on the whole low L⁴ space. -/
theorem schwartzHighSlotCommutator_L4_to_L2_norm_le
    (b : Joint → ℂ) (d : SchwartzMap E ℝ) (v : SchwartzMap E ℂ)
    (T Td : FirstOrderLp 4 →L[ℂ] FirstOrderLp 2)
    (hT : ∀ f w : SchwartzMap E ℂ, inner ℂ (w.toLp 2 volume) (T (f.toLp 4 volume)) = radianHighPair b f v w)
    (hTd : ∀ f w : SchwartzMap E ℂ, inner ℂ (w.toLp 2 volume) (Td (f.toLp 4 volume)) =
      radianHighPair b f (realSchwartzMultiply d v) w)
    {J : ℝ} (hJ : 0 ≤ J)
    (hBound : ∀ f w : SchwartzMap E ℂ, ‖radianHighCommutatorPair b d f v w‖ ≤
      J * ‖f.toLp 4 volume‖ * ‖w.toLp 2 volume‖)
    (H : FirstOrderLp 4) :
    ‖symbolCLM (realSchwartzCoefficient d) (T H) - Td H‖ ≤ J * ‖H‖ := by
  let P := (symbolCLM (realSchwartzCoefficient d)).comp T - Td
  have hLow (H : FirstOrderLp 4) (w : SchwartzMap E ℂ) :
      ‖inner ℂ (w.toLp 2 volume) (P H)‖ ≤ J * ‖H‖ * ‖w.toLp 2 volume‖ := by
    refine (CMBilinearDual.schwartz_toLp_denseRange 4 (by norm_num)).induction_on H ?_ ?_
    · exact isClosed_le (continuous_const.inner P.continuous).norm
        ((continuous_const.mul continuous_norm).mul continuous_const)
    · intro f
      change ‖inner ℂ (w.toLp 2 volume)
        (symbolCLM (realSchwartzCoefficient d) (T (f.toLp 4 volume)) - Td (f.toLp 4 volume))‖ ≤ _
      rw [schwartzHighSlotCommutator_pair_eq b d v T Td hT hTd f w, norm_neg]
      exact hBound f w
  let x := P H
  have hTest (w : FirstOrderLp 2) : ‖inner ℂ w x‖ ≤ J * ‖H‖ * ‖w‖ := by
    refine (CMBilinearDual.schwartz_toLp_denseRange 2 (by norm_num)).induction_on w ?_ (hLow H)
    exact isClosed_le (continuous_id.inner continuous_const).norm (continuous_const.mul continuous_norm)
  have diagonal := hTest x
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x), pow_two] at diagonal
  change ‖x‖ ≤ J * ‖H‖
  by_cases hz : ‖x‖ = 0
  · rw [hz]
    exact mul_nonneg hJ (norm_nonneg _)
  · exact le_of_mul_le_mul_right diagonal (lt_of_le_of_ne (norm_nonneg x) (fun h => hz h.symm))

end Burnett.A07
