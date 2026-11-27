import Burnett.Analysis.PrincipalEnergy.Freezing.PatchIntegralLpBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.A02.FrequencySplit
open scoped ENNReal

/-- A physically absolutely summable family transfers the order-zero bound
on its actual terms to their pointwise sum. -/
theorem patch_summed_L3_bound {ι : Type} [Countable ι]
    (G : ι → E → ℂ) (A : E → ℂ) (hA : Continuous A)
    (sum : ∀ x, A x = ∑' k, G k x)
    (w : ι → ℝ) (hw : Summable w) (w0 : ∀ k, 0 ≤ w k)
    (M : ℝ) (major : ∀ k x, ‖G k x‖ ≤ w k * M)
    (V : ℝ≥0∞) (hV : V < ⊤)
    (bound : ∀ k, MemLp (G k) (ENNReal.ofReal 3) volume ∧
      eLpNorm (G k) (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (w k) * V) :
    MemLp A (ENNReal.ofReal 3) volume ∧
      eLpNorm A (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (∑' k, w k) * V := by
  have conjugate : Real.HolderConjugate 3 (3 / 2) := by constructor <;> norm_num
  apply CMBilinearDual.memLp_of_schwartz_pairing conjugate hA
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV).ne
  intro φ
  let p := ENNReal.ofReal (3 / 2)
  let P := eLpNorm (φ : E → ℂ) p volume
  let L (k : ι) (x : E) := G k x * φ x
  have hL (k : ι) := energy_integral_three_three_halves (bound k).1 (φ.memLp p volume)
  have abs (k : ι) : (∫ x, ‖L k x‖) ≤ w k * (M * ∫ x, ‖φ x‖) := by
    refine (integral_mono (hL k).1.norm (φ.integrable.norm.const_mul (w k * M)) (fun x => ?_)).trans_eq ?_
    · exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (major k x) (norm_nonneg _))
    · rw [integral_const_mul, mul_assoc]
  have summable : Summable (fun k => ∫ x, ‖L k x‖) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg (fun x => norm_nonneg (L k x))) abs (hw.mul_right _)
  have pair (k : ι) : ‖∫ x, L k x‖ₑ ≤ ENNReal.ofReal (w k) * (V * P) :=
    (hL k).2.trans ((mul_le_mul_right' (bound k).2 _).trans_eq (mul_assoc _ _ _))
  calc
    _ = ‖∑' k, ∫ x, L k x‖ₑ := by
      congr 1
      rw [integral_tsum_of_summable_integral_norm (fun k => (hL k).1) summable]
      apply integral_congr_ae
      filter_upwards with x
      rw [sum x]
      exact (tsum_mul_right).symm
    _ ≤ ∑' k, ‖∫ x, L k x‖ₑ := enorm_tsum_le_tsum_enorm
    _ ≤ ∑' k, ENNReal.ofReal (w k) * (V * P) := ENNReal.tsum_le_tsum pair
    _ = _ := by rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg w0 hw, mul_assoc]

end Burnett.A03
