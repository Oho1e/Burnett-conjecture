import Burnett.Analysis.AllScaleTransfer.RadianTrilinearChange
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Burnett.A05

open MeasureTheory Filter
open Burnett.A02.FrequencySplit (E Joint radianWeight tau)
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight
  integrable_radianTrilinearWeight_of_bounded)

/-- Identification of an absolutely controlled symbol expansion with the
same trilinear form. The majorant is integrated against the actual
three Fourier factors, including the retained negative-sum frequency. -/
theorem radianTrilinearForm_hasSum_of_symbol_expansion {ι : Type*} [Countable ι]
    (F : ι → Joint → ℂ) (m : Joint → ℂ) (b : ι → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (F i) volume)
    (hb : Summable b) (hbound : ∀ i p, ‖F i p‖ ≤ b i)
    (hsum : ∀ᵐ p ∂(volume : Measure Joint), HasSum (fun i => F i p) (m p))
    (f g h : SchwartzMap E ℂ) :
    HasSum (fun i => radianTrilinearForm (F i) f g h) (radianTrilinearForm m f g h) := by
  let K := radianWeight (fun _ => 1) f g h
  have hone : radianTrilinearWeight (fun _ => (1 : ℂ)) f g h = K := by
    funext p
    change (1 : ℂ) * K p = K p
    exact one_mul _
  have hK : Integrable K := by
    rw [← hone]
    exact integrable_radianTrilinearWeight_of_bounded (fun _ => (1 : ℂ))
      aestronglyMeasurable_const 1 (fun p => norm_one.le) f g h
  have hMass : Integrable (fun p : Joint => ∑' i, b i * ‖K p‖) := by
    have eq : (fun p : Joint => ∑' i, b i * ‖K p‖) = (fun p => (∑' i, b i) * ‖K p‖) := by
      funext p
      exact hb.tsum_mul_right _
    rw [eq]
    exact hK.norm.const_mul _
  have hIntegral : HasSum (fun i => ∫ p, F i p * K p) (∫ p, m p * K p) := by
    apply hasSum_integral_of_dominated_convergence (fun i p => b i * ‖K p‖)
    · exact fun i => (hf i).mul hK.1
    · intro i
      filter_upwards with p
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound i p) (norm_nonneg _)
    · exact Eventually.of_forall (fun p => hb.mul_right ‖K p‖)
    · exact hMass
    · filter_upwards [hsum] with p hp
      exact hp.mul_right (K p)
  exact hIntegral.const_smul ((tau ^ 8)⁻¹ : ℝ)

end Burnett.A05
