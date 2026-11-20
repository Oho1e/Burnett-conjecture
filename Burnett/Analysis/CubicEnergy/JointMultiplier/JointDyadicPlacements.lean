import Burnett.Analysis.CubicEnergy.JointMultiplier.JointDyadicWindows
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointKernelSummation
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointSlotExpansion

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset
open scoped ENNReal ContDiff

def shiftWeight (c : ℝ) (j : ℕ) (y : E) : ℝ≥0∞ :=
  ENNReal.ofReal ((1+‖(-c⁻¹) • y‖)^j)

def sumWindowEnorm (f g h a b c : SchwartzMap E ℂ) (u v w t : ℝ) (n : ℕ) (y : Joint) : ℝ≥0∞ :=
  ∫⁻ x : E, ∑ i : Fin n, ‖translatedEntry (dyadicScale t i)
    (windowTest a f (u*dyadicScale t i)) (windowTest b g (v*dyadicScale t i))
    (windowTest c h (w*dyadicScale t i)) y x‖ₑ

private theorem sumWindowEnorm_eq (f g h a b c : SchwartzMap E ℂ) (u v w t : ℝ) (n : ℕ) (y : Joint) :
    sumWindowEnorm f g h a b c u v w t n y =
    ∫⁻ x : E, ∑ i : Fin n, ‖shiftedTest a f u t i y.1 x*
      shiftedTest b g v t i y.2 x*shiftedTest c h w t i 0 x‖ₑ := by
  simp only [sumWindowEnorm,translatedEntry,shiftedTest,smul_zero,sub_zero]

/-- The actual three placements in the joint annulus have two annular
inputs and one low window. The third physical translation is zero. -/
theorem dyadic_three_placements (a d : SchwartzMap E ℂ)
    (hc : HasCompactSupport (a : E → ℂ)) (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (p s z : ℝ) (hp : 1<p) (hs : 1<s) (hz : 1<z) (bal : triBalance p s z) :
    ∃ C₁ C₂ C₃ : ℝ≥0∞, C₁<⊤ ∧ C₂<⊤ ∧ C₃<⊤ ∧
      ∀ (u v w t : ℝ), 0<u → 0<v → 0<w → 0<t → ∀ (n : ℕ) (f g h : SchwartzMap E ℂ) (y : Joint),
      (sumWindowEnorm f g h a a d u v w t n y ≤
        C₁*shiftWeight u 1 y.1*shiftWeight v 1 y.2*triLpMass f g h p s z) ∧
      (sumWindowEnorm f g h d a a u v w t n y ≤
        C₂*shiftWeight u 5 y.1*shiftWeight v 1 y.2*triLpMass f g h p s z) ∧
      (sumWindowEnorm f g h a d a u v w t n y ≤
        C₃*shiftWeight u 1 y.1*shiftWeight v 5 y.2*triLpMass f g h p s z) := by
  have bal₂ : triBalance s z p := by simpa only [triBalance,add_assoc,add_left_comm,add_comm] using bal
  have bal₃ : triBalance p z s := by simpa only [triBalance,add_assoc,add_left_comm,add_comm] using bal
  obtain ⟨C₁,f₁,H₁⟩ := dyadic_two_high_one_low a a d hc hc cut cut p s z hp hs hz bal
  obtain ⟨C₂,f₂,H₂⟩ := dyadic_two_high_one_low a a d hc hc cut cut s z p hs hz hp bal₂
  obtain ⟨C₃,f₃,H₃⟩ := dyadic_two_high_one_low a a d hc hc cut cut p z s hp hz hs bal₃
  refine ⟨C₁,C₂,C₃,f₁,f₂,f₃,?_⟩
  intro u v w t hu hv hw ht n f g h y
  have perm₂ : triLpMass g h f s z p = triLpMass f g h p s z := by unfold triLpMass; ac_rfl
  have perm₃ : triLpMass f h g p z s = triLpMass f g h p s z := by unfold triLpMass; ac_rfl
  have e₂ (x : E) (i : Fin n) :
      shiftedTest d f u t i y.1 x * shiftedTest a g v t i y.2 x * shiftedTest a h w t i 0 x =
      shiftedTest a g v t i y.2 x * shiftedTest a h w t i 0 x * shiftedTest d f u t i y.1 x := by ring
  have e₃ (x : E) (i : Fin n) :
      shiftedTest a f u t i y.1 x * shiftedTest d g v t i y.2 x * shiftedTest a h w t i 0 x =
      shiftedTest a f u t i y.1 x * shiftedTest a h w t i 0 x * shiftedTest d g v t i y.2 x := by ring
  have b₁ := H₁ u v w t hu hv hw ht y.1 y.2 0 n f g h
  have b₂ := H₂ v w u t hv hw hu ht y.2 0 y.1 n g h f
  have b₃ := H₃ u w v t hu hw hv ht y.1 0 y.2 n f h g
  simp only [sumWindowEnorm_eq,e₂,e₃,shiftWeight,pow_one]
  refine ⟨?_,?_,?_⟩
  · simpa only [smul_zero,norm_zero,add_zero,one_pow,ENNReal.ofReal_one,mul_one] using b₁
  · simp only [smul_zero,norm_zero,add_zero,ENNReal.ofReal_one,mul_one,perm₂] at b₂
    exact b₂.trans_eq (by ac_rfl)
  · simpa only [smul_zero,norm_zero,add_zero,ENNReal.ofReal_one,mul_one,perm₃] using b₃

end Burnett.A02.FrequencySplit
