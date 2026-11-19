import Burnett.Analysis.SignedFourierWindow.CalderonSplit

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Set Function
open scoped ENNReal

/-- Reconstruction and total bad mass give simultaneous L¹ and L² energy control
for the same complex good part, for every finite positive threshold. -/
theorem good_energy {ι : Type*} [Countable ι] (f g : Space → ℂ) (b : ι → Space → ℂ)
    (hf : Integrable f) (hg : Measurable g) (hb : ∀ i, Integrable (b i))
    (hsplit : ∀ x, g x + ∑' i, b i x = f x)
    (mass : (∑' i, ∫⁻ x, ‖b i x‖ₑ) ≤ 2*∫⁻ x, ‖f x‖ₑ)
    (a : ℝ≥0∞) (ha : a < ⊤) (cap : ∀ᵐ x ∂volume, ‖g x‖ₑ ≤ a*256) :
    Integrable g ∧ (∫⁻ x, ‖g x‖ₑ) ≤ 3*∫⁻ x, ‖f x‖ₑ ∧
    MemLp g 2 volume ∧ (∫⁻ x, ‖g x‖ₑ^2) ≤ (a*768)*∫⁻ x, ‖f x‖ₑ := by
  let M := ∫⁻ x, ‖f x‖ₑ
  have Mfin : M < ⊤ := hf.2
  have point (x : Space) : ‖g x‖ₑ ≤ ‖f x‖ₑ + ∑' i, ‖b i x‖ₑ := by
    have eq := eq_sub_of_add_eq (hsplit x)
    rw [eq]
    rw [sub_eq_add_neg]
    refine (enorm_add_le _ _).trans ?_
    rw [enorm_neg]
    exact add_le_add_left enorm_tsum_le_tsum_enorm _
  have one : (∫⁻ x, ‖g x‖ₑ) ≤ 3*M := by
    refine (lintegral_mono point).trans ?_
    rw [lintegral_add_left' hf.1.enorm,lintegral_tsum (fun i => (hb i).1.enorm)]
    exact (add_le_add_left mass _).trans_eq (by change M + 2*M = 3*M; ring)
  have two : (∫⁻ x, ‖g x‖ₑ^2) ≤ (a*768)*M := by
    calc
      _ ≤ ∫⁻ x, (a*256)*‖g x‖ₑ := lintegral_mono_ae (cap.mono fun x hx => by
        rw [pow_two]; exact mul_le_mul_right' hx _)
      _ = (a*256)*∫⁻ x, ‖g x‖ₑ := lintegral_const_mul _ hg.enorm
      _ ≤ (a*256)*(3*M) := mul_le_mul_left' one _
      _ = _ := by ring
  refine ⟨⟨hg.aestronglyMeasurable,one.trans_lt (ENNReal.mul_lt_top (by norm_num) Mfin)⟩,one,
    ⟨hg.aestronglyMeasurable,?_⟩,two⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
  simp only [ENNReal.toReal_ofNat,ENNReal.rpow_two]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (two.trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ha (by norm_num)) Mfin)).ne

end Burnett.Analysis.SignedFourierWindow
