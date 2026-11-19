import Burnett.Analysis.ShiftedFourierWindow.LowPassFourier

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal
open Burnett.Analysis.ShiftedFourierWindow
open MeasureTheory

def shiftedSpatialKernel (φ : SchwartzMap Space ℂ) (s : ℝ) (q z : Space) : ℂ :=
  (s^4)⁻¹ • φ (s⁻¹ • z + q)

private theorem translated_first_moment (φ : SchwartzMap Space ℂ) (q : Space) :
    Integrable (fun z : Space => ‖z‖ * ‖φ (z+q)‖) ∧
    (∫ z : Space, ‖z‖ * ‖φ (z+q)‖) ≤
      (∫ z : Space, ‖z‖ * ‖φ z‖) + ‖q‖ * ∫ z : Space, ‖φ z‖ := by
  let F := fun z : Space => ‖z‖ * ‖φ z‖ + ‖q‖ * ‖φ z‖
  have ht := measurePreserving_add_right (volume : Measure Space) q
  have hi : Integrable (fun z : Space => ‖z‖ * ‖φ z‖) := by simpa using φ.integrable_pow_mul volume 1
  have hj : Integrable (fun z : Space => ‖q‖ * ‖φ z‖) := φ.integrable.norm.const_mul _
  have hF : Integrable F := hi.add hj
  have hshift : Integrable (fun z : Space => F (z+q)) :=
    (ht.integrable_comp_emb (Homeomorph.addRight q).measurableEmbedding).2 hF
  have hle (z : Space) : ‖z‖ * ‖φ (z+q)‖ ≤ F (z+q) := by
    have h : ‖z‖ ≤ ‖z+q‖ + ‖q‖ := by simpa using norm_sub_le (z+q) q
    simpa [F,add_mul] using mul_le_mul_of_nonneg_right h (norm_nonneg (φ (z+q)))
  have actual : Integrable (fun z : Space => ‖z‖ * ‖φ (z+q)‖) := hshift.mono'
    (by fun_prop) (Filter.Eventually.of_forall fun z => by simpa [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hle z)
  refine ⟨actual,(integral_mono actual hshift hle).trans_eq ?_⟩
  have he := ht.integral_comp (Homeomorph.addRight q).measurableEmbedding F
  calc
    _ = ∫ z, F z := he
    _ = _ := by simp only [F,integral_add hi hj,integral_const_mul]

/-- The off-ball mass of the physically normalized translated Schwartz kernel.
The first moment controls the ultraviolet tail uniformly in the starting scale. -/
theorem shifted_spatial_tail (φ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) (q : Space) (d : ℝ) (hd : 0<d) :
    (∫ z in {z : Space | d ≤ ‖z‖}, ‖shiftedSpatialKernel φ s q z‖) ≤
      (s/d) * ((∫ z : Space, ‖z‖ * ‖φ z‖) + ‖q‖ * ∫ z : Space, ‖φ z‖) := by
  let F := fun z : Space => ‖z‖ * ‖φ (z+q)‖
  obtain ⟨hF,hb⟩ := translated_first_moment φ q
  have he (z : Space) : ‖z‖ * ‖shiftedSpatialKernel φ s q z‖ = (s/(s^4))*F (s⁻¹ • z) := by
    simp only [F,shiftedSpatialKernel,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),
      abs_of_pos (inv_pos.mpr (pow_pos hs 4))]
    field_simp
  have hI : Integrable (fun z : Space => ‖z‖ * ‖shiftedSpatialKernel φ s q z‖) := by
    simp_rw [he]
    exact (hF.comp_smul (inv_ne_zero hs.ne')).const_mul _
  have moment : (∫ z : Space, ‖z‖ * ‖shiftedSpatialKernel φ s q z‖) ≤
      s*((∫ z : Space, ‖z‖ * ‖φ z‖) + ‖q‖ * ∫ z : Space, ‖φ z‖) := by
    simp_rw [he]
    rw [integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg volume F hs.le,
      show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin,smul_eq_mul,← mul_assoc,
      div_mul_cancel₀ _ (pow_ne_zero _ hs.ne')]
    exact mul_le_mul_of_nonneg_left hb hs.le
  have hK : Integrable (fun z : Space => ‖shiftedSpatialKernel φ s q z‖) := by
    let ht := measurePreserving_add_right (volume : Measure Space) q
    have h : Integrable (fun z : Space => ‖φ (z+q)‖) :=
      (ht.integrable_comp_emb (Homeomorph.addRight q).measurableEmbedding).2 φ.integrable.norm
    simpa only [shiftedSpatialKernel,norm_smul] using
      (h.comp_smul (inv_ne_zero hs.ne')).const_mul ‖(s^4)⁻¹‖
  let S := {z : Space | d ≤ ‖z‖}
  have hm : MeasurableSet S := isClosed_le continuous_const continuous_norm |>.measurableSet
  have upper : d*(∫ z in S, ‖shiftedSpatialKernel φ s q z‖) ≤ ∫ z : Space, ‖z‖*‖shiftedSpatialKernel φ s q z‖ := by
    rw [← integral_const_mul]
    exact (setIntegral_mono_on (hK.const_mul _).integrableOn hI.integrableOn hm
      (fun z hz => mul_le_mul_of_nonneg_right hz (norm_nonneg _))).trans
        (setIntegral_le_integral hI (Filter.Eventually.of_forall fun z => mul_nonneg (norm_nonneg z) (norm_nonneg _)))
  have bound := upper.trans moment
  change (∫ z in S, ‖shiftedSpatialKernel φ s q z‖) ≤ _
  rw [div_mul_eq_mul_div,le_div_iff₀ hd,mul_comm _ d]
  exact bound

end Burnett.Analysis.SignedFourierWindow
