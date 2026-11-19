import Burnett.Analysis.SignedFourierWindow.KernelTranslation

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal
open MeasureTheory Set

theorem shiftedSpatialKernel_integrable (φ : SchwartzMap Space ℂ) {s : ℝ} (hs : 0<s) (q : Space) :
    Integrable (shiftedSpatialKernel φ s q) := by
  have ht := measurePreserving_add_right (volume : Measure Space) q
  have h : Integrable (fun z : Space => φ (z+q)) :=
    (ht.integrable_comp_emb (Homeomorph.addRight q).measurableEmbedding).2 φ.integrable
  exact (h.comp_smul (inv_ne_zero hs.ne')).smul _

private theorem translated_difference_integral (φ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) (q h : Space) :
    (∫ z : Space, ‖shiftedSpatialKernel φ s q (z-h) - shiftedSpatialKernel φ s q z‖) =
      ∫ z : Space, ‖φ (z - s⁻¹ • h) - φ z‖ := by
  let F := fun z : Space => ‖φ (z - s⁻¹ • h) - φ z‖
  let G := fun z : Space => F (z+q)
  have H (z : Space) : ‖shiftedSpatialKernel φ s q (z-h) - shiftedSpatialKernel φ s q z‖ =
      (s^4)⁻¹ * G (s⁻¹ • z) := by
    simp only [shiftedSpatialKernel,G,F,smul_sub]
    rw [sub_add_eq_add_sub,← smul_sub,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (pow_pos hs _))]
  simp_rw [H]
  rw [integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg volume G hs.le,
    show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin,smul_eq_mul,← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ hs.ne'),one_mul]
  exact (measurePreserving_add_right (volume : Measure Space) q).integral_comp
    (Homeomorph.addRight q).measurableEmbedding F

/-- Large spatial scales have translation difference of first order, uniformly
in the Fourier modulation because integration is over the whole space. -/
theorem large_scale_difference (φ : SchwartzMap Space ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (q h : Space), 0<s → ‖h‖ ≤ s →
      (∫ z : Space, ‖shiftedSpatialKernel φ s q (z-h) - shiftedSpatialKernel φ s q z‖) ≤ C*(‖h‖/s) := by
  obtain ⟨C,hC,hφ⟩ := schwartz_translation_L1 φ
  refine ⟨C,hC,?_⟩
  intro s q h hs hh
  have he : ‖s⁻¹ • h‖ = ‖h‖ / s := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),inv_mul_eq_div]
  rw [translated_difference_integral φ s hs q h,← he]
  exact hφ _ (he.trans_le ((div_le_one hs).mpr hh))

private theorem exterior_shift_le (K : Space → ℂ) (hK : Integrable K) (h : Space) :
    (∫ z in {z : Space | 2*‖h‖ ≤ ‖z‖}, ‖K (z-h)‖) ≤ ∫ z in {z : Space | ‖h‖ ≤ ‖z‖}, ‖K z‖ := by
  let S := {z : Space | 2*‖h‖ ≤ ‖z‖}
  let T := {z : Space | ‖h‖ ≤ ‖z‖}
  have hmS : MeasurableSet S := isClosed_le continuous_const continuous_norm |>.measurableSet
  have hmT : MeasurableSet T := isClosed_le continuous_const continuous_norm |>.measurableSet
  let ht := measurePreserving_add_right (volume : Measure Space) (-h)
  have shift {f : Space → ℝ} (hf : Integrable f) : Integrable (fun z => f (z-h)) := by
    simpa only [sub_eq_add_neg] using (ht.integrable_comp_emb (Homeomorph.addRight (-h)).measurableEmbedding).2 hf
  change (∫ z in S, ‖K (z-h)‖) ≤ ∫ z in T, ‖K z‖
  rw [← integral_indicator hmS,← integral_indicator hmT]
  have hle (z : Space) : S.indicator (fun z => ‖K (z-h)‖) z ≤ T.indicator (fun z => ‖K z‖) (z-h) := by
    by_cases hz : z ∈ S
    · have htri : ‖z‖ ≤ ‖z-h‖+‖h‖ := by simpa using norm_add_le (z-h) h
      have H : z-h ∈ T := by change ‖h‖ ≤ ‖z-h‖; change 2*‖h‖ ≤ ‖z‖ at hz; linarith
      rw [indicator_of_mem hz,indicator_of_mem H]
    · rw [indicator_of_notMem hz]
      exact indicator_nonneg (fun z _ => norm_nonneg _) _
  refine (integral_mono ((shift hK.norm).indicator hmS) (shift (hK.norm.indicator hmT)) hle).trans_eq ?_
  simpa only [sub_eq_add_neg] using ht.integral_comp (Homeomorph.addRight (-h)).measurableEmbedding
    (T.indicator fun z => ‖K z‖)

/-- The small-scale part is estimated away from the doubled exclusion ball.
The right side decays like s/‖h‖, including after the spatial translation. -/
theorem exterior_difference_tail (φ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) (q h : Space) (hh : 0<‖h‖) :
    (∫ z in {z : Space | 2*‖h‖ ≤ ‖z‖}, ‖shiftedSpatialKernel φ s q (z-h) - shiftedSpatialKernel φ s q z‖) ≤
      2*(s/‖h‖)*((∫ z : Space, ‖z‖*‖φ z‖)+‖q‖*(∫ z : Space, ‖φ z‖)) := by
  let K := shiftedSpatialKernel φ s q
  let S := {z : Space | 2*‖h‖ ≤ ‖z‖}
  let T := {z : Space | ‖h‖ ≤ ‖z‖}
  have hk : Integrable K := shiftedSpatialKernel_integrable φ hs q
  have hk' : Integrable (fun z : Space => K (z-h)) := by
    simpa only [sub_eq_add_neg] using ((measurePreserving_add_right (volume : Measure Space) (-h)).integrable_comp_emb
      (Homeomorph.addRight (-h)).measurableEmbedding).2 hk
  have sub : S ⊆ T := fun z hz => show ‖h‖ ≤ ‖z‖ from by change 2*‖h‖ ≤ ‖z‖ at hz; linarith
  have here : (∫ z in S, ‖K z‖) ≤ ∫ z in T, ‖K z‖ :=
    setIntegral_mono_set hk.norm.integrableOn (Filter.Eventually.of_forall fun z => norm_nonneg _) (Filter.Eventually.of_forall sub)
  have there := exterior_shift_le K hk h
  have tail := shifted_spatial_tail φ s hs q ‖h‖ hh
  change (∫ z in S, ‖K (z-h)-K z‖) ≤ _
  calc
    _ ≤ ∫ z in S, ‖K (z-h)‖+‖K z‖ :=
      integral_mono (hk'.sub hk).norm.integrableOn (hk'.norm.add hk.norm).integrableOn (fun _ => norm_sub_le _ _)
    _ = (∫ z in S, ‖K (z-h)‖) + (∫ z in S, ‖K z‖) := integral_add hk'.norm.integrableOn hk.norm.integrableOn
    _ ≤ (∫ z in T, ‖K z‖) + (∫ z in T, ‖K z‖) := add_le_add there here
    _ ≤ _ := by dsimp only [T,K]; linarith

end Burnett.Analysis.SignedFourierWindow
