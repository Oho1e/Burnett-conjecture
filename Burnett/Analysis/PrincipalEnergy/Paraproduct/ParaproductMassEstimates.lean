import Burnett.Analysis.PrincipalEnergy.Paraproduct.CompactWaveletConvolution

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Function
open scoped NNReal

private theorem waveletKernel_norm_mass (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) :
    (∫ z, ‖compactWaveletKernel ψ s z‖) = ∫ z, ‖ψ z‖ := by
  simp only [compactWaveletKernel,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _))]
  rw [integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg volume (fun z => ‖ψ z‖) hs.le,
    finrank_euclideanSpace_fin,smul_eq_mul,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 4 hs.ne'),one_mul]

/-- The physical rescaled convolution has the same Young L¹ bound at every scale. -/
theorem compactWaveletAction_L1_bound (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    {f : Space → ℂ} (hf : Integrable f volume) :
    (∫ x, ‖compactWaveletAction ψ s f x‖) ≤ (∫ z, ‖ψ z‖)*(∫ y, ‖f y‖) := by
  let K := compactWaveletKernel ψ s
  have hK : Integrable K (volume : Measure Space) := (ψ.integrable.comp_smul (inv_ne_zero hs.ne')).smul _
  have hProd : Integrable (uncurry (fun x y => ‖K (x-y)‖*‖f y‖))
      ((volume : Measure Space).prod volume) :=
    (measurePreserving_sub_prod (volume : Measure Space) volume).integrable_comp_of_integrable
      (hK.norm.mul_prod hf.norm)
  have hIt (y : Space) : (∫ x, ‖K (x-y)‖*‖f y‖) = (∫ z, ‖ψ z‖)*‖f y‖ := by
    rw [integral_mul_const]
    have hTx : MeasurePreserving (fun x : Space => x-y) volume volume := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure Space) (-y)
    rw [← integral_map (f := fun z => ‖K z‖) hTx.measurable.aemeasurable
      (by rw [hTx.map_eq]; exact hK.norm.aestronglyMeasurable),
      hTx.map_eq, show (∫ z, ‖K z‖) = ∫ z, ‖ψ z‖ from waveletKernel_norm_mass ψ s hs]
  calc
    _ ≤ ∫ x, ∫ y, ‖K (x-y)‖*‖f y‖ := integral_mono
      (compactWaveletAction_integrable ψ s hs hf).norm hProd.integral_prod_left fun x => by
        simpa only [compactWaveletAction,norm_mul] using
          (norm_integral_le_integral_norm (f := fun y => K (x-y)*f y))
    _ = ∫ y, ∫ x, ‖K (x-y)‖*‖f y‖ := integral_integral_swap hProd
    _ = _ := by simp_rw [hIt]; rw [integral_const_mul]

/-- Bounded inputs are controlled by the unscaled L¹ mass of the window. -/
theorem compactWaveletAction_norm_le_L1Mass_mul (ψ : SchwartzMap Space ℂ)
    (s : ℝ) (hs : 0<s) {f : Space → ℂ} {C : ℝ} (hC : ∀ y, ‖f y‖≤C) (x : Space) :
    ‖compactWaveletAction ψ s f x‖ ≤ C*(∫ z, ‖ψ z‖) := by
  let K := compactWaveletKernel ψ s
  have hK : Integrable K (volume : Measure Space) :=
    (ψ.integrable.comp_smul (inv_ne_zero hs.ne')).smul _
  have hTx := (volume : Measure Space).measurePreserving_sub_left x
  have hKt : Integrable (fun y => K (x-y)) (volume : Measure Space) :=
    hTx.integrable_comp_of_integrable hK
  have hMass : (∫ y, ‖K (x-y)‖) = ∫ z, ‖ψ z‖ := by
    rw [← integral_map (f := fun z => ‖K z‖) hTx.measurable.aemeasurable
      (by rw [hTx.map_eq]; exact hK.norm.aestronglyMeasurable),hTx.map_eq]
    exact waveletKernel_norm_mass ψ s hs
  calc
    _ ≤ ∫ y, ‖K (x-y)*f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C*‖K (x-y)‖ := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (hKt.norm.const_mul C) (Eventually.of_forall fun y => by
        change ‖K (x-y)*f y‖ ≤ C*‖K (x-y)‖
        rw [norm_mul,mul_comm ‖K (x-y)‖]
        exact mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _))
    _ = _ := by rw [integral_const_mul,hMass]

/-- A compact mean-zero filter gains one length factor on a Lipschitz input. -/
theorem compactWaveletAction_Lipschitz_small_scale_bound (ψ : SchwartzMap Space ℂ)
    (hψ : ∀ z, 1<‖z‖ → ψ z=0) (hψ₀ : (∫ z, ψ z)=0)
    (s : ℝ) (hs : 0<s) {b : Space → ℂ} (hb : Integrable b volume)
    (L : NNReal) (hLip : LipschitzWith L b) (x : Space) :
    ‖compactWaveletAction ψ s b x‖ ≤ ((L:ℝ)*s)*(∫ z, ‖ψ z‖) := by
  let K (y : Space) := compactWaveletKernel ψ s (x-y)
  have hW : Integrable (compactWaveletKernel ψ s) (volume : Measure Space) :=
    (ψ.integrable.comp_smul (inv_ne_zero hs.ne')).smul _
  have hTx := (volume : Measure Space).measurePreserving_sub_left x
  have hK : Integrable K (volume : Measure Space) := hTx.integrable_comp_of_integrable hW
  have hA : ∀ y : Space, ‖K y‖ ≤ |(s^4)⁻¹| * SchwartzMap.seminorm ℝ 0 0 ψ := by
    intro y
    dsimp only [K,compactWaveletKernel]
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ ψ _) (abs_nonneg _)
  have hB : Integrable (fun y => K y*b y) (volume : Measure Space) := by
    simpa only [mul_comm] using hb.bdd_mul hK.aestronglyMeasurable ⟨_,hA⟩
  have hC := hK.mul_const (b x)
  have hMass : (∫ y, K y) = 0 := by
    simpa only [compactWaveletAction,mul_one,K] using (compactWaveletAction_one ψ s hs x).trans hψ₀
  have hDiff : compactWaveletAction ψ s b x = ∫ y, K y*(b y-b x) := by
    simp_rw [mul_sub]
    rw [integral_sub hB hC, integral_mul_const,hMass,zero_mul,sub_zero]
    rfl
  have hLoc (y : Space) : ‖K y*(b y-b x)‖ ≤ ((L:ℝ)*s)*‖K y‖ := by
    by_cases hy : ‖x-y‖ ≤ s
    · have h := hLip.dist_le_mul y x
      rw [dist_eq_norm,dist_comm y x,dist_eq_norm] at h
      rw [norm_mul,mul_comm ‖K y‖]
      exact mul_le_mul_of_nonneg_right (h.trans (mul_le_mul_of_nonneg_left hy L.coe_nonneg))
        (norm_nonneg _)
    · have hScale : 1<‖s⁻¹ • (x-y)‖ := by
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le), ← div_eq_inv_mul]
        exact (lt_div_iff₀ hs).mpr (by simpa only [one_mul] using lt_of_not_ge hy)
      have hZero : K y = 0 := by simp only [K,compactWaveletKernel,hψ _ hScale,smul_zero]
      simp only [hZero,zero_mul,norm_zero,mul_zero,le_rfl]
  have hMassNorm : (∫ y, ‖K y‖) = ∫ z, ‖ψ z‖ := by
    change (∫ y, ‖compactWaveletKernel ψ s (x-y)‖) = _
    rw [← integral_map (f := fun z => ‖compactWaveletKernel ψ s z‖) hTx.measurable.aemeasurable
      (by rw [hTx.map_eq]; exact hW.norm.aestronglyMeasurable),
      hTx.map_eq,waveletKernel_norm_mass ψ s hs]
  rw [hDiff]
  calc
    _ ≤ ∫ y, ‖K y*(b y-b x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ((L:ℝ)*s)*‖K y‖ := integral_mono_of_nonneg
      (Eventually.of_forall fun _ => norm_nonneg _) (hK.norm.const_mul _) (Eventually.of_forall hLoc)
    _ = _ := by rw [integral_const_mul,hMassNorm]

/-- Fine and coarse L¹ estimates for the actual double-window scale term. -/
theorem compactWaveletParaproduct_scale_L1_bounds (φ ψ θ : SchwartzMap Space ℂ)
    (hψ : ∀ z, 1<‖z‖ → ψ z=0) (hψ₀ : (∫ z, ψ z)=0)
    (s : ℝ) (hs : 0<s) {b f : Space → ℂ}
    (hb : Integrable b volume) (hf : Integrable f volume) (L : NNReal) (hLip : LipschitzWith L b) :
    let F := fun y => compactWaveletAction ψ s b y * compactWaveletAction φ s f y
    let I := ∫ x, ‖compactWaveletAction θ s F x‖
    Integrable (compactWaveletAction θ s F) volume ∧
      I ≤ ((L:ℝ)*s)*(∫ z, ‖θ z‖)*(∫ z, ‖ψ z‖)*(∫ z, ‖φ z‖)*(∫ y, ‖f y‖) ∧
      I ≤ ((s^4)⁻¹ * SchwartzMap.seminorm ℝ 0 0 φ) *
        (∫ z, ‖θ z‖)*(∫ z, ‖ψ z‖)*(∫ z, ‖b z‖)*(∫ y, ‖f y‖) := by
  intro F I
  let B := ((L:ℝ)*s)*(∫ z, ‖ψ z‖)
  let P := (|(s^4)⁻¹| * SchwartzMap.seminorm ℝ 0 0 φ)*(∫ y, ‖f y‖)
  have hB : 0≤B := mul_nonneg (mul_nonneg L.coe_nonneg hs.le) (integral_nonneg fun _ => norm_nonneg _)
  have hP : 0≤P := mul_nonneg (mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
    (integral_nonneg fun _ => norm_nonneg _)
  have hT : 0 ≤ ∫ z : Space, ‖θ z‖ := integral_nonneg fun _ => norm_nonneg _
  have hG := compactWaveletAction_integrable ψ s hs hb
  have hH := compactWaveletAction_integrable φ s hs hf
  have hF : Integrable F volume := by
    simpa only [F,mul_comm] using hG.bdd_mul hH.aestronglyMeasurable
      ⟨P, compactWaveletAction_norm_le_integral_norm φ s hf⟩
  have hOne := compactWaveletAction_L1_bound θ s hs hF
  refine ⟨compactWaveletAction_integrable θ s hs hF,?_,?_⟩
  · have hFine : (∫ y, ‖F y‖) ≤ B*((∫ z, ‖φ z‖)*(∫ y, ‖f y‖)) := by
      calc
        _ ≤ ∫ y, B*‖compactWaveletAction φ s f y‖ := integral_mono hF.norm
          (hH.norm.const_mul B) fun y => by
            rw [show ‖F y‖ = ‖compactWaveletAction ψ s b y‖*‖compactWaveletAction φ s f y‖ from norm_mul _ _]
            exact mul_le_mul_of_nonneg_right
              (compactWaveletAction_Lipschitz_small_scale_bound ψ hψ hψ₀ s hs hb L hLip y) (norm_nonneg _)
        _ ≤ _ := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (compactWaveletAction_L1_bound φ s hs hf) hB
    refine (hOne.trans (mul_le_mul_of_nonneg_left hFine hT)).trans_eq ?_
    dsimp only [B]
    ring
  · have hC : (∫ y, ‖F y‖) ≤ P*((∫ z, ‖ψ z‖)*(∫ y, ‖b y‖)) := by
      calc
        _ ≤ ∫ y, P*‖compactWaveletAction ψ s b y‖ := integral_mono hF.norm
          (hG.norm.const_mul P) fun y => by
            rw [show ‖F y‖ = ‖compactWaveletAction ψ s b y‖*‖compactWaveletAction φ s f y‖ from norm_mul _ _,
              mul_comm ‖compactWaveletAction ψ s b y‖]
            exact mul_le_mul_of_nonneg_right (compactWaveletAction_norm_le_integral_norm φ s hf y) (norm_nonneg _)
        _ ≤ _ := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (compactWaveletAction_L1_bound ψ s hs hb) hP
    refine (hOne.trans (mul_le_mul_of_nonneg_left hC hT)).trans_eq ?_
    dsimp only [P]
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _))]
    ring

end Burnett.Analysis.CarlesonEmbedding
