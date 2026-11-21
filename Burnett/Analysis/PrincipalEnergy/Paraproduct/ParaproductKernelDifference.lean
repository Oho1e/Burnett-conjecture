import Burnett.Analysis.PrincipalEnergy.Paraproduct.ParaproductKernelAtScale

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set
open scoped NNReal

/-- The actual scaled Schwartz kernel loses one inverse length under a
first spatial difference. -/
theorem compactWaveletKernel_spatial_sub_bound (φ : SchwartzMap Space ℂ)
    (s : ℝ) (hs : 0<s) (z z' : Space) :
    ‖compactWaveletKernel φ s z-compactWaveletKernel φ s z'‖ ≤
      (s^5)⁻¹*SchwartzMap.seminorm ℝ 0 1 φ*‖z-z'‖ := by
  have hD (x : Space) : ‖fderiv ℝ (φ : Space → ℂ) x‖ ≤ SchwartzMap.seminorm ℝ 0 1 φ := by
    have h := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ φ 1 x
    rwa [← norm_iteratedFDeriv_fderiv (n := 0),norm_iteratedFDeriv_zero] at h
  have hLip := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => φ.differentiableAt)
    (fun x _ => hD x) convex_univ (mem_univ (s⁻¹ • z')) (mem_univ (s⁻¹ • z))
  rw [compactWaveletKernel,compactWaveletKernel,← smul_sub,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _))]
  refine (mul_le_mul_of_nonneg_left hLip (inv_nonneg.mpr (pow_nonneg hs.le _))).trans_eq ?_
  rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),
    show s^5=s^4*s by ring,mul_inv_rev]
  ring

private theorem waveletKernel_integrable (φ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) :
    Integrable (compactWaveletKernel φ s) (volume : Measure Space) :=
  (φ.integrable.comp_smul (inv_ne_zero hs.ne')).smul _

private theorem waveletKernel_continuous (φ : SchwartzMap Space ℂ) (s : ℝ) :
    Continuous (compactWaveletKernel φ s) :=
  continuous_const.smul (φ.continuous.comp (continuous_const.smul continuous_id))

private theorem waveletKernel_norm_mass_sub_right (φ : SchwartzMap Space ℂ) (s : ℝ)
    (hs : 0<s) (y : Space) : (∫ z, ‖compactWaveletKernel φ s (z-y)‖) = ∫ z, ‖φ z‖ := by
  have hTx : MeasurePreserving (fun z : Space => z-y) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure Space) (-y)
  rw [← integral_map (f := fun z => ‖compactWaveletKernel φ s z‖) hTx.measurable.aemeasurable
    (by rw [hTx.map_eq]; exact (waveletKernel_integrable φ s hs).norm.aestronglyMeasurable),hTx.map_eq]
  simp only [compactWaveletKernel,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _))]
  rw [integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg volume (fun z => ‖φ z‖) hs.le,
    finrank_euclideanSpace_fin,smul_eq_mul,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 4 hs.ne'),one_mul]

private theorem paraproduct_kernel_integrand_integrable (φ ψ θ : SchwartzMap Space ℂ)
    (s : ℝ) (hs : 0<s) {b : Space → ℂ} (hb : Integrable b volume)
    {B : ℝ} (hB : 0≤B) (hQ : ∀ z, ‖compactWaveletAction ψ s b z‖≤B)
    (x y : Space) :
    Integrable (fun z => compactWaveletKernel θ s (x-z)*
      (compactWaveletAction ψ s b z*compactWaveletKernel φ s (z-y))) volume := by
  let Θ (z : Space) := compactWaveletKernel θ s (x-z)
  let Φ (z : Space) := compactWaveletKernel φ s (z-y)
  let Q := compactWaveletAction ψ s b
  let V := (s^4)⁻¹*SchwartzMap.seminorm ℝ 0 0 φ
  have hΘ : Integrable Θ (volume : Measure Space) :=
    ((volume : Measure Space).measurePreserving_sub_left x).integrable_comp_of_integrable
      (waveletKernel_integrable θ s hs)
  have hQcont : Continuous Q := compactWaveletAction_continuous ψ s hs b hb
  have hΦcont : Continuous Φ := (waveletKernel_continuous φ s).comp (continuous_id.sub continuous_const)
  refine (hΘ.norm.const_mul (B*V)).mono'
    (hΘ.aestronglyMeasurable.mul (hQcont.mul hΦcont).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  change ‖Θ z*(Q z*Φ z)‖ ≤ (B*V)*‖Θ z‖
  rw [norm_mul,norm_mul,mul_comm ‖Θ z‖]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (hQ z) (compactWaveletKernel_norm_le_scale φ s hs _) (norm_nonneg _) hB) (norm_nonneg _)

/-- Difference in the source variable of a single physical kernel. -/
theorem compactWaveletParaproductKernelAtScale_source_sub_bound (φ ψ θ : SchwartzMap Space ℂ)
    (s : ℝ) (hs : 0<s) {b : Space → ℂ} (hb : Integrable b volume)
    {B : ℝ} (hB : 0≤B) (hQ : ∀ z, ‖compactWaveletAction ψ s b z‖≤B)
    (x y y' : Space) :
    ‖compactWaveletParaproductKernelAtScale φ ψ θ s b x y-
      compactWaveletParaproductKernelAtScale φ ψ θ s b x y'‖ ≤
      B*(SchwartzMap.seminorm ℝ 0 1 φ)*(∫ z, ‖θ z‖)*‖y-y'‖*(s^5)⁻¹ := by
  let F (z : Space) := compactWaveletAction ψ s b z*
    (compactWaveletKernel φ s (z-y)-compactWaveletKernel φ s (z-y'))
  have hF (z : Space) : ‖F z‖ ≤ B*((s^5)⁻¹*SchwartzMap.seminorm ℝ 0 1 φ*‖y-y'‖) := by
    have hSub := compactWaveletKernel_spatial_sub_bound φ s hs (z-y) (z-y')
    rw [show z-y-(z-y')=y'-y by abel,norm_sub_rev y' y] at hSub
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul (hQ z) hSub (norm_nonneg _) hB
  have hEq :
      compactWaveletParaproductKernelAtScale φ ψ θ s b x y-
        compactWaveletParaproductKernelAtScale φ ψ θ s b x y' = compactWaveletAction θ s F x := by
    change ((∫ z, compactWaveletKernel θ s (x-z)*
      (compactWaveletAction ψ s b z*compactWaveletKernel φ s (z-y)))-
      ∫ z, compactWaveletKernel θ s (x-z)*
        (compactWaveletAction ψ s b z*compactWaveletKernel φ s (z-y'))) =
      ∫ z, compactWaveletKernel θ s (x-z)*F z
    rw [← integral_sub (paraproduct_kernel_integrand_integrable φ ψ θ s hs hb hB hQ x y)
      (paraproduct_kernel_integrand_integrable φ ψ θ s hs hb hB hQ x y')]
    apply congrArg (fun G : Space → ℂ => ∫ z, G z)
    funext z
    change compactWaveletKernel θ s (x-z)*
      (compactWaveletAction ψ s b z*compactWaveletKernel φ s (z-y))-
      compactWaveletKernel θ s (x-z)*
      (compactWaveletAction ψ s b z*compactWaveletKernel φ s (z-y')) =
      compactWaveletKernel θ s (x-z)*F z
    dsimp only [F]
    ring
  rw [hEq]
  exact (compactWaveletAction_norm_le_L1Mass_mul θ s hs hF x).trans_eq (by ring)

/-- Difference in the target variable of a single physical kernel. -/
theorem compactWaveletParaproductKernelAtScale_target_sub_bound (φ ψ θ : SchwartzMap Space ℂ)
    (s : ℝ) (hs : 0<s) {b : Space → ℂ} (hb : Integrable b volume)
    {B : ℝ} (hB : 0≤B) (hQ : ∀ z, ‖compactWaveletAction ψ s b z‖≤B)
    (x x' y : Space) :
    ‖compactWaveletParaproductKernelAtScale φ ψ θ s b x y-
      compactWaveletParaproductKernelAtScale φ ψ θ s b x' y‖ ≤
      B*(SchwartzMap.seminorm ℝ 0 1 θ)*(∫ z, ‖φ z‖)*‖x-x'‖*(s^5)⁻¹ := by
  let Θ (z : Space) := compactWaveletKernel θ s (x-z)-compactWaveletKernel θ s (x'-z)
  let Φ (z : Space) := compactWaveletKernel φ s (z-y)
  let Q := compactWaveletAction ψ s b
  let C := (s^5)⁻¹*SchwartzMap.seminorm ℝ 0 1 θ*‖x-x'‖
  have hC : 0≤C := mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _)) (apply_nonneg _ _)) (norm_nonneg _)
  have hΘ (z : Space) : ‖Θ z‖≤C := by
    have h := compactWaveletKernel_spatial_sub_bound θ s hs (x-z) (x'-z)
    rwa [show x-z-(x'-z)=x-x' by abel] at h
  have hΦ : Integrable Φ (volume : Measure Space) := by
    have hTx : MeasurePreserving (fun z : Space => z-y) volume volume := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure Space) (-y)
    exact hTx.integrable_comp_of_integrable (waveletKernel_integrable φ s hs)
  have hEq :
      compactWaveletParaproductKernelAtScale φ ψ θ s b x y-
        compactWaveletParaproductKernelAtScale φ ψ θ s b x' y = ∫ z, Θ z*(Q z*Φ z) := by
    unfold compactWaveletParaproductKernelAtScale
    rw [← integral_sub (paraproduct_kernel_integrand_integrable φ ψ θ s hs hb hB hQ x y)
      (paraproduct_kernel_integrand_integrable φ ψ θ s hs hb hB hQ x' y)]
    apply congrArg (fun G : Space → ℂ => ∫ z, G z)
    funext z
    dsimp only [Θ,Φ,Q]
    ring
  rw [hEq]
  calc
    _ ≤ ∫ z, ‖Θ z*(Q z*Φ z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, (C*B)*‖Φ z‖ := integral_mono_of_nonneg
      (Eventually.of_forall fun _ => norm_nonneg _) (hΦ.norm.const_mul _) (Eventually.of_forall fun z => by
        change ‖Θ z*(Q z*Φ z)‖≤(C*B)*‖Φ z‖
        rw [norm_mul,norm_mul,← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (hΘ z) (hQ z) (norm_nonneg _) hC) (norm_nonneg _))
    _ = _ := by rw [integral_const_mul,waveletKernel_norm_mass_sub_right φ s hs y]; dsimp only [C]; ring

theorem compactWaveletParaproductKernelAtScale_continuous (φ ψ θ : SchwartzMap Space ℂ)
    (s : ℝ) (hs : 0<s) {b : Space → ℂ} (hb : Integrable b volume)
    {B : ℝ} (hB : 0≤B) (hQ : ∀ z, ‖compactWaveletAction ψ s b z‖≤B) :
    Continuous (fun p : Space × Space => compactWaveletParaproductKernelAtScale φ ψ θ s b p.1 p.2) := by
  let A := B*SchwartzMap.seminorm ℝ 0 1 θ*(∫ z, ‖φ z‖)*(s^5)⁻¹
  let C := B*SchwartzMap.seminorm ℝ 0 1 φ*(∫ z, ‖θ z‖)*(s^5)⁻¹
  have hInv : 0≤(s^5)⁻¹ := inv_nonneg.mpr (pow_nonneg hs.le _)
  have hA : 0≤A := mul_nonneg (mul_nonneg (mul_nonneg hB (apply_nonneg _ _))
    (integral_nonneg fun _ => norm_nonneg _)) hInv
  have hC : 0≤C := mul_nonneg (mul_nonneg (mul_nonneg hB (apply_nonneg _ _))
    (integral_nonneg fun _ => norm_nonneg _)) hInv
  let K := compactWaveletParaproductKernelAtScale φ ψ θ s b
  have hLip : LipschitzWith (⟨A+C,add_nonneg hA hC⟩ : NNReal)
      (fun p : Space × Space => K p.1 p.2) := by
    refine lipschitzWith_iff_norm_sub_le.mpr fun p q => ?_
    change ‖K p.1 p.2-K q.1 q.2‖≤(A+C)*‖p-q‖
    have hX : ‖K p.1 p.2-K q.1 p.2‖≤A*‖p.1-q.1‖ :=
      (compactWaveletParaproductKernelAtScale_target_sub_bound φ ψ θ s hs hb hB hQ p.1 q.1 p.2).trans_eq (by
        dsimp only [A]
        ring)
    have hY : ‖K q.1 p.2-K q.1 q.2‖≤C*‖p.2-q.2‖ :=
      (compactWaveletParaproductKernelAtScale_source_sub_bound φ ψ θ s hs hb hB hQ q.1 p.2 q.2).trans_eq (by
        dsimp only [C]
        ring)
    have hT := norm_add_le (K p.1 p.2-K q.1 p.2) (K q.1 p.2-K q.1 q.2)
    rw [sub_add_sub_cancel] at hT
    calc
      _ ≤ ‖K p.1 p.2-K q.1 p.2‖+‖K q.1 p.2-K q.1 q.2‖ := hT
      _ ≤ A*‖p.1-q.1‖+C*‖p.2-q.2‖ := add_le_add hX hY
      _ ≤ A*‖p-q‖+C*‖p-q‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le (p-q)) hA)
          (mul_le_mul_of_nonneg_left (norm_snd_le (p-q)) hC)
      _ = _ := by ring
  exact hLip.continuous

end Burnett.Analysis.CarlesonEmbedding
