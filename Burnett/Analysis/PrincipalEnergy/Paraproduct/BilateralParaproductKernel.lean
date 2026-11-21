import Burnett.Analysis.PrincipalEnergy.Paraproduct.ParaproductKernelDifference
import Burnett.Analysis.PrincipalEnergy.Paraproduct.BilateralKernelTails
import Burnett.Analysis.PrincipalEnergy.Paraproduct.PointwiseCoefficientWavelet

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Burnett.Analysis.FirstOrderDyadic
open scoped NNReal

def bilateralParaproductKernel (φ ψ θ : SchwartzMap Space ℂ) (t : ℝ)
    (b : Space → ℂ) (x y : Space) : ℂ :=
  ∑' j : ℤ, compactWaveletParaproductKernelAtScale φ ψ θ (bilateralWaveletScale t j) b x y

theorem bilateralParaproductKernel_size (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hθ : ∀ z, 1<‖z‖ → θ z=0)
    (t : ℝ) (ht : 0<t) {b : Space → ℂ} {B : ℝ} (hB : 0≤B)
    (hQ : ∀ (j : ℤ) z, ‖compactWaveletAction ψ (bilateralWaveletScale t j) b z‖≤B)
    (x y : Space) (hxy : x≠y) :
    Summable (fun j : ℤ =>
      ‖compactWaveletParaproductKernelAtScale φ ψ θ (bilateralWaveletScale t j) b x y‖) ∧
    (∑' j : ℤ, ‖compactWaveletParaproductKernelAtScale φ ψ θ (bilateralWaveletScale t j) b x y‖) ≤
      (256/15:ℝ)*B*SchwartzMap.seminorm ℝ 0 0 φ*(∫ z, ‖θ z‖)*(‖x-y‖^4)⁻¹ ∧
    ‖bilateralParaproductKernel φ ψ θ t b x y‖ ≤
      (256/15:ℝ)*B*SchwartzMap.seminorm ℝ 0 0 φ*(∫ z, ‖θ z‖)*(‖x-y‖^4)⁻¹ := by
  let s := bilateralWaveletScale t
  let κ (j : ℤ) := compactWaveletParaproductKernelAtScale φ ψ θ (s j) b x y
  let A := B*SchwartzMap.seminorm ℝ 0 0 φ*(∫ z, ‖θ z‖)
  have hA : 0≤A := mul_nonneg (mul_nonneg hB (apply_nonneg _ _)) (integral_nonneg fun _ => norm_nonneg _)
  have hs (j : ℤ) : 0<s j := div_pos ht (zpow_pos (by norm_num) _)
  have hr : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hZero (j : ℤ) (hj : s j < ‖x-y‖/2) : ‖κ j‖=0 := by
    rw [show κ j = 0 from compactWaveletParaproductKernelAtScale_zero φ ψ θ hφ hθ (s j) (hs j)
      b x y (by linarith),norm_zero]
  have hTail := bilateral_wavelet_inversePower_tail 4 (by decide) t (‖x-y‖/2) ht (half_pos hr) hA
    (fun j => ‖κ j‖) (fun _ => norm_nonneg _) hZero
    (fun j => compactWaveletParaproductKernelAtScale_size φ ψ θ (s j) (hs j) hB (hQ j) x y)
  have hScale : ((‖x-y‖/2)^4)⁻¹ = 16*(‖x-y‖^4)⁻¹ := by
    field_simp [hr.ne']
    ring
  have hAbs : (∑' j, ‖κ j‖) ≤ (256/15:ℝ)*B*SchwartzMap.seminorm ℝ 0 0 φ*
      (∫ z, ‖θ z‖)*(‖x-y‖^4)⁻¹ := by
    refine (Real.le_norm_self _).trans (hTail.2.trans_eq ?_)
    rw [hScale]
    dsimp only [A]
    norm_num
    ring
  exact ⟨hTail.1,hAbs,(norm_tsum_le_tsum_norm hTail.1).trans hAbs⟩

private theorem bilateralParaproductKernel_sub_bound (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hθ : ∀ z, 1<‖z‖ → θ z=0)
    (t : ℝ) (ht : 0<t) {b : Space → ℂ} {B : ℝ} (hB : 0≤B)
    (hQ : ∀ (j : ℤ) z, ‖compactWaveletAction ψ (bilateralWaveletScale t j) b z‖≤B)
    (x y x' y' : Space) (hxy : x≠y) (hGap : ‖x-y‖/2≤‖x'-y'‖)
    {A : ℝ} (hA : 0≤A)
    (hS : ∀ j : ℤ,
      ‖compactWaveletParaproductKernelAtScale φ ψ θ (bilateralWaveletScale t j) b x y-
        compactWaveletParaproductKernelAtScale φ ψ θ (bilateralWaveletScale t j) b x' y'‖ ≤
      A*((bilateralWaveletScale t j)^5)⁻¹) :
    ‖bilateralParaproductKernel φ ψ θ t b x y-bilateralParaproductKernel φ ψ θ t b x' y'‖ ≤
      (32768/31:ℝ)*A*(‖x-y‖^5)⁻¹ := by
  let s := bilateralWaveletScale t
  let κ (j : ℤ) := compactWaveletParaproductKernelAtScale φ ψ θ (s j) b x y
  let κ' (j : ℤ) := compactWaveletParaproductKernelAtScale φ ψ θ (s j) b x' y'
  have hr : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hxy' : x'≠y' := sub_ne_zero.mp (norm_pos_iff.mp ((half_pos hr).trans_le hGap))
  have hs (j : ℤ) : 0<s j := div_pos ht (zpow_pos (by norm_num) _)
  have hZero (j : ℤ) (hj : s j<‖x-y‖/4) : ‖κ j-κ' j‖=0 := by
    rw [show κ j = 0 from compactWaveletParaproductKernelAtScale_zero φ ψ θ hφ hθ (s j) (hs j)
      b x y (by linarith),show κ' j = 0 from
      compactWaveletParaproductKernelAtScale_zero φ ψ θ hφ hθ (s j) (hs j) b x' y' (by linarith),
      sub_zero,norm_zero]
  have hTail := bilateral_wavelet_inversePower_tail 5 (by decide) t (‖x-y‖/4) ht
    (div_pos hr (by norm_num)) hA (fun j => ‖κ j-κ' j‖) (fun _ => norm_nonneg _) hZero hS
  have hSum : Summable κ := (bilateralParaproductKernel_size φ ψ θ hφ hθ t ht hB hQ x y hxy).1.of_norm
  have hSum' : Summable κ' := (bilateralParaproductKernel_size φ ψ θ hφ hθ t ht hB hQ x' y' hxy').1.of_norm
  change ‖(∑' j, κ j)-(∑' j, κ' j)‖ ≤ _
  rw [← hSum.tsum_sub hSum']
  have hScale : ((‖x-y‖/4)^5)⁻¹ = 1024*(‖x-y‖^5)⁻¹ := by
    field_simp [hr.ne']
    ring
  refine (norm_tsum_le_tsum_norm hTail.1).trans ((Real.le_norm_self _).trans (hTail.2.trans_eq ?_))
  rw [hScale]
  norm_num
  ring

theorem bilateralParaproductKernel_source_sub_bound (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hθ : ∀ z, 1<‖z‖ → θ z=0)
    (t : ℝ) (ht : 0<t) {b : Space → ℂ} (hb : Integrable b volume) {B : ℝ} (hB : 0≤B)
    (hQ : ∀ (j : ℤ) z, ‖compactWaveletAction ψ (bilateralWaveletScale t j) b z‖≤B)
    (x y y' : Space) (hxy : x≠y) (hGap : ‖y-y'‖≤‖x-y‖/2) :
    ‖bilateralParaproductKernel φ ψ θ t b x y-bilateralParaproductKernel φ ψ θ t b x y'‖ ≤
      (32768/31:ℝ)*B*SchwartzMap.seminorm ℝ 0 1 φ*(∫ z, ‖θ z‖)*‖y-y'‖*(‖x-y‖^5)⁻¹ := by
  have hTriangle := norm_add_le (x-y') (y'-y)
  rw [show x-y'+(y'-y)=x-y by abel,norm_sub_rev y' y] at hTriangle
  have hGap' : ‖x-y‖/2≤‖x-y'‖ := by linarith
  let A := B*SchwartzMap.seminorm ℝ 0 1 φ*(∫ z, ‖θ z‖)*‖y-y'‖
  have hA : 0≤A := mul_nonneg
    (mul_nonneg (mul_nonneg hB (apply_nonneg _ _)) (integral_nonneg fun _ => norm_nonneg _)) (norm_nonneg _)
  refine (bilateralParaproductKernel_sub_bound φ ψ θ hφ hθ t ht hB hQ x y x y' hxy hGap' hA
    (fun j => compactWaveletParaproductKernelAtScale_source_sub_bound φ ψ θ _ (div_pos ht
      (zpow_pos (by norm_num) _)) hb hB (hQ j) x y y')).trans_eq ?_
  dsimp only [A]
  ring

theorem bilateralParaproductKernel_target_sub_bound (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hθ : ∀ z, 1<‖z‖ → θ z=0)
    (t : ℝ) (ht : 0<t) {b : Space → ℂ} (hb : Integrable b volume) {B : ℝ} (hB : 0≤B)
    (hQ : ∀ (j : ℤ) z, ‖compactWaveletAction ψ (bilateralWaveletScale t j) b z‖≤B)
    (x x' y : Space) (hxy : x≠y) (hGap : ‖x-x'‖≤‖x-y‖/2) :
    ‖bilateralParaproductKernel φ ψ θ t b x y-bilateralParaproductKernel φ ψ θ t b x' y‖ ≤
      (32768/31:ℝ)*B*SchwartzMap.seminorm ℝ 0 1 θ*(∫ z, ‖φ z‖)*‖x-x'‖*(‖x-y‖^5)⁻¹ := by
  have hTriangle := norm_add_le (x-x') (x'-y)
  rw [show x-x'+(x'-y)=x-y by abel] at hTriangle
  have hGap' : ‖x-y‖/2≤‖x'-y‖ := by linarith
  let A := B*SchwartzMap.seminorm ℝ 0 1 θ*(∫ z, ‖φ z‖)*‖x-x'‖
  have hA : 0≤A := mul_nonneg
    (mul_nonneg (mul_nonneg hB (apply_nonneg _ _)) (integral_nonneg fun _ => norm_nonneg _)) (norm_nonneg _)
  refine (bilateralParaproductKernel_sub_bound φ ψ θ hφ hθ t ht hB hQ x y x' y hxy hGap' hA
    (fun j => compactWaveletParaproductKernelAtScale_target_sub_bound φ ψ θ _ (div_pos ht
      (zpow_pos (by norm_num) _)) hb hB (hQ j) x x' y)).trans_eq ?_
  dsimp only [A]
  ring

/-- The actual commutator coefficient yields uniform size and both
first differences for the bilateral physical paraproduct kernel. -/
theorem exists_compactBase_bilateral_paraproduct_kernel_bounds
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hψ : ∀ z, 1<‖z‖ → ψ z=0) (hθ : ∀ z, 1<‖z‖ → θ z=0)
    (hψ₀ : (∫ z, ψ z)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0≤U → LipschitzWith L r → (∀ x, ‖r x‖≤U) → ∀ (t : ℝ), 0<t →
      let b := coefficientCommutatorConstant a r
      let K := bilateralParaproductKernel φ ψ θ t b
      (∀ x y, x≠y → Summable (fun j : ℤ =>
          ‖compactWaveletParaproductKernelAtScale φ ψ θ (bilateralWaveletScale t j) b x y‖) ∧
        ‖K x y‖ ≤ C*(U+(L:ℝ))*(‖x-y‖^4)⁻¹) ∧
      (∀ x y y', x≠y → ‖y-y'‖≤‖x-y‖/2 →
        ‖K x y-K x y'‖ ≤ C*(U+(L:ℝ))*‖y-y'‖*(‖x-y‖^5)⁻¹) ∧
      (∀ x x' y, x≠y → ‖x-x'‖≤‖x-y‖/2 →
        ‖K x y-K x' y‖ ≤ C*(U+(L:ℝ))*‖x-x'‖*(‖x-y‖^5)⁻¹) := by
  obtain ⟨D,hD,hQ⟩ := exists_compactBase_commutatorConstant_wavelet_sup_bound ha hBase hCont ψ hψ hψ₀
  let C₀ := (256/15:ℝ)*SchwartzMap.seminorm ℝ 0 0 φ*(∫ z, ‖θ z‖)
  let C₁ := (32768/31:ℝ)*SchwartzMap.seminorm ℝ 0 1 φ*(∫ z, ‖θ z‖)
  let C₂ := (32768/31:ℝ)*SchwartzMap.seminorm ℝ 0 1 θ*(∫ z, ‖φ z‖)
  have hC₀ : 0≤C₀ := mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg _ _)) (integral_nonneg fun _ => norm_nonneg _)
  have hC₁ : 0≤C₁ := mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg _ _)) (integral_nonneg fun _ => norm_nonneg _)
  have hC₂ : 0≤C₂ := mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg _ _)) (integral_nonneg fun _ => norm_nonneg _)
  let E := C₀+C₁+C₂
  have hE : 0≤E := add_nonneg (add_nonneg hC₀ hC₁) hC₂
  refine ⟨E*D,mul_nonneg hE hD,?_⟩
  intro r L U hU hLip hR t ht b K
  let B := D*(U+(L:ℝ))
  have hB : 0≤B := mul_nonneg hD (add_nonneg hU L.coe_nonneg)
  have hb : Integrable b volume := coefficientCommutatorConstant_integrable ha.frequency hBase hCont r
  have hQ' (j : ℤ) (z : Space) : ‖compactWaveletAction ψ (bilateralWaveletScale t j) b z‖≤B :=
    hQ r L U hU hLip hR _ (div_pos ht (zpow_pos (by norm_num) _)) z
  have hMon (A : ℝ) (hA : A≤E) (V : ℝ) (hV : 0≤V) :
      A*B*V≤(E*D)*(U+(L:ℝ))*V := by
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hB) hV).trans_eq (by dsimp only [B]; ring)
  refine ⟨?_,?_,?_⟩
  · intro x y hxy
    obtain ⟨hAbs,_,hSize⟩ := bilateralParaproductKernel_size φ ψ θ hφ hθ t ht hB hQ' x y hxy
    refine ⟨hAbs,hSize.trans ?_⟩
    calc
      _ = C₀*B*(‖x-y‖^4)⁻¹ := by dsimp only [C₀]; ring
      _ ≤ _ := hMon C₀ (by dsimp only [E]; linarith) _ (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _))
  · intro x y y' hxy hd
    refine (bilateralParaproductKernel_source_sub_bound φ ψ θ hφ hθ t ht hb hB hQ' x y y' hxy hd).trans ?_
    calc
      _ = C₁*B*(‖y-y'‖*(‖x-y‖^5)⁻¹) := by dsimp only [C₁]; ring
      _ ≤ (E*D)*(U+(L:ℝ))*(‖y-y'‖*(‖x-y‖^5)⁻¹) :=
        hMon C₁ (by dsimp only [E]; linarith) _ (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)))
      _ = _ := by ring
  · intro x x' y hxy hd
    refine (bilateralParaproductKernel_target_sub_bound φ ψ θ hφ hθ t ht hb hB hQ' x x' y hxy hd).trans ?_
    calc
      _ = C₂*B*(‖x-x'‖*(‖x-y‖^5)⁻¹) := by dsimp only [C₂]; ring
      _ ≤ (E*D)*(U+(L:ℝ))*(‖x-x'‖*(‖x-y‖^5)⁻¹) :=
        hMon C₂ (by dsimp only [E]; linarith) _ (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)))
      _ = _ := by ring

end Burnett.Analysis.CarlesonEmbedding
