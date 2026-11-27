import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualSymbolInputs
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

namespace Burnett.A03

open Filter Function Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff FourierTransform Topology

private theorem order_one_iteratedFDeriv_scale (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ | ξ ≠ 0})
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (t : ℝ) (ht : 0 < t) (ξ : E) (hξ : ξ ≠ 0) (n : ℕ) :
    t ^ n * ‖iteratedFDeriv ℝ n a (t • ξ)‖ = t * ‖iteratedFDeriv ℝ n a ξ‖ := by
  let L : E →L[ℝ] E := t • ContinuousLinearMap.id ℝ E
  let U : Set E := {x | x ≠ 0}
  have hU : IsOpen U := isOpen_ne
  have hLU : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hxL : L ξ ∈ U := smul_ne_zero ht.ne' hξ
  have hn : (n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have h := L.iteratedFDerivWithin_comp_right ha hU.uniqueDiffOn hLU.uniqueDiffOn hxL (i := n) hn
  rw [iteratedFDerivWithin_of_isOpen n hLU (x := ξ) hxL,
    iteratedFDerivWithin_of_isOpen n hU (x := L ξ) hxL] at h
  have hScale : a ∘ L = t • a := funext (hHom t ht)
  have hMap : (iteratedFDeriv ℝ n a (L ξ)).compContinuousLinearMap (fun _ => L) =
      t ^ n • iteratedFDeriv ℝ n a (L ξ) := by
    ext v
    change iteratedFDeriv ℝ n a (L ξ) (fun i => t • v i) =
      t ^ n • iteratedFDeriv ℝ n a (L ξ) v
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (iteratedFDeriv ℝ n a (L ξ)).map_smul_univ (fun _ => t) v
  rw [hScale, iteratedFDeriv_const_smul_apply ((ha.contDiffAt (hU.mem_nhds hξ)).of_le hn), hMap] at h
  change t • iteratedFDeriv ℝ n a ξ = t ^ n • iteratedFDeriv ℝ n a (t • ξ) at h
  have hnEq := congrArg norm h
  simpa only [norm_smul, Real.norm_of_nonneg ht.le, Real.norm_of_nonneg (pow_nonneg ht.le n)] using hnEq.symm

private theorem regularized_order_one_derivative_growth (a β : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ | ξ ≠ 0}) (hβ : ContDiff ℝ ∞ β)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (hHigh : ∀ ξ, 1 < ‖ξ‖ → β ξ = a ξ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, ‖iteratedFDeriv ℝ n β ξ‖ ≤ C * (1 + ‖ξ‖) := by
  have hn : (n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  let U : Set E := {ξ | ξ ≠ 0}
  have hU : IsOpen U := isOpen_ne
  have hCont : ContinuousOn (iteratedFDeriv ℝ n a) U :=
    (ha.continuousOn_iteratedFDerivWithin hn hU.uniqueDiffOn).congr
      (fun ξ hξ => (iteratedFDerivWithin_of_isOpen n hU hξ).symm)
  have hSphere : sphere (0 : E) 1 ⊆ U := fun ξ hξ h0 => by
    simpa only [h0, norm_zero, zero_ne_one] using mem_sphere_zero_iff_norm.mp hξ
  obtain ⟨A, hA⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn (hCont.mono hSphere)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) 2).exists_bound_of_continuousOn
    (hβ.continuous_iteratedFDeriv hn).continuousOn
  let C := max 0 (max A B)
  have hC : 0 ≤ C := le_max_left _ _
  refine ⟨C, hC, fun ξ => ?_⟩
  by_cases hSmall : ‖ξ‖ ≤ 2
  · exact ((hB ξ (mem_closedBall_zero_iff.mpr hSmall)).trans
      ((le_max_right A B).trans (le_max_right 0 _))).trans
      (le_mul_of_one_le_right hC (le_add_of_nonneg_right (norm_nonneg _)))
  · have hLarge : 1 < ‖ξ‖ := (by norm_num : (1 : ℝ) < 2).trans (lt_of_not_ge hSmall)
    have hNonzero : ξ ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hLarge)
    let v := ‖ξ‖⁻¹ • ξ
    have hv : ‖v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hNonzero
    have hv0 : v ≠ 0 := by intro h; simp [h] at hv
    have hBack : ‖ξ‖ • v = ξ := by
      change ‖ξ‖ • (‖ξ‖⁻¹ • ξ) = ξ
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hNonzero), one_smul]
    have hScale := order_one_iteratedFDeriv_scale a ha hHom ‖ξ‖ (zero_lt_one.trans hLarge) v hv0 n
    rw [hBack] at hScale
    have hNear : ∀ᶠ y in 𝓝 ξ, 1 < ‖y‖ :=
      (continuous_norm.tendsto ξ).eventually (Ioi_mem_nhds hLarge)
    have hSame : β =ᶠ[𝓝 ξ] a := hNear.mono hHigh
    rw [(hSame.iteratedFDeriv ℝ n).eq_of_nhds]
    calc
      _ ≤ ‖ξ‖ ^ n * ‖iteratedFDeriv ℝ n a ξ‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hLarge.le)
      _ = ‖ξ‖ * ‖iteratedFDeriv ℝ n a v‖ := hScale
      _ ≤ ‖ξ‖ * C := mul_le_mul_of_nonneg_left
        ((hA v (mem_sphere_zero_iff_norm.mpr hv)).trans ((le_max_left A B).trans (le_max_right 0 _)))
        (norm_nonneg _)
      _ ≤ C * (1 + ‖ξ‖) := by
        rw [mul_comm ‖ξ‖ C]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hC

private theorem regularized_order_one_scaled_temperate (a β : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ | ξ ≠ 0}) (hβ : ContDiff ℝ ∞ β)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (hHigh : ∀ ξ, 1 < ‖ξ‖ → β ξ = a ξ) :
    Function.HasTemperateGrowth (fun ν : E => (β (tau • ν) : ℂ)) := by
  let L : E →L[ℝ] E := tau • ContinuousLinearMap.id ℝ E
  have hComp : ContDiff ℝ ∞ (β ∘ L) := hβ.comp L.contDiff
  refine ⟨Complex.ofRealCLM.contDiff.comp hComp, fun n => ?_⟩
  obtain ⟨C, hC, bound⟩ := regularized_order_one_derivative_growth a β ha hβ hHom hHigh n
  have hn : (n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  let S := max 1 ‖L‖
  have hS (x : E) : 1 + ‖L x‖ ≤ S * (1 + ‖x‖) := by
    calc
      _ ≤ S + S * ‖x‖ := add_le_add (le_max_left _ _)
        ((L.le_opNorm x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
      _ = _ := by rw [mul_add, mul_one]
  refine ⟨1, C * S * ‖L‖ ^ n, fun x => ?_⟩
  change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ (β ∘ L)) x‖ ≤ _
  rw [pow_one, Complex.ofRealLI.norm_iteratedFDeriv_comp_left hComp.contDiffAt hn,
    L.iteratedFDeriv_comp_right hβ x hn]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n β (L x)‖ * ∏ _ : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ n β (L x)‖ * ‖L‖ ^ n := by simp
    _ ≤ (C * (S * (1 + ‖x‖))) * ‖L‖ ^ n :=
      mul_le_mul_of_nonneg_right ((bound (L x)).trans (mul_le_mul_of_nonneg_left (hS x) hC)) (by positivity)
    _ = _ := by ring

/-- The regularized frozen order-one multiplier acts on Schwartz fields
and agrees pointwise with the radian quantization. -/
theorem exists_order_one_frozen_schwartz_action (a β : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ | ξ ≠ 0}) (hβ : ContDiff ℝ ∞ β)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (hHigh : ∀ ξ, 1 < ‖ξ‖ → β ξ = a ξ) :
    ∃ B : SchwartzMap E ℂ → SchwartzMap E ℂ, ∀ u, (B u : E → ℂ) = radianAction β u := by
  let h := regularized_order_one_scaled_temperate a β ha hβ hHom hHigh
  let B (u : SchwartzMap E ℂ) :=
    (SchwartzMap.fourierTransformCLE ℂ).symm
      (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) h (SchwartzMap.fourierTransformCLE ℂ u))
  refine ⟨B, fun u => ?_⟩
  have spectrum : 𝓕 (B u : E → ℂ) = radianActionSpectrum β u := by
    funext ξ
    change SchwartzMap.fourierTransformCLE ℂ (B u) ξ = _
    dsimp only [B]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change 𝓕 (u : E → ℂ) ξ * (β (tau • ξ) : ℂ) = (β (tau • ξ) : ℂ) * 𝓕 (u : E → ℂ) ξ
    exact mul_comm _ _
  calc
    (B u : E → ℂ) = 𝓕⁻ (𝓕 (B u : E → ℂ)) :=
      ((B u).continuous.fourier_inversion (B u).integrable
        (SchwartzMap.fourierTransformCLM ℂ (B u)).integrable).symm
    _ = _ := by rw [spectrum, radianActionSpectrum_inverse]

end Burnett.A03
