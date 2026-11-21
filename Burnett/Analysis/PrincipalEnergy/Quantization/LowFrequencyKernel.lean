import Burnett.Analysis.PrincipalEnergy.Quantization.NormalizedBaseIdentification

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Set MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff FourierTransform BigOperators

def firstOrderLowSymbol (a : E → E → ℂ) (x ξ : E) : ℂ := (radialCore ξ : ℂ) * a x ξ

def firstOrderLowKernel (a : E → E → ℂ) (x z : E) : ℂ := 𝓕⁻ (firstOrderLowSymbol a x) z

def firstOrderLowAction (a : E → E → ℂ) (f : E → ℂ) (x : E) : ℂ :=
  firstOrderAction (firstOrderLowSymbol a) f x

private theorem lowSymbol_support (a : E → E → ℂ) (x : E) :
    tsupport (firstOrderLowSymbol a x) ⊆ Metric.closedBall 0 2 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro ξ hξ
  by_contra h
  have hout : 2 ≤ ‖ξ‖ :=
    (not_le.mp (by simpa only [Metric.mem_closedBall,dist_zero_right] using h)).le
  exact hξ (by simp [firstOrderLowSymbol,radialCore_eq_zero ξ hout])

private theorem lowSymbol_smooth {a : E → E → ℂ} (ha : FrequencyOrderOne a) (x : E) :
    ContDiff ℝ ∞ (firstOrderLowSymbol a x) :=
  (Complex.ofRealCLM.contDiff.comp radialCore_contDiff).mul (ha.smooth x)

theorem firstOrderLowSymbol_integrable {a : E → E → ℂ} (ha : FrequencyOrderOne a) (x : E) :
    Integrable (firstOrderLowSymbol a x) (volume : Measure E) :=
  (lowSymbol_smooth ha x).continuous.integrable_of_hasCompactSupport
    ((isCompact_closedBall (0 : E) 2).of_isClosed_subset isClosed_closure (lowSymbol_support a x))

private theorem uniform_low_frequency_derivative {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ, ‖iteratedFDeriv ℝ n (firstOrderLowSymbol a x) ξ‖ ≤ C := by
  classical
  let θ (ξ : E) : ℂ := (radialCore ξ : ℂ)
  let K := Metric.closedBall (0 : E) 2
  have hK : IsCompact K := isCompact_closedBall _ _
  have hθ : ContDiff ℝ ∞ θ := Complex.ofRealCLM.contDiff.comp radialCore_contDiff
  have hθBound (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ ξ ∈ K, ‖iteratedFDeriv ℝ j θ ξ‖ ≤ B := by
    have hc := (hθ.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm
    obtain ⟨B,hB⟩ := hK.bddAbove_image hc.continuousOn
    exact ⟨max B 0,le_max_right _ _,fun ξ hξ => (hB (mem_image_of_mem _ hξ)).trans (le_max_left _ _)⟩
  choose B hB hΘ using hθBound
  choose D hD hOrder using ha.order
  let C := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * B i * (3*D (n-i))
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i)) (mul_nonneg (by norm_num) (hD (n-i))))
  refine ⟨C,hC,?_⟩
  intro x ξ
  by_cases hξ : ξ ∈ K
  · have hsize : ‖ξ‖ ≤ 2 := by simpa only [K,Metric.mem_closedBall,dist_zero_right] using hξ
    have hDer (j : ℕ) : ‖iteratedFDeriv ℝ j (a x) ξ‖ ≤ 3*D j := by
      have hW : 1 ≤ (1+‖ξ‖)^j := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))
      calc
        _ ≤ ‖iteratedFDeriv ℝ j (a x) ξ‖ * (1+‖ξ‖)^j :=
          le_mul_of_one_le_right (norm_nonneg _) hW
        _ ≤ D j * (1+‖ξ‖) := hOrder j x ξ
        _ ≤ _ := by have := mul_le_mul_of_nonneg_left (by linarith : 1+‖ξ‖ ≤ 3) (hD j); linarith
    change ‖iteratedFDeriv ℝ n (fun η => θ η * a x η) ξ‖ ≤ C
    exact (norm_iteratedFDeriv_mul_le hθ (ha.smooth x) ξ (by exact_mod_cast le_top)).trans
      (Finset.sum_le_sum fun i _ => mul_le_mul
        (mul_le_mul_of_nonneg_left (hΘ i ξ hξ) (by positivity)) (hDer (n-i))
        (norm_nonneg _) (mul_nonneg (by positivity) (hB i)))
  · have h0 : iteratedFDeriv ℝ n (firstOrderLowSymbol a x) ξ = 0 := by
      by_contra hn
      exact hξ (lowSymbol_support a x (support_iteratedFDeriv_subset n hn))
    rw [h0,norm_zero]
    exact hC

private def swappedLowSymbol (a : E → E → ℂ) (ξ x : E) : ℂ :=
  (1+‖x‖) • firstOrderLowSymbol a x ξ

private theorem swappedLowSymbol_compactBaseOrderOne {a : E → E → ℂ} (ha : FrequencyOrderOne a) :
    CompactBaseOrderOne (swappedLowSymbol a) where
  support := by
    refine ⟨Metric.closedBall 0 2,isCompact_closedBall _ _,fun x => ?_⟩
    exact (closure_mono (Function.support_const_smul_subset (1+‖x‖) (firstOrderLowSymbol a x))).trans
      (lowSymbol_support a x)
  smooth x := (lowSymbol_smooth ha x).const_smul (1+‖x‖)
  order n := by
    obtain ⟨C,hC,hBound⟩ := uniform_low_frequency_derivative ha n
    refine ⟨C,hC,fun ξ x => ?_⟩
    have hS : ContDiffAt ℝ n (firstOrderLowSymbol a x) ξ :=
      (lowSymbol_smooth ha x).contDiffAt.of_le (by exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ n ((1+‖x‖) • firstOrderLowSymbol a x) ξ‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply hS,norm_smul,Real.norm_of_nonneg (by positivity),mul_comm C]
    exact mul_le_mul_of_nonneg_left (hBound x ξ) (by positivity)

private theorem normalized_swappedLowSymbol (a : E → E → ℂ) (x ξ : E) :
    normalizedBaseSymbol (swappedLowSymbol a) ξ x = firstOrderLowSymbol a x ξ := by
  rw [normalizedBaseSymbol,swappedLowSymbol,smul_smul,inv_mul_cancel₀ (by positivity),one_smul]

private theorem lowKernel_eq_baseFourier (a : E → E → ℂ) (x z : E) :
    firstOrderLowKernel a x z = normalizedBaseFourier (swappedLowSymbol a) (-z) x := by
  rw [firstOrderLowKernel,Real.fourierIntegralInv_eq_fourierIntegral_neg,normalizedBaseFourier]
  simp_rw [normalized_swappedLowSymbol]

/-- Uniform integrable radial majorant for the true low-frequency kernel. -/
theorem exists_lowKernel_integrable_profile {a : E → E → ℂ} (ha : FrequencyOrderOne a) :
    ∃ C : ℝ, 0 < C ∧ Integrable (fun z : E => C * ((1+‖z‖^2)^3)⁻¹) ∧
      ∀ x z, ‖firstOrderLowKernel a x z‖ ≤ C * ((1+‖z‖^2)^3)⁻¹ := by
  obtain ⟨C,hC,hI,hDom⟩ := normalizedBaseFourier_dominated (swappedLowSymbol_compactBaseOrderOne ha)
  refine ⟨C,hC,hI,fun x z => ?_⟩
  rw [lowKernel_eq_baseFourier]
  simpa only [norm_neg] using hDom (-z) x

/-- The compact radial multiplier preserves the genuine joint continuity of
the low kernel in its base and displacement variables. -/
theorem firstOrderLowKernel_joint_continuous {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (hs : Continuous (Function.uncurry a)) :
    Continuous (Function.uncurry (firstOrderLowKernel a)) := by
  have hh : Continuous (Function.uncurry (swappedLowSymbol a)) :=
    (continuous_const.add continuous_snd.norm).smul
      ((Complex.continuous_ofReal.comp (radialCore_contDiff.continuous.comp continuous_fst)).mul
        (hs.comp continuous_swap))
  let T (p : E × E) : E × E := (-p.2,p.1)
  have hT : Continuous T := continuous_snd.neg.prodMk continuous_fst
  have hComp : Continuous (fun p : E × E =>
      normalizedBaseFourier (swappedLowSymbol a) (-p.2) p.1) := by
    change Continuous ((Function.uncurry (normalizedBaseFourier (swappedLowSymbol a))) ∘ T)
    exact (normalizedBaseFourier_joint_continuous (swappedLowSymbol_compactBaseOrderOne ha) hh).comp hT
  rw [show Function.uncurry (firstOrderLowKernel a) =
      (fun p : E × E => normalizedBaseFourier (swappedLowSymbol a) (-p.2) p.1) from
      funext fun p => lowKernel_eq_baseFourier a p.1 p.2]
  exact hComp

end Burnett.Analysis.FirstOrderDyadic
