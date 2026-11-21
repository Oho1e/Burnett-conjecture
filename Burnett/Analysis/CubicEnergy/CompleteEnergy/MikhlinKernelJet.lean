import Burnett.Analysis.CubicEnergy.CompleteEnergy.MikhlinProfileJet
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Finset Metric Set
open scoped ContDiff FourierTransform

/-- The inverse-transform kernel of a frequency profile supported in the fixed
ball has bounds for its spatial derivatives from the stated frequency derivative
masses. The coefficient is independent of the profile. -/
theorem mikhlin_inverse_profile_decay (k N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : SchwartzMap E ℂ),
    tsupport (a : E → ℂ) ⊆ closedBall (0 : E) 2 → ∀ (B : ℝ), 0 ≤ B →
    (∀ n : ℕ, n ≤ N → (∫ ξ, ‖iteratedFDeriv ℝ n (a : E → ℂ) ξ‖) ≤ B) →
    ∀ x : E, (1+‖x‖)^N * ‖iteratedFDeriv ℝ k (𝓕⁻ (a : E → ℂ)) x‖ ≤ C * B := by
  let L : ℝ := (2 * Real.pi)^k * (2*(k:ℝ)+2)^N
  let M : ℝ := ((k+1:ℕ):ℝ) * ((N+1:ℕ):ℝ) * (2:ℝ)^k
  have L0 : 0 ≤ L := by dsimp [L]; positivity
  have M0 : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨(2:ℝ)^N * (L*M), by positivity, ?_⟩
  intro a support B B0 mass x
  have negForm : 𝓕⁻ (a : E → ℂ) = (𝓕 (a : E → ℂ)) ∘ (LinearIsometryEquiv.neg ℝ (E := E)) := by
    funext ξ
    exact Real.fourierIntegralInv_eq_fourierIntegral_neg _ _
  have powerBound (n : ℕ) (hn : n ≤ N) :
      ‖x‖^n * ‖iteratedFDeriv ℝ k (𝓕⁻ (a : E → ℂ)) x‖ ≤ L * (M * B) := by
    let J := range (k+1) ×ˢ range (n+1)
    have weighted (p j : ℕ) (hp : p ≤ k) (hj : j ≤ N) :
        (∫ ξ, ‖ξ‖^p * ‖iteratedFDeriv ℝ j (a : E → ℂ) ξ‖) ≤ (2:ℝ)^k * B := by
      let g := fun ξ => ‖iteratedFDeriv ℝ j (a : E → ℂ) ξ‖
      have gi : Integrable g := by
        simpa only [g, pow_zero, one_mul] using a.integrable_pow_mul_iteratedFDeriv volume 0 j
      have point (ξ : E) : ‖ξ‖^p * g ξ ≤ (2:ℝ)^k * g ξ := by
        by_cases hr : ‖ξ‖ ≤ 2
        · exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (norm_nonneg _) hr _).trans
            (pow_le_pow_right₀ (by norm_num) hp)) (norm_nonneg _)
        · have out : ξ ∉ tsupport (iteratedFDeriv ℝ j (a : E → ℂ)) := fun hs =>
            hr (by simpa only [mem_closedBall, dist_zero_right] using support (tsupport_iteratedFDeriv_subset j hs))
          simp only [g, image_eq_zero_of_notMem_tsupport out, norm_zero, mul_zero, le_refl]
      calc
        _ ≤ ∫ ξ, (2:ℝ)^k * g ξ := integral_mono (a.integrable_pow_mul_iteratedFDeriv volume p j)
          (gi.const_mul _) point
        _ ≤ _ := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (mass j hj) (by positivity)
    have sums : (∑ p ∈ J, ∫ ξ, ‖ξ‖^p.1 * ‖iteratedFDeriv ℝ p.2 (a : E → ℂ) ξ‖)
        ≤ M * B := by
      calc
        _ ≤ ∑ _p ∈ J, (2:ℝ)^k * B := by
          apply sum_le_sum
          intro p hp
          have h : p.1 < k+1 ∧ p.2 < n+1 := by
            simpa only [J, mem_product, Finset.mem_range] using hp
          exact weighted p.1 p.2 (by omega) (by omega)
        _ = ((k+1:ℕ):ℝ) * ((n+1:ℕ):ℝ) * ((2:ℝ)^k * B) := by simp [J, mul_assoc]
        _ ≤ M * B := by
          unfold M
          rw [mul_assoc _ ((2:ℝ)^k) B]
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) (mul_nonneg (by positivity) B0)
          exact_mod_cast Nat.succ_le_succ hn
    rw [negForm, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
    have ff := Real.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (K := ⊤) (N := ⊤) (k := k) (n := n)
      (a.smooth ⊤) (fun p j _ _ => a.integrable_pow_mul_iteratedFDeriv volume p j) le_top le_top (-x)
    simp only [norm_neg] at ff
    refine ff.trans ((mul_le_mul_of_nonneg_left sums (by positivity)).trans ?_)
    unfold L
    have one_le_base : (1:ℝ) ≤ 2*(k:ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ one_le_base hn) (by positivity)) (mul_nonneg M0 B0)
  have bare : ‖iteratedFDeriv ℝ k (𝓕⁻ (a : E → ℂ)) x‖ ≤ L * (M*B) := by
    simpa only [pow_zero, one_mul] using powerBound 0 (Nat.zero_le _)
  by_cases small : ‖x‖ ≤ 1
  · exact (mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith : 1+‖x‖ ≤ 2) _) bare
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · calc
      _ ≤ (2*‖x‖)^N * ‖iteratedFDeriv ℝ k (𝓕⁻ (a : E → ℂ)) x‖ := by gcongr; linarith
      _ = (2:ℝ)^N * (‖x‖^N * ‖iteratedFDeriv ℝ k (𝓕⁻ (a : E → ℂ)) x‖) := by rw [mul_pow, mul_assoc]
      _ ≤ (2:ℝ)^N * (L * (M*B)) := mul_le_mul_of_nonneg_left (powerBound N le_rfl) (by positivity)
      _ = _ := by ring

end Burnett.A02.FrequencySplit
