import Burnett.Analysis.CubicEnergy.JointMultiplier.JointKernelMoment
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Finset Filter
open scoped ContDiff FourierTransform

/-- The oscillatory integral estimate uses only the L¹ norms of the Cartesian
derivatives of the frequency profile through the indicated integer order. -/
theorem symbol_inverse_decay (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : SchwartzMap Freq8 ℂ)
    (B : ℝ), 0≤B → (∀ n : ℕ, n≤N → (∫ ξ, ‖iteratedFDeriv ℝ n (A : Freq8 → ℂ) ξ‖) ≤ B) →
    ∀ x : Freq8, (1+‖x‖)^N * ‖𝓕⁻ (A : Freq8 → ℂ) x‖ ≤ C*B := by
  let D := (2:ℝ)^N * (N+1:ℕ)
  have dpos : 0≤D := by dsimp [D]; positivity
  refine ⟨(2:ℝ)^N * (1+D),by positivity,?_⟩
  intro A B hB hA x
  have hp (n : ℕ) (hn : n≤N) : ‖x‖^n * ‖𝓕⁻ (A : Freq8 → ℂ) x‖ ≤ (2:ℝ)^n * ((n+1:ℕ)*B) := by
    let J := range (0+1) ×ˢ range (n+1)
    have s : (∑ p ∈ J, ∫ v, ‖v‖^p.1 * ‖iteratedFDeriv ℝ p.2 (A : Freq8 → ℂ) v‖) ≤ (n+1:ℕ)*B := by
      calc
        _ ≤ ∑ _q ∈ J, B := by
          apply sum_le_sum
          intro q hq
          have h : q.1<1 ∧ q.2<n+1 := by simpa only [J,mem_product,mem_range] using hq
          have h0 : q.1=0 := by omega
          simpa only [h0,pow_zero,one_mul] using hA q.2 (by omega)
        _ = _ := by simp [J]
    have ff := Real.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (K := ⊤) (N := ⊤) (k := 0) (n := n)
      (A.smooth ⊤) (fun k m _ _ => A.integrable_pow_mul_iteratedFDeriv volume k m) le_top le_top (-x)
    rw [Real.fourierIntegralInv_eq_fourierIntegral_neg]
    simp only [norm_neg,norm_iteratedFDeriv_zero,pow_zero,one_mul,Nat.cast_zero,mul_zero,zero_add] at ff
    exact ff.trans (mul_le_mul_of_nonneg_left s (by positivity))
  have b0 : ‖𝓕⁻ (A : Freq8 → ℂ) x‖ ≤ B := by simpa using hp 0 (Nat.zero_le _)
  have bN : ‖x‖^N * ‖𝓕⁻ (A : Freq8 → ℂ) x‖ ≤ D*B := (hp N le_rfl).trans_eq (mul_assoc _ _ _).symm
  by_cases h : ‖x‖ ≤ 1
  · calc
      _ ≤ (2:ℝ)^N*B := mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _) b0 (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) N) dpos) hB]
  · calc
      _ ≤ (2*‖x‖)^N * ‖𝓕⁻ (A : Freq8 → ℂ) x‖ := by gcongr; linarith
      _ = (2:ℝ)^N * (‖x‖^N * ‖𝓕⁻ (A : Freq8 → ℂ) x‖) := by rw [mul_pow,mul_assoc]
      _ ≤ (2:ℝ)^N * (D*B) := mul_le_mul_of_nonneg_left bN (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) N) hB]

/-- In eight dimensions, nine extra derivatives suffice to integrate the
pointwise decay after paying a polynomial translation weight of total order n. -/
theorem symbol_inverse_weighted_L1 (n : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ (A : SchwartzMap Freq8 ℂ)
    (B : ℝ), 0≤B → (∀ i : ℕ, i≤n+9 → (∫ ξ, ‖iteratedFDeriv ℝ i (A : Freq8 → ℂ) ξ‖) ≤ B) →
    (∫ x, (1+‖x‖)^n * ‖𝓕⁻ (A : Freq8 → ℂ) x‖) ≤ C*B := by
  let W := fun x : Freq8 => ((1+‖x‖)^9)⁻¹
  have hw : Integrable W := by
    have dim : Module.finrank ℝ Freq8 = 8 := by simp [Freq8,finrank_euclideanSpace]
    have hi := integrable_one_add_norm (μ := (volume : Measure Freq8)) (r := 9) (by rw [dim]; norm_num)
    refine hi.congr (Eventually.of_forall fun x => ?_)
    change (1+‖x‖)^(-(9:ℝ)) = ((1+‖x‖)^9)⁻¹
    rw [Real.rpow_neg (by positivity)]
    norm_num
  obtain ⟨K,hK,h⟩ := symbol_inverse_decay (n+9)
  have non : 0≤∫ x, W x := integral_nonneg (fun _ => by dsimp [W]; positivity)
  refine ⟨K*(∫ x, W x),mul_nonneg hK non,?_⟩
  intro A B hB b
  let F := fun x : Freq8 => (1+‖x‖)^n * ‖𝓕⁻ (A : Freq8 → ℂ) x‖
  have point (x : Freq8) : F x ≤ (K*B)*W x := by
    have d := h A B hB b x
    change _ ≤ (K*B)*((1+‖x‖)^9)⁻¹
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [F,pow_add,mul_right_comm _ (‖𝓕⁻ (A : Freq8 → ℂ) x‖)] using d
  have hF : Integrable F := by
    let G := (SchwartzMap.fourierTransformCLE ℂ).symm A
    have eg : (G : Freq8 → ℂ) = 𝓕⁻ (A : Freq8 → ℂ) := SchwartzMap.fourierTransformCLE_symm_apply _ _
    have m : Continuous F := by change Continuous (fun x => (1+‖x‖)^n * ‖𝓕⁻ (A : Freq8 → ℂ) x‖); rw [← eg]; fun_prop
    apply (hw.const_mul (K*B)).mono' m.aestronglyMeasurable
    exact Eventually.of_forall (fun x => (Real.norm_of_nonneg (show 0≤F x by dsimp [F]; positivity)).le.trans (point x))
  exact (integral_mono hF (hw.const_mul _) point).trans_eq (by rw [integral_const_mul]; ring)

end Burnett.A02.FrequencySplit
