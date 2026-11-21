import Burnett.Analysis.PrincipalEnergy.Commutator.CompactWaveletLocalization
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory
open scoped FourierTransform NNReal

def compactWaveletFrequency (ψ : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  SchwartzMap.fourierTransformCLM ℂ ψ

/-- A genuine mean-zero Schwartz kernel has its actual Fourier profile
vanishing linearly at the origin and decaying with one spatial moment. -/
theorem compactWaveletFrequency_linear_decay (ψ : SchwartzMap Space ℂ)
    (hMean : (∫ z, ψ z) = 0) :
    ∃ A B : ℝ, 0≤A ∧ 0≤B ∧ ∀ ξ : Space,
      ‖compactWaveletFrequency ψ ξ‖ ≤ A*‖ξ‖ ∧
      ‖ξ‖*‖compactWaveletFrequency ψ ξ‖ ≤ B := by
  let a := compactWaveletFrequency ψ
  let L : NNReal := ⟨SchwartzMap.seminorm ℝ 0 1 a,apply_nonneg _ _⟩
  have hDiff : Differentiable ℝ (a : Space → ℂ) := a.differentiable
  have hLip : LipschitzWith L (a : Space → ℂ) := by
    refine lipschitzWith_of_nnnorm_fderiv_le hDiff (fun x => ?_)
    have h : ‖fderiv ℝ (a : Space → ℂ) x‖ ≤ (L : ℝ) := by
      exact (norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ (a : Space → ℂ)) (x := x)).symm.le.trans
        ((norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0)).le.trans
          (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ a 1 x))
    exact_mod_cast h
  have h0 : a 0 = 0 := by
    change 𝓕 (ψ : Space → ℂ) 0 = 0
    simpa [Real.fourierIntegral_eq] using hMean
  refine ⟨L,SchwartzMap.seminorm ℝ 1 0 a,L.coe_nonneg,apply_nonneg _ _,fun ξ => ⟨?_,?_⟩⟩
  · have h := hLip.dist_le_mul ξ 0
    simpa only [dist_eq_norm,h0,sub_zero] using h
  · simpa only [pow_one] using SchwartzMap.norm_pow_mul_le_seminorm ℝ a 1 ξ

/-- Cross-scale decay for the two genuine Fourier factors for every pair of
positive real scales. Both adjoint products have the same magnitudes. -/
theorem compactWaveletFrequency_cross (ψ : SchwartzMap Space ℂ)
    (hMean : (∫ z, ψ z) = 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ s t : ℝ, 0<s → 0<t → ∀ ξ : Space,
      ‖compactWaveletFrequency ψ (s • ξ)‖ * ‖compactWaveletFrequency ψ (t • ξ)‖ ≤
        C * (min s t / max s t) := by
  obtain ⟨A,B,hA,hB,est⟩ := compactWaveletFrequency_linear_decay ψ hMean
  let a := compactWaveletFrequency ψ
  have oneSide (s t : ℝ) (hs : 0<s) (ht : 0<t) (ξ : Space) :
      ‖a (s • ξ)‖*‖a (t • ξ)‖ ≤ (A*B)*(s/t) := by
    have hS := (est (s • ξ)).1
    have hT := (est (t • ξ)).2
    rw [norm_smul,Real.norm_of_nonneg hs.le] at hS
    rw [norm_smul,Real.norm_of_nonneg ht.le] at hT
    calc
      _ ≤ (A*(s*‖ξ‖))*‖a (t • ξ)‖ := mul_le_mul_of_nonneg_right hS (norm_nonneg _)
      _ = (A*(s/t))*((t*‖ξ‖)*‖a (t • ξ)‖) := by field_simp [ht.ne']
      _ ≤ (A*(s/t))*B := mul_le_mul_of_nonneg_left hT (mul_nonneg hA (div_nonneg hs.le ht.le))
      _ = _ := by ring
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro s t hs ht ξ
  rcases le_total s t with h | h
  · rw [min_eq_left h,max_eq_right h]
    exact oneSide s t hs ht ξ
  · rw [min_eq_right h,max_eq_left h,mul_comm ‖compactWaveletFrequency ψ (s • ξ)‖]
    exact oneSide t s ht hs ξ

end Burnett.Analysis.CarlesonEmbedding
