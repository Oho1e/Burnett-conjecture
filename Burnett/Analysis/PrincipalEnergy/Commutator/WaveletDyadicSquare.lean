import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletFourierProfile
import Burnett.Analysis.PrincipalEnergy.Commutator.GeometricRows
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Burnett.Analysis.CotlarStein MeasureTheory
open scoped BigOperators

def compactWaveletScale (t : ℝ) (j : ℕ) : ℝ := t/(2:ℝ)^j

private theorem ratio_of_ordered_scales (t : ℝ) (ht : 0<t) {i j : ℕ} (h : i≤j) :
    min (compactWaveletScale t i) (compactWaveletScale t j) /
      max (compactWaveletScale t i) (compactWaveletScale t j) =
      (1/2:ℝ)^(j-i) := by
  have hBase : (0:ℝ)<2 := by norm_num
  have hOrder : compactWaveletScale t j ≤ compactWaveletScale t i :=
    div_le_div_of_nonneg_left ht.le (pow_pos hBase _) (pow_le_pow_right₀ (by norm_num) h)
  rw [min_eq_right hOrder,max_eq_left hOrder]
  calc
    _ = (2:ℝ)^i/(2:ℝ)^j := by
      unfold compactWaveletScale
      field_simp [ht.ne']
    _ = ((2:ℝ)^j/(2:ℝ)^i)⁻¹ := by rw [inv_div]
    _ = ((2:ℝ)^(j-i))⁻¹ := by
      rw [pow_sub₀ _ hBase.ne' h,div_eq_mul_inv]
    _ = _ := by rw [← inv_pow,one_div]

/-- The true inverse-dyadic scale ratio depends only on the two natural indices. -/
theorem compactWaveletScale_ratio (t : ℝ) (ht : 0<t) (i j : ℕ) :
    min (compactWaveletScale t i) (compactWaveletScale t j) /
      max (compactWaveletScale t i) (compactWaveletScale t j) =
      (1/2:ℝ)^(scaleGap i j) := by
  rcases le_total i j with h | h
  · rw [ratio_of_ordered_scales t ht h]
    congr 1
    exact (show scaleGap i j = j-i by unfold scaleGap; omega).symm
  · rw [min_comm,max_comm,ratio_of_ordered_scales t ht h]
    congr 1
    exact (show scaleGap i j = i-j by unfold scaleGap; omega).symm

/-- Uniform finite spectral square sum for the original mean-zero window,
including arbitrary finite gaps and every positive initial physical scale. -/
theorem exists_compactWaveletFrequency_square_bound (ψ : SchwartzMap Space ℂ)
    (hMean : (∫ z, ψ z) = 0) :
    ∃ D : ℝ, 0≤D ∧ ∀ (t : ℝ), 0<t → ∀ (J : Finset ℕ) (ξ : Space),
      (∑ j ∈ J, ‖compactWaveletFrequency ψ (compactWaveletScale t j • ξ)‖^2) ≤ D := by
  obtain ⟨C,hC,hCross⟩ := compactWaveletFrequency_cross ψ hMean
  refine ⟨4*C,mul_nonneg (by norm_num) hC,?_⟩
  intro t ht J ξ
  let u (j : ℕ) := ‖compactWaveletFrequency ψ (compactWaveletScale t j • ξ)‖
  by_cases hJ : J.Nonempty
  · obtain ⟨j,hj,hMax⟩ := J.exists_max_image u hJ
    have hp (i : ℕ) : 0 < compactWaveletScale t i := div_pos ht (pow_pos (by norm_num) _)
    have hSq (i : ℕ) (hi : i ∈ J) : u i^2 ≤ C*(1/2:ℝ)^(scaleGap i j) := by
      have h := hCross (compactWaveletScale t i) (compactWaveletScale t j) (hp i) (hp j) ξ
      rw [compactWaveletScale_ratio t ht i j] at h
      rw [pow_two]
      exact (mul_le_mul_of_nonneg_left (hMax i hi) (norm_nonneg _)).trans h
    have hEq (i : ℕ) : scaleGap i j = scaleGap j i := by unfold scaleGap; omega
    change (∑ i ∈ J, u i^2) ≤ _
    calc
      _ ≤ ∑ i ∈ J, C*(1/2:ℝ)^(scaleGap i j) := Finset.sum_le_sum hSq
      _ = C*∑ i ∈ J, (1/2:ℝ)^(scaleGap j i) := by simp only [hEq,Finset.mul_sum]
      _ ≤ C*(2*(1-(1/2:ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left (finite_geometric_row_le J j (1/2) (by norm_num) (by norm_num)) hC
      _ = _ := by rw [show 2*(1-(1/2:ℝ))⁻¹ = 4 by norm_num]; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hJ,Finset.sum_empty]
    positivity

end Burnett.Analysis.CarlesonEmbedding
