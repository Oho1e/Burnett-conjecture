import Burnett.Analysis.PrincipalEnergy.Commutator.CotlarStein
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section

namespace Burnett.Analysis.CotlarStein

open Set
open scoped BigOperators

def scaleGap (i j : ℕ) : ℕ := (i-j)+(j-i)

private theorem sum_geometric_under_injective (J : Finset ℕ) (f : ℕ → ℕ)
    (hinj : ∀ j ∈ J, ∀ k ∈ J, f j = f k → j = k)
    (β : ℝ) (hβ : 0 ≤ β) (hβ₁ : β < 1) :
    (∑ j ∈ J, β^(f j)) ≤ (1-β)⁻¹ := by
  have hs := (hasSum_geometric_of_lt_one hβ hβ₁).summable
  calc
    _ = ∑ u ∈ J.image f, β^u := (Finset.sum_image (fun j hj k hk eq => hinj j hj k hk eq)).symm
    _ ≤ ∑' u : ℕ, β^u := hs.sum_le_tsum _ (fun u _ => pow_nonneg hβ u)
    _ = _ := tsum_geometric_of_lt_one hβ hβ₁

/-- Each dyadic distance occurs at most twice in a row, uniformly in the
choice of finite scales. -/
theorem finite_geometric_row_le (J : Finset ℕ) (i : ℕ) (β : ℝ)
    (hβ : 0 ≤ β) (hβ₁ : β < 1) :
    (∑ j ∈ J, β^(scaleGap i j)) ≤ 2*(1-β)⁻¹ := by
  classical
  let L := J.filter (fun j => j ≤ i)
  let R := J.filter (fun j => i < j)
  have hp : (∑ j ∈ J, β^(scaleGap i j)) =
      (∑ j ∈ L, β^(scaleGap i j)) + (∑ j ∈ R, β^(scaleGap i j)) := by
    let g := fun j : ℕ => β^(scaleGap i j)
    have h := Finset.sum_filter_add_sum_filter_not (s := J) (p := fun j => j ≤ i) g
    simpa only [L,R,not_le,g] using h.symm
  have hl (j : ℕ) (hj : j ∈ L) : scaleGap i j = i-j :=
    by have h := (Finset.mem_filter.mp hj).2; unfold scaleGap; omega
  have hr (j : ℕ) (hj : j ∈ R) : scaleGap i j = j-i :=
    by have h := (Finset.mem_filter.mp hj).2; unfold scaleGap; omega
  have hLeft : (∑ j ∈ L, β^(scaleGap i j)) ≤ (1-β)⁻¹ := by
    rw [Finset.sum_congr rfl (fun j hj => congrArg (fun n : ℕ => β^n) (hl j hj))]
    refine sum_geometric_under_injective L (fun j => i-j) (fun j hj k hk eq => ?_) β hβ hβ₁
    have hj' := (Finset.mem_filter.mp hj).2
    have hk' := (Finset.mem_filter.mp hk).2
    change i-j = i-k at eq
    omega
  have hRight : (∑ j ∈ R, β^(scaleGap i j)) ≤ (1-β)⁻¹ := by
    rw [Finset.sum_congr rfl (fun j hj => congrArg (fun n : ℕ => β^n) (hr j hj))]
    refine sum_geometric_under_injective R (fun j => j-i) (fun j hj k hk eq => ?_) β hβ hβ₁
    have hj' := (Finset.mem_filter.mp hj).2
    have hk' := (Finset.mem_filter.mp hk).2
    change j-i = k-i at eq
    omega
  rw [hp,two_mul]
  exact add_le_add hLeft hRight

variable {A : Type*} [NormedRing A] [NormOneClass A] [StarRing A] [CStarRing A]

/-- Genuine finite Cotlar–Stein with dyadic separation for any subset of
nonnegative scale indices. -/
theorem norm_sum_le_of_geometric_cross_bounds (T : ℕ → A) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hδ₁ : δ < 1)
    (hL : ∀ i j, ‖star (T i) * T j‖ ≤ D*δ^(scaleGap i j))
    (hR : ∀ i j, ‖T i * star (T j)‖ ≤ D*δ^(scaleGap i j))
    (J : Finset ℕ) :
    ‖∑ j ∈ J, T j‖ ≤ 2*Real.sqrt D*(1-Real.sqrt δ)⁻¹ := by
  classical
  let β := Real.sqrt δ
  let C := Real.sqrt D
  have hb : 0 ≤ β := Real.sqrt_nonneg _
  have hb' : β < 1 := by
    simpa only [β,Real.sqrt_one] using Real.sqrt_lt_sqrt hδ hδ₁
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hPos : 0 ≤ (1-β)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hb'.le)
  let w (i j : J) := C*β^(scaleGap i j)
  have hW (i j : J) : 0 ≤ w i j := mul_nonneg hC (pow_nonneg hb _)
  have hsq (i j : J) : (w i j)^2 = D*δ^(scaleGap i j) := by
    dsimp only [w]
    rw [mul_pow,Real.sq_sqrt hD,← pow_mul,mul_comm (scaleGap (i:ℕ) (j:ℕ)) 2,
      pow_mul,Real.sq_sqrt hδ]
  have hLambda : 0 ≤ 2*C*(1-β)⁻¹ := mul_nonneg (mul_nonneg (by norm_num) hC) hPos
  have hRow (i : J) : ∑ j : J, w i j ≤ 2*C*(1-β)⁻¹ := by
    change (∑ j : J, C*β^(scaleGap i j)) ≤ _
    rw [← Finset.mul_sum]
    have h := finite_geometric_row_le J i β hb hb'
    rw [← Finset.sum_attach J (fun j => β^(scaleGap i j))] at h
    exact (mul_le_mul_of_nonneg_left h hC).trans_eq (by ring)
  have h := norm_sum_le_of_cotlar_weight (fun i : J => T i) w hW
    (fun i j => (hL i j).trans_eq (hsq i j).symm)
    (fun i j => (hR i j).trans_eq (hsq i j).symm) _ hLambda hRow
  rw [← Finset.sum_attach J T]
  exact h

end Burnett.Analysis.CotlarStein
