import Burnett.Analysis.PrincipalEnergy.Commutator.GeometricRows
import Burnett.Analysis.PrincipalEnergy.Commutator.ReproductionLimit

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Burnett.Analysis.CotlarStein
open scoped BigOperators

/-- The square-root ratio for the actual natural-index reconstruction scales
is the geometric weight of the distance between the two indices. -/
theorem reproducingScale_ratio_sqrt {t : ℝ} (ht : 0<t) (N i j : ℕ) (hij : i≤j) :
    reproducingScale t N j≤reproducingScale t N i ∧
      Real.sqrt (reproducingScale t N j/reproducingScale t N i)=
        (Real.sqrt (1/2:ℝ))^(scaleGap i j) := by
  let b := t*(2:ℝ)^N
  have hb : 0<b := by dsimp only [b]; positivity
  have hI : 0<reproducingScale t N i := by
    change 0<b/(2:ℝ)^i
    positivity
  have hPow : (2:ℝ)^j=(2:ℝ)^i*(2:ℝ)^(j-i) := by
    rw [← pow_add,Nat.add_sub_of_le hij]
  have hRatio : reproducingScale t N j/reproducingScale t N i=(1/2:ℝ)^(j-i) := by
    change (b/(2:ℝ)^j)/(b/(2:ℝ)^i)=(1/2:ℝ)^(j-i)
    rw [hPow,div_pow,one_pow]
    field_simp [hb.ne']
  refine ⟨(div_le_one hI).mp (by
    rw [hRatio]
    exact pow_le_one₀ (by norm_num : 0≤(1/2:ℝ)) (by norm_num : (1/2:ℝ)≤1)),?_⟩
  have hGap : scaleGap i j=j-i := by unfold scaleGap; omega
  have hRoot (n : ℕ) : Real.sqrt ((1/2:ℝ)^n)=(Real.sqrt (1/2:ℝ))^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,Real.sqrt_mul (pow_nonneg (by norm_num : 0≤(1/2:ℝ)) n),ih,pow_succ]
  rw [hRatio,hGap,hRoot]

/-- Geometric block bounds sum over independent finite windows with their
true square functions. The constant is uniform in both windows. -/
theorem finite_geometric_wavelet_pair_bound (c : ℕ → ℕ → ℂ)
    (a b : ℕ → ℝ)
    (D β : ℝ) (hD : 0≤D) (hβ : 0≤β) (hβ₁ : β<1)
    (hTerm : ∀ i j, ‖c i j‖≤D*β^(scaleGap i j)*a i*b j)
    (I J : Finset ℕ) :
    ‖∑ i ∈ I, ∑ j ∈ J, c i j‖≤D*(2*(1-β)⁻¹)*
      Real.sqrt (∑ i ∈ I, a i^2)*Real.sqrt (∑ j ∈ J, b j^2) := by
  let M := 2*(1-β)⁻¹
  have hM : 0≤M := mul_nonneg (by norm_num) (inv_nonneg.mpr (sub_nonneg.mpr hβ₁.le))
  let w (i j : ℕ) := β^(scaleGap i j)
  have hw (i j : ℕ) : 0≤w i j := pow_nonneg hβ _
  have hSym (i j : ℕ) : w i j=w j i := by
    dsimp only [w,scaleGap]
    rw [Nat.add_comm (i-j)]
  let S := I ×ˢ J
  let A (p : ℕ × ℕ) := Real.sqrt (w p.1 p.2)*a p.1
  let B (p : ℕ × ℕ) := Real.sqrt (w p.1 p.2)*b p.2
  have hEq (i j : ℕ) : A (i,j)*B (i,j)=w i j*a i*b j := by
    dsimp only [A,B]
    calc
      _ = (Real.sqrt (w i j))^2*a i*b j := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i j)]
  have hASq : (∑ p ∈ S, A p^2)≤M*(∑ i ∈ I, a i^2) := by
    dsimp only [S,A]
    rw [Finset.sum_product]
    simp_rw [mul_pow,Real.sq_sqrt (hw _ _),← Finset.sum_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (finite_geometric_row_le J i β hβ hβ₁)
      (sq_nonneg _)
  have hBSq : (∑ p ∈ S, B p^2)≤M*(∑ j ∈ J, b j^2) := by
    dsimp only [S,B]
    rw [Finset.sum_product,Finset.sum_comm]
    simp_rw [mul_pow,Real.sq_sqrt (hw _ _),← Finset.sum_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    simpa only [hSym _ j] using finite_geometric_row_le I j β hβ hβ₁
  have hSum : ‖∑ i ∈ I, ∑ j ∈ J, c i j‖≤D*(∑ p ∈ S, A p*B p) := by
    calc
      _ ≤ ∑ i ∈ I, ∑ j ∈ J, ‖c i j‖ := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i ∈ I, ∑ j ∈ J, D*(A (i,j)*B (i,j)) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [hEq]
        exact (hTerm i j).trans_eq (by dsimp only [w]; ring)
      _ = _ := by simp only [S,Finset.sum_product,Finset.mul_sum]
  calc
    _ ≤ D*(∑ p ∈ S, A p*B p) := hSum
    _ ≤ D*(Real.sqrt (∑ p ∈ S, A p^2)*Real.sqrt (∑ p ∈ S, B p^2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt S A B) hD
    _ ≤ D*(Real.sqrt (M*(∑ i ∈ I, a i^2))*Real.sqrt (M*(∑ j ∈ J, b j^2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt hASq) (Real.sqrt_le_sqrt hBSq)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hD
    _ = _ := by
      rw [Real.sqrt_mul hM,Real.sqrt_mul hM]
      calc
        _ = D*(Real.sqrt M)^2*Real.sqrt (∑ i ∈ I, a i^2)*Real.sqrt (∑ j ∈ J, b j^2) := by ring
        _ = _ := by rw [Real.sq_sqrt hM]

end Burnett.Analysis.CarlesonEmbedding
