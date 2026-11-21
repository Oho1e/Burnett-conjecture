import Burnett.Analysis.PrincipalEnergy.Commutator.AlternatingWords
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Burnett.Analysis.CotlarStein

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

private theorem sum_cons_tuple {R : Type*} [AddCommMonoid R] {n : ℕ}
    (g : (Fin (n+1) → ι) → R) :
    ∑ j, g j = ∑ i : ι, ∑ j : Fin n → ι, g (Fin.cons i j) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n+1) => ι)
  have h := (e.sum_comp g).symm
  rw [h,Fintype.sum_prod_type]
  rfl

theorem sum_pathWeight_le (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (hRow : ∀ i, ∑ j, w i j ≤ Λ) :
    ∀ (n : ℕ) (i : ι), (∑ t : Fin n → ι, pathWeight w (i :: List.ofFn t)) ≤ Λ^n := by
  classical
  intro n
  induction n with
  | zero => intro i; simp [pathWeight]
  | succ n ih =>
    intro i
    rw [sum_cons_tuple]
    have hStep (j : ι) (t : Fin n → ι) :
        pathWeight w (i :: List.ofFn (Fin.cons j t)) = w i j * pathWeight w (j :: List.ofFn t) := by
      simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,pathWeight]
    simp_rw [hStep,← Finset.mul_sum]
    calc
      _ ≤ ∑ j, w i j * Λ^n :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hw i j)
      _ = (∑ j, w i j)*Λ^n := (Finset.sum_mul ..).symm
      _ ≤ Λ^(n+1) := by
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_right (hRow i) (pow_nonneg hΛ n)

variable {A : Type*} [NormedRing A] [NormOneClass A] [StarRing A] [NormedStarGroup A]

def alternatingPower (s : A) : Bool → ℕ → A
  | _, 0 => 1
  | b, n+1 => (if b then star s else s) * alternatingPower s (!b) n

theorem alternatingPower_sum (T : ι → A) : ∀ (n : ℕ) (b : Bool),
    alternatingPower (∑ i, T i) b n =
      ∑ t : Fin n → ι, alternatingProduct T b (List.ofFn t) := by
  classical
  intro n
  induction n with
  | zero => intro b; simp [alternatingPower,alternatingProduct]
  | succ n ih =>
    intro b
    rw [sum_cons_tuple]
    have hStep (i : ι) (j : Fin n → ι) :
        alternatingProduct T b (List.ofFn (Fin.cons i j)) =
          letter T b i * alternatingProduct T (!b) (List.ofFn j) := by
      simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,alternatingProduct]
    simp_rw [hStep,← Finset.mul_sum,← Finset.sum_mul]
    rw [alternatingPower,ih (!b)]
    congr 1
    cases b
    · simp [letter]
    · simpa only [letter,if_true] using map_sum (starAddEquiv : A ≃+ A) T Finset.univ

theorem norm_alternatingPower_sum_le (T : ι → A) (w : ι → ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (h₁ : ∀ i j, ‖star (T i) * T j‖ ≤ (w i j)^2)
    (h₂ : ∀ i j, ‖T i * star (T j)‖ ≤ (w i j)^2)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (hRow : ∀ i, ∑ j, w i j ≤ Λ)
    (M : ℝ) (hM : 0 ≤ M) (hT : ∀ i, ‖T i‖ ≤ M) (b : Bool) (n : ℕ) :
    ‖alternatingPower (∑ i, T i) b (n+1)‖ ≤ ((Fintype.card ι : ℝ)*M)*Λ^n := by
  classical
  rw [alternatingPower_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [sum_cons_tuple]
  have hStep (i : ι) (j : Fin n → ι) : List.ofFn (Fin.cons i j) = i :: List.ofFn j := by
    simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ]
  simp_rw [hStep]
  calc
    _ ≤ ∑ i : ι, ∑ j : Fin n → ι, M*pathWeight w (i :: List.ofFn j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        alternatingProduct_path_bound T w hw h₁ h₂ M hM hT b i (List.ofFn j)
    _ = ∑ _i : ι, M*(∑ j : Fin n → ι, pathWeight w (_i :: List.ofFn j)) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ _i : ι, M*Λ^n := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (sum_pathWeight_le w hw Λ hΛ hRow n i) hM
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end Burnett.Analysis.CotlarStein
