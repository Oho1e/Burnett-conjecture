import Burnett.Analysis.CubicEnergy.CompleteEnergy.CompleteCubicContinuity

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Finset
open scoped BigOperators ENNReal

/-- The symmetric real trilinear map with the same diagonal as T. -/
def symmetricAverageCubic {F : Type} [AddCommGroup F] [Module ℝ F]
    (T : MultilinearMap ℝ (fun _ : Fin 3 => F) ℝ) :
    MultilinearMap ℝ (fun _ : Fin 3 => F) ℝ :=
  (6 : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin 3), T.domDomCongr σ

private theorem permutations_card : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  norm_num [Fintype.card_perm, Nat.factorial_succ]

private def permutationAfter (τ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 3) ≃ Equiv.Perm (Fin 3) where
  toFun σ := σ.trans τ
  invFun σ := σ.trans τ.symm
  left_inv σ := by ext i; simp
  right_inv σ := by ext i; simp

theorem symmetricAverageCubic_permute {F : Type} [AddCommGroup F] [Module ℝ F]
    (T : MultilinearMap ℝ (fun _ : Fin 3 => F) ℝ) (v : Fin 3 → F) (τ : Equiv.Perm (Fin 3)) :
    symmetricAverageCubic T (v ∘ τ) = symmetricAverageCubic T v := by
  simp only [symmetricAverageCubic, MultilinearMap.smul_apply, MultilinearMap.sum_apply,
    MultilinearMap.domDomCongr_apply, Function.comp_apply]
  congr 1
  exact Fintype.sum_equiv (permutationAfter τ) (fun σ => T (fun i => v (τ (σ i))))
    (fun σ => T (fun i => v (σ i))) (fun _ => rfl)

theorem symmetricAverageCubic_diag {F : Type} [AddCommGroup F] [Module ℝ F]
    (T : MultilinearMap ℝ (fun _ : Fin 3 => F) ℝ) (u : F) :
    symmetricAverageCubic T (fun _ => u) = T (fun _ => u) := by
  simp only [symmetricAverageCubic, MultilinearMap.smul_apply, MultilinearMap.sum_apply,
    MultilinearMap.domDomCongr_apply, sum_const, card_univ, permutations_card, nsmul_eq_mul,
    Nat.cast_ofNat, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (6 : ℝ) ≠ 0), one_mul]

theorem symmetricAverageCubic_bound {F : Type} [AddCommGroup F] [Module ℝ F]
    (T : MultilinearMap ℝ (fun _ : Fin 3 => F) ℝ) (G : F → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ v : Fin 3 → F, ‖T v‖ₑ ≤ C * ∏ i, G (v i)) (v : Fin 3 → F) :
    ‖symmetricAverageCubic T v‖ₑ ≤ C * ∏ i, G (v i) := by
  let mass := ∏ i, G (v i)
  have each (σ : Equiv.Perm (Fin 3)) : ‖T (fun i => v (σ i))‖ₑ ≤ C * mass := by
    refine (h (fun i => v (σ i))).trans_eq ?_
    exact congrArg (C * ·) (Fintype.prod_equiv σ _ _ (fun _ => rfl))
  have one : ‖(6 : ℝ)⁻¹‖ₑ * (6 : ℝ≥0∞) = 1 := by
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by positivity : 0 ≤ (6 : ℝ)⁻¹),
      show (6 : ℝ≥0∞) = ENNReal.ofReal (6 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (6 : ℝ)⁻¹)]
    norm_num
  simp only [symmetricAverageCubic, MultilinearMap.smul_apply, MultilinearMap.sum_apply,
    MultilinearMap.domDomCongr_apply, smul_eq_mul, enorm_mul]
  change ‖(6 : ℝ)⁻¹‖ₑ * ‖∑ σ : Equiv.Perm (Fin 3), T (fun i => v (σ i))‖ₑ ≤ C * mass
  calc
    _ ≤ ‖(6 : ℝ)⁻¹‖ₑ * (∑ _σ : Equiv.Perm (Fin 3), C * mass) :=
      mul_le_mul_left' ((enorm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => each σ)) _
    _ = _ := by
      simp only [sum_const, card_univ, permutations_card, nsmul_eq_mul, Nat.cast_ofNat]
      rw [← mul_assoc ‖(6 : ℝ)⁻¹‖ₑ, one, one_mul]

private def triple {F : Type} (a b c : F) : Fin 3 → F :=
  Fin.cons a (Fin.cons b (fun _ : Fin 1 => c))

@[simp] private theorem triple_zero {F : Type} (a b c : F) : triple a b c 0 = a := rfl
@[simp] private theorem triple_one {F : Type} (a b c : F) : triple a b c 1 = b := rfl
@[simp] private theorem triple_two {F : Type} (a b c : F) : triple a b c 2 = c := rfl

private theorem triple_diag {F : Type} (u : F) : triple u u u = fun _ => u := by
  funext i
  fin_cases i <;> rfl

private theorem update_triple_zero {F : Type} (a b c d : F) :
    Function.update (triple a b c) 0 d = triple d b c := by
  funext i
  fin_cases i <;> rfl

private theorem update_triple_one {F : Type} (a b c d : F) :
    Function.update (triple a b c) 1 d = triple a d c := by
  funext i
  fin_cases i <;> rfl

private theorem update_triple_two {F : Type} (a b c d : F) :
    Function.update (triple a b c) 2 d = triple a b d := by
  funext i
  fin_cases i <;> rfl

private theorem trilinear_diag_sub {F : Type} [AddCommGroup F] [Module ℝ F]
    (T : MultilinearMap ℝ (fun _ : Fin 3 => F) ℝ) (u v : F) :
    T (fun _ => u) - T (fun _ => v) =
      T (triple (u-v) u u) + T (triple v (u-v) u) + T (triple v v (u-v)) := by
  have h₀ := T.map_update_sub (triple u u u) (0 : Fin 3) u v
  have h₁ := T.map_update_sub (triple v u u) (1 : Fin 3) u v
  have h₂ := T.map_update_sub (triple v v u) (2 : Fin 3) u v
  rw [update_triple_zero,update_triple_zero,update_triple_zero] at h₀
  rw [update_triple_one,update_triple_one,update_triple_one] at h₁
  rw [update_triple_two,update_triple_two,update_triple_two] at h₂
  rw [← triple_diag u,← triple_diag v,h₀,h₁,h₂]
  ring

/-- A three-slot estimate controls the difference of two diagonals in the
same three norms. -/
theorem trilinear_diagonal_enorm_bound {F : Type} [AddCommGroup F] [Module ℝ F]
    (T : MultilinearMap ℝ (fun _ : Fin 3 => F) ℝ) (G : F → ℝ≥0∞) (C : ℝ≥0∞)
    (estimate : ∀ w : Fin 3 → F, ‖T w‖ₑ ≤ C * ∏ i, G (w i)) (u v : F) :
    ‖T (fun _ => u) - T (fun _ => v)‖ₑ ≤ C * G (u-v) * (G u + G v)^2 := by
  let U := G u
  let V := G v
  let N := G (u-v)
  rw [trilinear_diag_sub]
  have head : ‖T (triple (u-v) u u)‖ₑ ≤ C * (N*U*U) := by
    simpa only [Fin.prod_univ_three,triple_zero,triple_one,triple_two] using estimate (triple (u-v) u u)
  have middle : ‖T (triple v (u-v) u)‖ₑ ≤ C * (V*N*U) := by
    simpa only [Fin.prod_univ_three,triple_zero,triple_one,triple_two] using estimate (triple v (u-v) u)
  have last : ‖T (triple v v (u-v))‖ₑ ≤ C * (V*V*N) := by
    simpa only [Fin.prod_univ_three,triple_zero,triple_one,triple_two] using estimate (triple v v (u-v))
  change ‖T (triple (u-v) u u) + T (triple v (u-v) u) + T (triple v v (u-v))‖ₑ ≤
    C*N*(U+V)^2
  calc
    _ ≤ C*(N*U*U) + C*(V*N*U) + C*(V*V*N) :=
      (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans (add_le_add head middle)) last)
    _ ≤ C*(N*U*U) + C*(V*N*U) + C*(V*V*N) + C*(V*N*U) :=
      le_add_of_nonneg_right (zero_le _)
    _ = _ := by ring

end Burnett.A02.FrequencySplit
