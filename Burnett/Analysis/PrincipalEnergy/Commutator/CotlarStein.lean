import Burnett.Analysis.PrincipalEnergy.Commutator.FiniteRows

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.CotlarStein

open scoped BigOperators

variable {ι A : Type*} [Fintype ι] [NormedRing A] [NormOneClass A] [StarRing A] [CStarRing A]

private theorem alternatingPower_even (S : A) (m : ℕ) :
    alternatingPower S true (2*m) = (star S*S)^m := by
  induction m with
  | zero => simp [alternatingPower]
  | succ m ih =>
    rw [show 2*(m+1) = 2*m+1+1 by omega]
    change star S*(S*alternatingPower S true (2*m)) = _
    rw [ih,← mul_assoc,pow_succ']

/-- Finite Cotlar–Stein in a normed C*-ring. The same nonnegative
weight controls the two adjacent pairings, and its row sums control
the norm of the entire finite operator sum. -/
theorem norm_sum_le_of_cotlar_weight (T : ι → A) (w : ι → ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (h₁ : ∀ i j, ‖star (T i)*T j‖ ≤ (w i j)^2)
    (h₂ : ∀ i j, ‖T i*star (T j)‖ ≤ (w i j)^2)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (hRow : ∀ i, ∑ j, w i j ≤ Λ) :
    ‖∑ i, T i‖ ≤ Λ := by
  classical
  let S := ∑ i, T i
  let M := ∑ i, ‖T i‖
  let C := (Fintype.card ι : ℝ)*M
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hT (i : ι) : ‖T i‖ ≤ M :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hPower (n : ℕ) : ‖S‖^(2*2^n) ≤ C*Λ^(2*2^n-1) := by
    have hn : 1 ≤ 2*(2:ℕ)^n := by
      have hp : 0 < (2:ℕ)^n := by positivity
      omega
    have h := norm_alternatingPower_sum_le T w hw h₁ h₂ Λ hΛ hRow M hM hT true (2*2^n-1)
    change ‖alternatingPower S true ((2*2^n-1)+1)‖ ≤ C*Λ^(2*2^n-1) at h
    rw [Nat.sub_add_cancel hn,alternatingPower_even,
      (IsSelfAdjoint.star_mul_self S).norm_pow_two_pow,CStarRing.norm_star_mul_self,
      ← pow_two,← pow_mul] at h
    exact h
  change ‖S‖ ≤ Λ
  rcases hΛ.eq_or_lt with hZero | hPos
  · have h := hPower 0
    rw [← hZero] at h ⊢
    norm_num at h
    simp [h]
  by_contra! hLt
  have hOne : 1 < ‖S‖/Λ := (one_lt_div₀ hPos).mpr hLt
  have hRatio (n : ℕ) : (‖S‖/Λ)^(2*2^n) ≤ C/Λ := by
    have hOneNat : 1 ≤ 2*(2:ℕ)^n := by
      have hPosNat : 0 < (2:ℕ)^n := by positivity
      omega
    have hExponent : 2*(2:ℕ)^n-1+1 = 2*2^n := Nat.sub_add_cancel hOneNat
    have hPowEq : Λ^(2*(2:ℕ)^n) = Λ^(2*2^n-1)*Λ := by
      calc
        _ = Λ^(2*2^n-1+1) := congrArg (fun k : ℕ => Λ^k) hExponent.symm
        _ = _ := pow_succ ..
    calc
      _ = ‖S‖^(2*2^n)/Λ^(2*2^n) := div_pow ..
      _ ≤ (C*Λ^(2*2^n-1))/Λ^(2*2^n) :=
        div_le_div_of_nonneg_right (hPower n) (pow_nonneg hΛ _)
      _ = _ := by
        rw [hPowEq]
        field_simp [hPos.ne']
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (C/Λ) hOne
  have hn' : n ≤ 2*(2:ℕ)^n := by
    have hp : n < (2:ℕ)^n := Nat.lt_two_pow_self
    omega
  exact (not_lt_of_ge ((pow_le_pow_right₀ hOne.le hn').trans (hRatio n))) hn

end Burnett.Analysis.CotlarStein
