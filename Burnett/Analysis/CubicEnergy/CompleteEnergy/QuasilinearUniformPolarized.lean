import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearPolarization
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearUniformDiagonal

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff ENNReal

private def doubledCoefficient {J : Type} (A : EnergyIndex J → SchwartzMap E ℂ) :
    EnergyIndex (J ⊕ J) → SchwartzMap E ℂ
  | ((a,d),(.inl i,.inr j)) => A ((a,d),(i,j))
  | ((a,d),(.inr i,.inl j)) => A ((a,d),(i,j))
  | _ => 0

private theorem sum_doubled_cross {J : Type} [Fintype J] {M : Type*} [AddCommMonoid M]
    (F : EnergyIndex (J ⊕ J) → M)
    (hL : ∀ a d i j, F ((a,d),(.inl i,.inl j)) = 0)
    (hR : ∀ a d i j, F ((a,d),(.inr i,.inr j)) = 0) :
    (∑ k, F k) =
      (∑ k : EnergyIndex J, F (k.1,(.inl k.2.1,.inr k.2.2))) +
      (∑ k : EnergyIndex J, F (k.1,(.inr k.2.1,.inl k.2.2))) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, hL, hR,
    Finset.sum_const_zero, zero_add, add_zero]
  simp_rw [Finset.sum_add_distrib]

private theorem doubled_pairing {J : Type} [Fintype J] (b : E → ℝ)
    (A : EnergyIndex J → SchwartzMap E ℂ) (u v : J → SchwartzMap E ℂ) :
    quasilinearPairing b (doubledCoefficient A) (Sum.elim u v) =
      quasilinearMixedPairing b A u v + quasilinearMixedPairing b A v u := by
  unfold quasilinearPairing
  let F (k : EnergyIndex (J ⊕ J)) := ∫ x, doubledCoefficient A k x *
    energyPartial k.1.1 (energyPartial k.1.2 (Sum.elim u v k.2.2)) x *
    conj (radianAction b (Sum.elim u v k.2.1) x)
  change (∑ k, F k) = _
  rw [sum_doubled_cross F]
  · change quasilinearMixedPairing b A v u + quasilinearMixedPairing b A u v = _
    exact add_comm _ _
  · intro a d i j
    simp [F, doubledCoefficient]
  · intro a d i j
    simp [F, doubledCoefficient]

set_option maxHeartbeats 800000 in
private theorem energyGradientNorm_zero : energyGradientNorm (0 : SchwartzMap E ℂ) = 0 := by
  change eLpNorm (fderiv ℝ (0 : E → ℂ)) (ENNReal.ofReal 3) volume = 0
  rw [fderiv_zero]
  exact eLpNorm_zero (ε := E →L[ℝ] ℂ) (p := ENNReal.ofReal 3) (μ := (volume : Measure E))

private theorem field_component_norm_le {J : Type} [Fintype J]
    (u : J → SchwartzMap E ℂ) (i : J) :
    energyGradientNorm (u i) ≤ fieldEnergyGradientNorm u := by
  classical
  exact Finset.single_le_sum (fun j _ => zero_le (energyGradientNorm (u j))) (Finset.mem_univ i)

private theorem doubled_gradient_bound {J : Type} [Fintype J]
    (A : EnergyIndex J → SchwartzMap E ℂ) (u v : J → SchwartzMap E ℂ) :
    (∑ k : EnergyIndex (J ⊕ J), energyGradientNorm (doubledCoefficient A k) *
      (energyGradientNorm (Sum.elim u v k.2.2) * energyGradientNorm (Sum.elim u v k.2.1))) ≤
      2 * ((∑ k, energyGradientNorm (A k)) * (fieldEnergyGradientNorm u * fieldEnergyGradientNorm v)) := by
  classical
  let F (k : EnergyIndex (J ⊕ J)) := energyGradientNorm (doubledCoefficient A k) *
    (energyGradientNorm (Sum.elim u v k.2.2) * energyGradientNorm (Sum.elim u v k.2.1))
  let D := fieldEnergyGradientNorm u * fieldEnergyGradientNorm v
  change (∑ k, F k) ≤ 2 * ((∑ k, energyGradientNorm (A k)) * D)
  rw [sum_doubled_cross F]
  · rw [two_mul, Finset.sum_mul]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro k _
      change energyGradientNorm (A k) *
        (energyGradientNorm (v k.2.2) * energyGradientNorm (u k.2.1)) ≤ _
      rw [mul_comm (energyGradientNorm (v k.2.2))]
      exact mul_le_mul_left' (mul_le_mul' (field_component_norm_le u _) (field_component_norm_le v _)) _
    · apply Finset.sum_le_sum
      intro k _
      change energyGradientNorm (A k) *
        (energyGradientNorm (u k.2.2) * energyGradientNorm (v k.2.1)) ≤ _
      exact mul_le_mul_left' (mul_le_mul' (field_component_norm_le u _) (field_component_norm_le v _)) _
  · intro a d i j
    simp [F, doubledCoefficient, energyGradientNorm_zero]
  · intro a d i j
    simp [F, doubledCoefficient, energyGradientNorm_zero]

/-- The two mixed terms have a common bound with the same symbol control. -/
theorem quasilinear_polarized_sphere_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ {J : Type} [Fintype J] (A : EnergyIndex J → SchwartzMap E ℂ) (u v : J → SchwartzMap E ℂ),
      (∀ a d i j x, conj (A ((a,d),(i,j)) x) = A ((d,a),(j,i)) x) →
      ENNReal.ofReal |quasilinearSymmetricEnergy b A u v| ≤ C * ENNReal.ofReal D *
        ((∑ k, energyGradientNorm (A k)) * (fieldEnergyGradientNorm u * fieldEnergyGradientNorm v)) := by
  obtain ⟨K, hK, bound⟩ := quasilinear_imaginary_sphere_bound
  refine ⟨K * 2, ENNReal.mul_lt_top hK (by norm_num), ?_⟩
  intro b hb hom D hD jet J _ A u v hA
  have hDouble : ∀ a d (i j : J ⊕ J) x,
      conj (doubledCoefficient A ((a,d),(i,j)) x) = doubledCoefficient A ((d,a),(j,i)) x := by
    intro a d i j x
    cases i <;> cases j <;> simp [doubledCoefficient, hA]
  have dbl := bound b hb hom D hD jet (doubledCoefficient A) (Sum.elim u v) hDouble
  rw [doubled_pairing] at dbl
  change ENNReal.ofReal |2 * quasilinearSymmetricEnergy b A u v| ≤ _ at dbl
  have less (r : ℝ) : |r| ≤ |2 * r| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [abs_nonneg r]
  calc
    _ ≤ ENNReal.ofReal |2 * quasilinearSymmetricEnergy b A u v| := ENNReal.ofReal_le_ofReal (less _)
    _ ≤ _ := dbl
    _ ≤ _ := mul_le_mul_left' (doubled_gradient_bound A u v) (K * ENNReal.ofReal D)
    _ = _ := by ring

end Burnett.A02.FrequencySplit
