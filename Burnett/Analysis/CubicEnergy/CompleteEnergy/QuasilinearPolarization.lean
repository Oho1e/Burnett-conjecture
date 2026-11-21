import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearEstimate

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff ENNReal

/-- The sum of component L³ gradient norms on the finite field space. -/
def fieldEnergyGradientNorm {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) : ℝ≥0∞ :=
  ∑ i, energyGradientNorm (u i)

/-- One ordered quasilinear pairing before taking the real polarization. -/
def quasilinearMixedPairing {J : Type} [Fintype J] (b : E → ℝ)
    (A : EnergyIndex J → SchwartzMap E ℂ) (u v : J → SchwartzMap E ℂ) : ℂ :=
  ∑ k : EnergyIndex J, ∫ x, A k x *
    energyPartial k.1.1 (energyPartial k.1.2 (u k.2.2)) x *
    conj (radianAction b (v k.2.1) x)

/-- The polarization of the complete quasilinear energy in its two field slots. -/
def quasilinearSymmetricEnergy {J : Type} [Fintype J] (b : E → ℝ)
    (A : EnergyIndex J → SchwartzMap E ℂ) (u v : J → SchwartzMap E ℂ) : ℝ :=
  (quasilinearMixedPairing b A u v + quasilinearMixedPairing b A v u).im

theorem quasilinearSymmetricEnergy_diag {J : Type} [Fintype J] (b : E → ℝ)
    (A : EnergyIndex J → SchwartzMap E ℂ) (u : J → SchwartzMap E ℂ) :
    quasilinearSymmetricEnergy b A u u = 2 * (quasilinearPairing b A u).im := by
  change (quasilinearPairing b A u + quasilinearPairing b A u).im = _
  rw [Complex.add_im, two_mul]

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

/-- Estimate the two mixed quasilinear terms together by applying the diagonal
estimate to a coefficient coupling the two copies of the field space. -/
theorem quasilinear_polarized_estimate (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {J : Type} [Fintype J]
    (A : EnergyIndex J → SchwartzMap E ℂ) (u v : J → SchwartzMap E ℂ),
      (∀ a d i j x, conj (A ((a,d),(i,j)) x) = A ((d,a),(j,i)) x) →
      ENNReal.ofReal |quasilinearSymmetricEnergy b A u v| ≤
        C * ((∑ k, energyGradientNorm (A k)) * (fieldEnergyGradientNorm u * fieldEnergyGradientNorm v)) := by
  obtain ⟨K, hK, bound⟩ := quasilinear_imaginary_estimate b hb hom
  refine ⟨K * 2, ENNReal.mul_lt_top hK (by norm_num), ?_⟩
  intro J _ A u v hA
  have hDouble : ∀ a d (i j : J ⊕ J) x,
      conj (doubledCoefficient A ((a,d),(i,j)) x) = doubledCoefficient A ((d,a),(j,i)) x := by
    intro a d i j x
    cases i <;> cases j <;> simp [doubledCoefficient, hA]
  have dbl := bound (doubledCoefficient A) (Sum.elim u v) hDouble
  rw [doubled_pairing] at dbl
  change ENNReal.ofReal |2 * quasilinearSymmetricEnergy b A u v| ≤ _ at dbl
  have less (r : ℝ) : |r| ≤ |2 * r| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [abs_nonneg r]
  calc
    _ ≤ ENNReal.ofReal |2 * quasilinearSymmetricEnergy b A u v| := ENNReal.ofReal_le_ofReal (less _)
    _ ≤ _ := dbl
    _ ≤ _ := mul_le_mul_left' (doubled_gradient_bound A u v) K
    _ = _ := by rw [mul_assoc]

end Burnett.A02.FrequencySplit
