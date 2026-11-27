import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSkewL3
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSkewDifferentiation
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FieldAndCoefficientChecks

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit

open MeasureTheory Metric Burnett.RicciSymbol Burnett.A02.FieldAndCoefficientReview
open scoped BigOperators ContDiff ENNReal

private theorem energyPartial_Linfty_le_actual_derivatives (j : Index) (f : SchwartzMap E ℂ) :
    eLpNorm (energyPartial j f : E → ℂ) ⊤ volume ≤ eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume ∧
      eLpNorm (fderiv ℝ (energyPartial j f : E → ℂ)) ⊤ volume ≤
        eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume := by
  let e : E := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  let D := fderiv ℝ (f : E → ℂ)
  constructor
  · apply eLpNorm_mono
    intro x
    change ‖D x e‖ ≤ ‖D x‖
    simpa only [he, mul_one] using (D x).le_opNorm e
  · apply eLpNorm_mono
    intro x
    let eval := ContinuousLinearMap.apply ℝ ℂ e
    have evalNorm : ‖eval‖ ≤ 1 := by
      apply eval.opNorm_le_bound zero_le_one
      intro L
      simpa only [eval, ContinuousLinearMap.apply_apply, he, mul_one, one_mul] using L.le_opNorm e
    have hD : DifferentiableAt ℝ D x := (SchwartzMap.fderivCLM ℝ f).differentiable x
    have shape : (energyPartial j f : E → ℂ) = eval ∘ D := by
      funext y
      rfl
    have deriv := eval.hasFDerivAt.comp x hD.hasFDerivAt
    rw [shape, deriv.fderiv]
    calc
      _ ≤ ‖eval‖ * ‖fderiv ℝ D x‖ := eval.opNorm_comp_le _
      _ ≤ ‖fderiv ℝ D x‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right evalNorm (norm_nonneg (fderiv ℝ D x))
      _ = ‖iteratedFDeriv ℝ 1 D x‖ := by
        rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]
      _ = _ := norm_iteratedFDeriv_fderiv (n := 1)

/-- The actual coordinate commutator has the same L³ bound as the separated
test with its spatial multiplier differentiated in the chosen coordinate. -/
theorem separated_skew_coordinate_commutator_L3_sphere_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (f u : SchwartzMap E ℂ) (j : Index),
        let T (x : E) := fderiv ℝ (separatedSkewAction f b u) x (EuclideanSpace.single j 1) -
          separatedSkewAction f b (energyPartial j u) x
        MemLp T (ENNReal.ofReal 3) volume ∧
        eLpNorm T (ENNReal.ofReal 3) volume ≤ C * ENNReal.ofReal D *
          (eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume * energyGradientNorm u +
            eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume *
              eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume) := by
  obtain ⟨C, hC, bound⟩ := separated_skew_action_L3_sphere_bound
  refine ⟨C, hC, ?_⟩
  intro b hb hom D hD jet f u j T
  have eq : T = separatedSkewAction (energyPartial j f) b u :=
    funext fun x => (separated_skew_coordinate_commutator f b hb hom u x j).2
  rw [eq]
  obtain ⟨hLp, inequality⟩ := bound b hb hom D hD jet (energyPartial j f) u
  obtain ⟨hFirst, hSecond⟩ := energyPartial_Linfty_le_actual_derivatives j f
  exact ⟨hLp, inequality.trans (mul_le_mul_left'
    (add_le_add (mul_le_mul_right' hFirst _) (mul_le_mul_right' hSecond _)) _)⟩

private theorem component_estimates_le_euclidean {J : Type} [Fintype J]
    (u : J → SchwartzMap E ℂ) (T : J → E → ℂ) (c A B : ℝ≥0∞)
    (hT : ∀ i, eLpNorm (T i) (ENNReal.ofReal 3) volume ≤
      c * (A * energyGradientNorm (u i) + B * eLpNorm (u i : E → ℂ) (ENNReal.ofReal 3) volume)) :
    (∑ i, eLpNorm (T i) (ENNReal.ofReal 3) volume) ≤
      c * ((Fintype.card J : ℝ≥0∞) * Fintype.card Index) *
        (A * euclideanFieldGradientNorm u +
          B * eLpNorm (fieldValueArray u) (ENNReal.ofReal 3) volume) := by
  let M := (Fintype.card J : ℝ≥0∞) * Fintype.card Index
  let U := eLpNorm (fieldValueArray u) (ENNReal.ofReal 3) volume
  have one : (1 : ℝ≥0∞) ≤ Fintype.card Index := by
    change (1 : ℝ≥0∞) ≤ Fintype.card (Fin 4)
    simp
  have hJ : (Fintype.card J : ℝ≥0∞) ≤ M := by
    simpa only [M, mul_one] using mul_le_mul_left' one (Fintype.card J : ℝ≥0∞)
  have values : (∑ i, eLpNorm (u i : E → ℂ) (ENNReal.ofReal 3) volume) ≤ M * U :=
    (component_values_L3_le_euclidean u).trans (mul_le_mul_right' hJ U)
  calc
    _ ≤ ∑ i, c * (A * energyGradientNorm (u i) +
        B * eLpNorm (u i : E → ℂ) (ENNReal.ofReal 3) volume) := Finset.sum_le_sum (fun i _ => hT i)
    _ = c * (A * fieldEnergyGradientNorm u +
        B * ∑ i, eLpNorm (u i : E → ℂ) (ENNReal.ofReal 3) volume) := by
      unfold fieldEnergyGradientNorm
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.mul_sum]
    _ ≤ c * (A * (M * euclideanFieldGradientNorm u) + B * (M * U)) :=
      mul_le_mul_left' (add_le_add (mul_le_mul_left' (fieldEnergyGradientNorm_le_euclidean u) _)
        (mul_le_mul_left' values _)) _
    _ = c * M * (A * euclideanFieldGradientNorm u + B * U) := by ring

/-- The component sums of the actual tests are controlled by the Euclidean
value and full-gradient arrays of the same input field. -/
theorem separated_skew_field_L3_euclidean_sphere_bounds {J : Type} [Fintype J] :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (f : SchwartzMap E ℂ) (u : J → SchwartzMap E ℂ),
        let P := ENNReal.ofReal 3
        let G := euclideanFieldGradientNorm u
        let V := eLpNorm (fieldValueArray u) P volume
        let F₀ := eLpNorm (f : E → ℂ) ⊤ volume
        let F₁ := eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume
        let F₂ := eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume
        ((∀ i, MemLp (separatedSkewAction f b (u i)) P volume) ∧
          (∑ i, eLpNorm (separatedSkewAction f b (u i)) P volume) ≤ C * ENNReal.ofReal D * (F₀ * G + F₁ * V)) ∧
        ∀ j : Index,
          let T (i : J) (x : E) := fderiv ℝ (separatedSkewAction f b (u i)) x (EuclideanSpace.single j 1) -
            separatedSkewAction f b (energyPartial j (u i)) x
          (∀ i, MemLp (T i) P volume) ∧
          (∑ i, eLpNorm (T i) P volume) ≤ C * ENNReal.ofReal D * (F₁ * G + F₂ * V) := by
  obtain ⟨C₀, hC₀, value⟩ := separated_skew_action_L3_sphere_bound
  obtain ⟨C₁, hC₁, coordinate⟩ := separated_skew_coordinate_commutator_L3_sphere_bound
  let M := (Fintype.card J : ℝ≥0∞) * Fintype.card Index
  have hM : M < ⊤ := ENNReal.mul_lt_top (by simp) (by simp)
  refine ⟨(C₀ + C₁) * M, ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨hC₀, hC₁⟩) hM, ?_⟩
  intro b hb hom D hD jet f u P G V F₀ F₁ F₂
  let c := (C₀ + C₁) * ENNReal.ofReal D
  have hc₀ : C₀ * ENNReal.ofReal D ≤ c := mul_le_mul_right' (le_add_of_nonneg_right (zero_le _)) _
  have hc₁ : C₁ * ENNReal.ofReal D ≤ c := mul_le_mul_right' (le_add_of_nonneg_left (zero_le _)) _
  have factor : ((C₀ + C₁) * M) * ENNReal.ofReal D = c * M := by dsimp only [c]; ring
  rw [factor]
  constructor
  · let T (i : J) := separatedSkewAction f b (u i)
    refine ⟨fun i => (value b hb hom D hD jet f (u i)).1, ?_⟩
    exact component_estimates_le_euclidean u T c F₀ F₁ (fun i =>
      (value b hb hom D hD jet f (u i)).2.trans (mul_le_mul_right' hc₀ _))
  · intro j T
    refine ⟨fun i => (coordinate b hb hom D hD jet f (u i) j).1, ?_⟩
    exact component_estimates_le_euclidean u T c F₁ F₂ (fun i =>
      (coordinate b hb hom D hD jet f (u i) j).2.trans (mul_le_mul_right' hc₁ _))

end Burnett.A02.FrequencySplit
