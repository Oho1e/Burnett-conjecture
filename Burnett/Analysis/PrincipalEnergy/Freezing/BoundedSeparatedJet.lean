import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSkewDifferentiation

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped ContDiff FourierTransform RealInnerProductSpace

/-- Pointwise boundedness on the action domain, for the field and every actual
first coordinate derivative. -/
def BoundedCoordinateJet (u : E → ℂ) : Prop :=
  Differentiable ℝ u ∧ (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖u x‖ ≤ M) ∧
    ∀ a : Index, ∃ M : ℝ, 0 ≤ M ∧ ∀ x,
      ‖fderiv ℝ u x (EuclideanSpace.single a 1)‖ ≤ M

private theorem schwartz_value_bound (u : SchwartzMap E ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖u x‖ ≤ M := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 u, apply_nonneg _ _, fun x => ?_⟩
  simpa using SchwartzMap.le_seminorm ℝ 0 0 u x

theorem schwartz_bounded_coordinate_jet (u : SchwartzMap E ℂ) :
    BoundedCoordinateJet (u : E → ℂ) :=
  ⟨u.differentiable, schwartz_value_bound u, fun j => schwartz_value_bound (energyPartial j u)⟩

private theorem radian_skew_value_bound (b : E → ℝ) (u : SchwartzMap E ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖radianSkewAction b u x‖ ≤ M := by
  let S := radianActionSpectrum b u
  refine ⟨∫ ξ, ‖S ξ‖, integral_nonneg (fun _ => norm_nonneg _), fun x => ?_⟩
  rw [radianSkewAction, norm_mul, norm_neg, Complex.norm_I, one_mul,
    ← radianActionSpectrum_inverse, Real.fourierIntegralInv_eq_fourierIntegral_neg]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ E) S (-x)

theorem radian_skew_bounded_coordinate_jet (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (u : SchwartzMap E ℂ) :
    BoundedCoordinateJet (radianSkewAction b u) := by
  refine ⟨fun x => (radian_skew_coordinate_derivative b hb hom u x).1,
    radian_skew_value_bound b u, fun j => ?_⟩
  obtain ⟨M, hM, bound⟩ := radian_skew_value_bound b (energyPartial j u)
  exact ⟨M, hM, fun x => by
    rw [(radian_skew_coordinate_derivative b hb hom u x).2 j]
    exact bound x⟩

private theorem separated_skew_value_bound (f : SchwartzMap E ℂ) (b : E → ℝ)
    (u : SchwartzMap E ℂ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖separatedSkewAction f b u x‖ ≤ M := by
  obtain ⟨A, hA, hF⟩ := schwartz_value_bound f
  obtain ⟨B, hB, hU⟩ := radian_skew_value_bound b u
  obtain ⟨C, hC, hP⟩ := radian_skew_value_bound b (energyProduct f u)
  refine ⟨(A*B+C)/2, div_nonneg (add_nonneg (mul_nonneg hA hB) hC) (by norm_num), fun x => ?_⟩
  rw [separatedSkewAction, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  exact add_le_add (mul_le_mul (hF x) (hU x) (norm_nonneg _) hA) (hP x)

/-- The actual separated test belongs to the domain of the cubic integral
along with the Schwartz field on which it acts. -/
theorem separated_skew_bounded_coordinate_jet (f : SchwartzMap E ℂ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (u : SchwartzMap E ℂ) :
    BoundedCoordinateJet (separatedSkewAction f b u) := by
  refine ⟨fun x => (separated_skew_coordinate_commutator f b hb hom u x 0).1,
    separated_skew_value_bound f b u, fun j => ?_⟩
  obtain ⟨A, hA, h₁⟩ := separated_skew_value_bound (energyPartial j f) b u
  obtain ⟨B, hB, h₂⟩ := separated_skew_value_bound f b (energyPartial j u)
  refine ⟨A+B, add_nonneg hA hB, fun x => ?_⟩
  rw [sub_eq_iff_eq_add.mp (separated_skew_coordinate_commutator f b hb hom u x j).2]
  exact (norm_add_le _ _).trans (add_le_add (h₁ x) (h₂ x))

end Burnett.A02.FrequencySplit
