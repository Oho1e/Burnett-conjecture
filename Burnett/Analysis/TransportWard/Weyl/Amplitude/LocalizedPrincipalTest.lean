import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearIBP

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Filter MeasureTheory Set Topology Burnett.RicciSymbol
open scoped BigOperators

/-- The three test placements in the variation of the principal cubic action. -/
def principalVariationDensity {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ)
    (z : J → SchwartzMap E ℂ) (w : J → E → ℂ) (x : E) : ℂ :=
  ∑ a : Index, ∑ d : Index, ∑ i : J, ∑ j : J, ∑ k : J, C a d i j k x *
    (w i x * energyPartial a (z j) x * energyPartial d (z k) x +
      z i x * fderiv ℝ (w j) x (EuclideanSpace.single a 1) * energyPartial d (z k) x +
      z i x * energyPartial a (z j) x * fderiv ℝ (w k) x (EuclideanSpace.single d 1))

/-- Insert the same spatial cutoff on both sides of a scalar test. -/
def sandwichedScalarTest (χ : SchwartzMap E ℂ)
    (Q : SchwartzMap E ℂ → E → ℂ) (u : SchwartzMap E ℂ) (x : E) : ℂ :=
  χ x * Q (energyProduct χ u) x

/-- A cutoff equal to one on an open neighborhood of the field's supports
leaves all three actual test placements unchanged in the principal variation. -/
theorem principal_variation_sandwiched_test {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (z : J → SchwartzMap E ℂ)
    (Q : SchwartzMap E ℂ → E → ℂ) (χ : SchwartzMap E ℂ)
    (U : Set E) (hU : IsOpen U)
    (support : ∀ i, tsupport (z i : E → ℂ) ⊆ U) (one : ∀ x ∈ U, χ x = 1) :
    principalVariationDensity C z (fun i => sandwichedScalarTest χ Q (z i)) =
      principalVariationDensity C z (fun i => Q (z i)) := by
  have input (i : J) : energyProduct χ (z i) = z i := by
    ext x
    rw [energyProduct_apply]
    by_cases hx : x ∈ U
    · rw [one x hx, one_mul]
    have hz : z i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hs => hx (support i hs))
    rw [hz, mul_zero]
  funext x
  by_cases hx : x ∈ U
  · have values (i : J) : sandwichedScalarTest χ Q (z i) x = Q (z i) x := by
      rw [sandwichedScalarTest, input i, one x hx, one_mul]
    have equalNear (i : J) :
        sandwichedScalarTest χ Q (z i) =ᶠ[𝓝 x] Q (z i) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [sandwichedScalarTest, input i, one y hy, one_mul]
    have derivatives (i : J) :
        fderiv ℝ (sandwichedScalarTest χ Q (z i)) x = fderiv ℝ (Q (z i)) x :=
      (equalNear i).fderiv_eq
    simp only [principalVariationDensity, values, derivatives]
  · have outside (i : J) : x ∉ tsupport (z i : E → ℂ) := fun hs => hx (support i hs)
    have zeros (i : J) : z i x = 0 := image_eq_zero_of_notMem_tsupport (outside i)
    have first (i : J) (a : Index) : energyPartial a (z i) x = 0 := by
      change fderiv ℝ (z i) x (EuclideanSpace.single a 1) = 0
      rw [fderiv_of_notMem_tsupport ℝ (outside i), ContinuousLinearMap.zero_apply]
    simp only [principalVariationDensity, zeros, first, mul_zero, zero_mul,
      add_zero, Finset.sum_const_zero]

theorem principal_variation_integral_sandwiched_test {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (z : J → SchwartzMap E ℂ)
    (Q : SchwartzMap E ℂ → E → ℂ) (χ : SchwartzMap E ℂ)
    (U : Set E) (hU : IsOpen U)
    (support : ∀ i, tsupport (z i : E → ℂ) ⊆ U) (one : ∀ x ∈ U, χ x = 1) :
    (∫ x, principalVariationDensity C z (fun i => sandwichedScalarTest χ Q (z i)) x) =
      ∫ x, principalVariationDensity C z (fun i => Q (z i)) x := by
  rw [principal_variation_sandwiched_test C z Q χ U hU support one]

end Burnett.A02.FrequencySplit
