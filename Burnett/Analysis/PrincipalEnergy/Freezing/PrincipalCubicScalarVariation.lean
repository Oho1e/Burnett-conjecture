import Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalCubicPolynomial
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped ContDiff

/-- Differentiate the actual cubic integral in the second real parameter,
holding the first parameter fixed. -/
theorem principal_cubic_action_hasDerivAt_second_parameter {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (u v : J → E → ℂ)
    (hu : ∀ i, BoundedCoordinateJet (u i)) (hv : ∀ i, BoundedCoordinateJet (v i)) (s : ℝ) :
    HasDerivAt (fun t : ℝ => principalCubicAction C (fun i y => s • u i y + t • v i y))
      (s^2 • (∫ x, principalCubicLinearDensity (fun a d i j k => C a d i j k) u v x)) 0 := by
  let A := principalCubicAction C u
  let B := ∫ x, principalCubicLinearDensity (fun a d i j k => C a d i j k) u v x
  let D := ∫ x, principalCubicLinearDensity (fun a d i j k => C a d i j k) v u x
  let P := principalCubicAction C v
  have form : (fun t : ℝ => principalCubicAction C (fun i y => s • u i y + t • v i y)) =
      (fun t : ℝ => s^3 • A + (s^2*t) • B + (s*t^2) • D + t^3 • P) :=
    funext (principal_cubic_action_polynomial C u v hu hv s)
  have constant : HasDerivAt (fun _ : ℝ => s^3 • A) 0 0 := hasDerivAt_const _ _
  have linear : HasDerivAt (fun t : ℝ => (s^2*t) • B) (s^2 • B) 0 := by
    simpa only [mul_one] using (((hasDerivAt_id' (0 : ℝ)).const_mul (s^2)).smul_const B)
  have quadratic : HasDerivAt (fun t : ℝ => (s*t^2) • D) 0 0 := by
    simpa using (((hasDerivAt_pow 2 (0 : ℝ)).const_mul s).smul_const D)
  have cubic : HasDerivAt (fun t : ℝ => t^3 • P) 0 0 := by
    simpa using ((hasDerivAt_pow 3 (0 : ℝ)).smul_const P)
  rw [form]
  simpa using (((constant.add linear).add quadratic).add cubic)

/-- The actual repeated first-direction derivative of the one test-direction
derivative gives the factor two in the homogeneous cubic polarization. -/
theorem principal_cubic_action_mixed_third_derivative {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (u v : J → E → ℂ)
    (hu : ∀ i, BoundedCoordinateJet (u i)) (hv : ∀ i, BoundedCoordinateJet (v i)) :
    deriv (fun s : ℝ => deriv (fun r : ℝ => deriv (fun t : ℝ =>
      principalCubicAction C (fun i y => r • u i y + t • v i y)) 0) s) 0 =
      (2 : ℝ) • (∫ x, principalCubicLinearDensity (fun a d i j k => C a d i j k) u v x) := by
  let B := ∫ x, principalCubicLinearDensity (fun a d i j k => C a d i j k) u v x
  have first : (fun r : ℝ => deriv (fun t : ℝ =>
      principalCubicAction C (fun i y => r • u i y + t • v i y)) 0) =
        (fun r : ℝ => r^2 • B) :=
    funext (fun r => (principal_cubic_action_hasDerivAt_second_parameter C u v hu hv r).deriv)
  have second : (fun s : ℝ => deriv (fun r : ℝ => r^2 • B) s) = (fun s : ℝ => (2*s) • B) := by
    funext s
    simpa using ((hasDerivAt_pow 2 s).smul_const B).deriv
  rw [first, second]
  simpa only [mul_one] using (((hasDerivAt_id' (0 : ℝ)).const_mul 2).smul_const B).deriv

theorem principal_variation_action_derivatives {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) (hw : ∀ i, BoundedCoordinateJet (w i)) :
    let V := ∫ x, principalVariationDensity (fun a d i j k => C a d i j k) z w x
    HasDerivAt (fun t : ℝ => principalCubicAction C (fun i y => z i y + t • w i y)) V 0 ∧
      deriv (fun s : ℝ => deriv (fun r : ℝ => deriv (fun t : ℝ =>
        principalCubicAction C (fun i y => r • z i y + t • w i y)) 0) s) 0 = (2 : ℝ) • V := by
  have hz (i : J) : BoundedCoordinateJet (fun y => z i y) := schwartz_bounded_coordinate_jet (z i)
  constructor
  · simpa [principal_cubic_linear_density_eq_variation] using
      principal_cubic_action_hasDerivAt_second_parameter C (fun i y => z i y) w hz hw 1
  · simpa only [principal_cubic_linear_density_eq_variation] using
      principal_cubic_action_mixed_third_derivative C (fun i y => z i y) w hz hw

/-- The action derivative and the polarization normalization on the actual
separated test. -/
theorem separated_principal_variation_action_derivatives {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (f : SchwartzMap E ℂ) (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) :
    let w (i : J) := separatedSkewAction f b (z i)
    let V := ∫ x, principalVariationDensity (fun a d i j k => C a d i j k) z w x
    HasDerivAt (fun t : ℝ => principalCubicAction C (fun i y => z i y + t • w i y)) V 0 ∧
      deriv (fun s : ℝ => deriv (fun r : ℝ => deriv (fun t : ℝ =>
        principalCubicAction C (fun i y => r • z i y + t • w i y)) 0) s) 0 = (2 : ℝ) • V :=
  principal_variation_action_derivatives C z _ (fun i => separated_skew_bounded_coordinate_jet f b hb hom (z i))

end Burnett.A02.FrequencySplit
