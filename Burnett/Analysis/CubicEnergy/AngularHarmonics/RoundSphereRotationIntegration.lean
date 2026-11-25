import Burnett.Analysis.CubicEnergy.AngularHarmonics.RoundSphereRotations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A06

open MeasureTheory Set Metric Filter
open scoped Topology ContDiff

local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))

/-- Apply the coordinate rotation generator to the ambient C¹ test. -/
def planeRotationDerivative (i j : Fin 4) (f : RotationSpace → ℝ) (x : RotationSpace) : ℝ :=
  fderiv ℝ f x (planeRotationGenerator i j x)

theorem planeRotationDerivative_eq_coordinates (i j : Fin 4) (f : RotationSpace → ℝ)
    (x : RotationSpace) :
    planeRotationDerivative i j f x =
      x i * fderiv ℝ f x (EuclideanSpace.single j 1) -
        x j * fderiv ℝ f x (EuclideanSpace.single i 1) := by
  simp only [planeRotationDerivative, planeRotationGenerator_eq, map_sub, map_smul, smul_eq_mul]

theorem continuous_planeRotationDerivative (i j : Fin 4) {f : RotationSpace → ℝ}
    (hf : ContDiff ℝ 1 f) : Continuous (planeRotationDerivative i j f) :=
  (hf.continuous_fderiv le_rfl).clm_apply (continuous_planeRotationGenerator i j)

theorem hasDerivAt_rotateRoundSphere3_test {i j : Fin 4} (hij : i ≠ j)
    {f : RotationSpace → ℝ} (hf : ContDiff ℝ 1 f) (x : RoundSphere3) (t : ℝ) :
    HasDerivAt (fun u => f (rotateRoundSphere3 hij u x))
      (planeRotationDerivative i j f (rotateRoundSphere3 hij t x)) t := by
  have h := HasFDerivAt.comp_hasDerivAt t
    (hf.differentiable_one (planeRotation hij t x)).hasFDerivAt (hasDerivAt_planeRotation hij t x)
  simpa only [Function.comp_apply, coe_rotateRoundSphere3, planeRotationDerivative] using h

private theorem integrable_roundSphere3_of_continuous {f : RotationSpace → ℝ} (hf : Continuous f) :
    Integrable (fun x : RoundSphere3 => f x) roundSphere3Measure := by
  obtain ⟨C,hC⟩ := (isCompact_sphere (0 : RotationSpace) 1).exists_bound_of_continuousOn hf.continuousOn
  refine Integrable.of_bound (hf.comp continuous_subtype_val).aestronglyMeasurable C ?_
  exact Eventually.of_forall fun x => hC x x.property

/-- Differentiating the rotation-invariant round integral gives zero integral
for the generator of a C¹ test restricted to the sphere. -/
theorem integral_planeRotationDerivative_eq_zero {i j : Fin 4} (hij : i ≠ j)
    {f : RotationSpace → ℝ} (hf : ContDiff ℝ 1 f) :
    (∫ x : RoundSphere3, planeRotationDerivative i j f x ∂roundSphere3Measure) = 0 := by
  let F (t : ℝ) (x : RoundSphere3) := f (rotateRoundSphere3 hij t x)
  let G (t : ℝ) (x : RoundSphere3) := planeRotationDerivative i j f (rotateRoundSphere3 hij t x)
  have continuousG := continuous_planeRotationDerivative i j hf
  obtain ⟨C,hC⟩ := (isCompact_sphere (0 : RotationSpace) 1).exists_bound_of_continuousOn
    continuousG.continuousOn
  have measF (t : ℝ) : AEStronglyMeasurable (F t) roundSphere3Measure := by
    change AEStronglyMeasurable (fun x : RoundSphere3 => f (planeRotation hij t x)) roundSphere3Measure
    exact ((hf.continuous.comp (planeRotation hij t).continuous).comp continuous_subtype_val).aestronglyMeasurable
  have int0 : Integrable (F 0) roundSphere3Measure := by
    simpa only [F, coe_rotateRoundSphere3, planeRotation_zero] using integrable_roundSphere3_of_continuous hf.continuous
  have measG : AEStronglyMeasurable (G 0) roundSphere3Measure := by
    simpa only [G, coe_rotateRoundSphere3, planeRotation_zero] using
      (continuousG.comp continuous_subtype_val).aestronglyMeasurable
  have der := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := G) (x₀ := 0) (ε := 1) (bound := fun _ : RoundSphere3 => C)
    zero_lt_one (Eventually.of_forall measF) int0 measG
    (Eventually.of_forall fun x t _ => hC _ (rotateRoundSphere3 hij t x).property)
    (integrable_const C)
    (Eventually.of_forall fun x t _ => hasDerivAt_rotateRoundSphere3_test hij hf x t)).2
  have constant : (fun t : ℝ => ∫ x, F t x ∂roundSphere3Measure) =
      fun _ => ∫ x : RoundSphere3, f x ∂roundSphere3Measure :=
    funext fun t => integral_rotateRoundSphere3 hij t (fun x => f x)
  rw [constant] at der
  simpa only [G, coe_rotateRoundSphere3, planeRotation_zero] using
    der.unique (hasDerivAt_const (0 : ℝ) (∫ x : RoundSphere3, f x ∂roundSphere3Measure))

/-- Coordinate-plane rotation generators are skew-adjoint in the real round
sphere pairing on restrictions of ambient C¹ tests. -/
theorem integral_planeRotationDerivative_mul {i j : Fin 4} (hij : i ≠ j)
    {f g : RotationSpace → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    (∫ x : RoundSphere3, planeRotationDerivative i j f x * g x ∂roundSphere3Measure) =
      -∫ x : RoundSphere3, f x * planeRotationDerivative i j g x ∂roundSphere3Measure := by
  have hprod : (fun x : RoundSphere3 => planeRotationDerivative i j (f * g) x) =
      fun x : RoundSphere3 => planeRotationDerivative i j f x * g x + f x * planeRotationDerivative i j g x := by
    funext x
    rw [planeRotationDerivative, fderiv_mul (hf.differentiable_one x) (hg.differentiable_one x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      planeRotationDerivative]
    ring
  have ha := integrable_roundSphere3_of_continuous
    ((continuous_planeRotationDerivative i j hf).mul hg.continuous)
  have hb := integrable_roundSphere3_of_continuous
    (hf.continuous.mul (continuous_planeRotationDerivative i j hg))
  have h := integral_planeRotationDerivative_eq_zero (f := f * g) hij (hf.mul hg)
  rw [hprod, integral_add ha hb] at h
  linarith only [h]

end Burnett.A06
