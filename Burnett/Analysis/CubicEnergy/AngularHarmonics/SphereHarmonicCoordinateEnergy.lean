import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicRotationPolynomial
import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicRotationEnergy

set_option autoImplicit false
set_option maxHeartbeats 7800000

noncomputable section

namespace Burnett.A06

open MvPolynomial Metric MeasureTheory
open scoped BigOperators ContDiff ENNReal

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem coordinate_pderiv_comm (i j : Fin 4) (P : SpherePolynomial) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hp hq => simp only [map_add, hp, hq]
  | mul_X P k ih =>
    simp only [pderiv_mul, map_add]
    by_cases hki : k = i
    · subst i
      by_cases hkj : k = j
      · subst j
        rfl
      · simp [hkj, ih]
    · by_cases hkj : k = j
      · subst j
        simp [hki, ih]
      · simp [hki, hkj, ih]

/-- The Cartesian derivatives of a degree-d harmonic polynomial belong to
the degree-(d−1) harmonic subspace, with the zero derivative at degree zero. -/
def sphereHarmonicCoordinateDerivative (d : ℕ) (i : Fin 4) (H : sphereHarmonicSubmodule d) :
    sphereHarmonicSubmodule (d - 1) :=
  ⟨⟨pderiv i H.val.val, H.val.property.pderiv⟩, mem_sphereHarmonicSubmodule_iff.mpr (by
    change polynomialLaplacian (pderiv i H.val.val) = 0
    have hp : polynomialLaplacian (pderiv i H.val.val) = pderiv i (polynomialLaplacian H.val.val) := by
      simp only [polynomialLaplacian_apply, map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [coordinate_pderiv_comm k i H.val.val,
        coordinate_pderiv_comm k i (pderiv k H.val.val)]
    rw [hp, mem_sphereHarmonicSubmodule_iff.mp H.property, map_zero])⟩

private theorem homogeneousEulerValue (d : ℕ) (P : SphereHomogeneous d) (x : RotationSpace) :
    (∑ i : Fin 4, x i * spherePolynomialValue (pderiv i P.val) x) =
      (d : ℝ) * spherePolynomialValue P.val x := by
  have h := congrArg (fun Q : SpherePolynomial => (eval fun i => x i) Q)
    ((show P.val.IsHomogeneous d from P.property).sum_X_mul_pderiv)
  simpa only [spherePolynomialValue, map_sum, map_mul, eval_X, map_nsmul, nsmul_eq_mul, map_natCast] using h

private theorem sum_four_reassociated (f : Fin 4 → ℝ) :
    (∑ i : Fin 4, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + f 3)) = f 0 + f 1 + f 2 + f 3
  ring

private theorem coordinate_lagrange_identity (u v : Fin 4 → ℝ) :
    (∑ p ∈ rotationPairs, (u p.1 * v p.2 - u p.2 * v p.1)^2) + (∑ i, u i * v i)^2 =
      (∑ i, u i^2) * (∑ i, v i^2) := by
  simp (disch := decide) only [rotationPairs, Finset.sum_insert, Finset.sum_singleton,
    sum_four_reassociated]
  ring

/-- Pointwise on the actual round sphere, the Cartesian gradient energy of a
homogeneous polynomial is its angular energy plus its radial Euler energy. -/
theorem spherePolynomialValue_coordinate_energy (d : ℕ) (P : SphereHomogeneous d) (x : RoundSphere3) :
    (∑ i : Fin 4, (spherePolynomialValue (pderiv i P.val) x)^2) =
      (∑ p ∈ rotationPairs, (planeRotationDerivative p.1 p.2 (spherePolynomialValue P.val) x)^2) +
        ((d : ℝ) * spherePolynomialValue P.val x)^2 := by
  let v (i : Fin 4) := spherePolynomialValue (pderiv i P.val) x
  have hn : ‖(x : RotationSpace)‖^2 = 1 := by
    rw [mem_sphere_zero_iff_norm.mp x.property, one_pow]
  rw [EuclideanSpace.norm_sq_eq] at hn
  have hnorm : (∑ i : Fin 4, (x : RotationSpace) i ^ 2) = 1 := by
    simpa only [Real.norm_eq_abs, sq_abs] using hn
  have h := coordinate_lagrange_identity (fun i => (x : RotationSpace) i) v
  rw [hnorm, one_mul] at h
  have hEuler : (∑ i : Fin 4, (x : RotationSpace) i * v i) =
      (d : ℝ) * spherePolynomialValue P.val x := homogeneousEulerValue d P x
  rw [hEuler] at h
  have heq (p : Fin 4 × Fin 4) :
      (x : RotationSpace) p.1 * v p.2 - (x : RotationSpace) p.2 * v p.1 =
        planeRotationDerivative p.1 p.2 (spherePolynomialValue P.val) x := by
    rw [planeRotationDerivative_eq_coordinates, spherePolynomialValue_fderiv_coordinate,
      spherePolynomialValue_fderiv_coordinate]
  simp_rw [heq] at h
  exact h.symm

private theorem integrable_round_square {f : RotationSpace → ℝ} (hf : Continuous f) :
    Integrable (fun x : RoundSphere3 => (f x)^2) roundSphere3Measure :=
  ((hf.comp continuous_subtype_val).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Cartesian differentiation of a degree-d true harmonic costs at most a
linear factor in d in the same actual spherical L² norm. -/
theorem norm_sphereHarmonicCoordinateDerivative_le (d : ℕ) (H : sphereHarmonicSubmodule d)
    (i : Fin 4) :
    ‖sphereHarmonicToLp (d-1) (sphereHarmonicCoordinateDerivative d i H)‖ ≤
      (2 * ((d : ℝ) + 1)) * ‖sphereHarmonicToLp d H‖ := by
  let f := spherePolynomialValue H.val.val
  let v (j : Fin 4) := spherePolynomialValue (pderiv j H.val.val)
  let R (p : Fin 4 × Fin 4) := planeRotationDerivative p.1 p.2 f
  have hv (j) : Continuous (v j) := (spherePolynomialValue_contDiff _).continuous
  have hf : Continuous f := (spherePolynomialValue_contDiff _).continuous
  have hR (p) : Continuous (R p) := sphereHarmonicRotation_continuous d H p.1 p.2
  have he :
      (∑ j : Fin 4, ‖roundSphereRestrictionLp (hv j)‖^2) =
        (d : ℝ) * ((d : ℝ) + 2) * ‖sphereHarmonicToLp d H‖^2 +
          (d : ℝ)^2 * ‖sphereHarmonicToLp d H‖^2 := by
    rw [← sphereHarmonic_rotationEnergy_eq]
    change (∑ j : Fin 4, ‖roundSphereRestrictionLp (hv j)‖^2) =
      (∑ p ∈ rotationPairs, ‖roundSphereRestrictionLp (hR p)‖^2) + (d : ℝ)^2 * ‖roundSphereRestrictionLp hf‖^2
    simp_rw [roundSphereRestrictionLp_norm_sq, ← pow_two]
    rw [← integral_finset_sum _ (fun j _ => integrable_round_square (hv j)),
      ← integral_finset_sum _ (fun p _ => integrable_round_square (hR p)),
      ← integral_const_mul, ← integral_add (integrable_finset_sum _ (fun p _ => integrable_round_square (hR p)))
        ((integrable_round_square hf).const_mul ((d : ℝ)^2))]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun x => ?_
    convert spherePolynomialValue_coordinate_energy d H.val x using 1
    ring
  have hle := Finset.single_le_sum
    (f := fun j : Fin 4 => ‖roundSphereRestrictionLp (hv j)‖^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  rw [he] at hle
  change ‖roundSphereRestrictionLp (hv i)‖ ≤ _
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hle.trans ?_)
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hn : 0 ≤ ‖sphereHarmonicToLp d H‖^2 := sq_nonneg _
  rw [← add_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (by nlinarith) hn

end Burnett.A06
