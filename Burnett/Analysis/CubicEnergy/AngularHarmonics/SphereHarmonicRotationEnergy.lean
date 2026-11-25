import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicCoefficientDecay

set_option autoImplicit false
set_option maxHeartbeats 7200000

noncomputable section

namespace Burnett.A06

open Metric MeasureTheory
open scoped BigOperators ContDiff ENNReal

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The actual real L² class of an ambient continuous test restricted to S³. -/
def roundSphereRestrictionLp {f : RotationSpace → ℝ} (hf : Continuous f) : RoundSphereL2 :=
  ContinuousMap.toLp 2 roundSphere3Measure ℝ ⟨fun x => f x, hf.comp continuous_subtype_val⟩

theorem roundSphereRestrictionLp_norm_sq {f : RotationSpace → ℝ} (hf : Continuous f) :
    ‖roundSphereRestrictionLp hf‖ ^ 2 = ∫ x : RoundSphere3, f x * f x ∂roundSphere3Measure := by
  rw [← real_inner_self_eq_norm_sq, roundSphereRestrictionLp, ContinuousMap.inner_toLp]
  simp

private theorem integrable_rotation_product {f g : RotationSpace → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x : RoundSphere3 => f x * g x) roundSphere3Measure :=
  ((hf.mul hg).comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem contDiff_planeRotationDerivative_of_two {f : RotationSpace → ℝ} (hf : ContDiff ℝ 2 f)
    (i j : Fin 4) : ContDiff ℝ 1 (planeRotationDerivative i j f) :=
  contDiff_planeRotationDerivative (by simpa only [one_add_one_eq_two] using hf) i j

/-- The true L² rotation energy on the sphere is the negative Casimir pairing. -/
theorem roundSphere_rotationEnergy_eq {f : RotationSpace → ℝ} (hf : ContDiff ℝ 2 f) :
    (∑ p ∈ rotationPairs, ‖roundSphereRestrictionLp (contDiff_planeRotationDerivative_of_two hf p.1 p.2).continuous‖^2) =
      -∫ x : RoundSphere3, planeRotationCasimir f x * f x ∂roundSphere3Measure := by
  let D (p : Fin 4 × Fin 4) := planeRotationDerivative p.1 p.2 f
  have df (p) : ContDiff ℝ 1 (D p) := contDiff_planeRotationDerivative_of_two hf p.1 p.2
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  let H (p : Fin 4 × Fin 4) (x : RoundSphere3) := planeRotationDerivative p.1 p.2 (D p) x * f x
  have hH (p) : Integrable (H p) roundSphere3Measure :=
    integrable_rotation_product (continuous_planeRotationDerivative _ _ (df p)) hf.continuous
  have hi :
      (∫ x : RoundSphere3, planeRotationCasimir f x * f x ∂roundSphere3Measure) =
      ∑ p ∈ rotationPairs, ∫ x, H p x ∂roundSphere3Measure := by
    simpa only [planeRotationCasimir, Finset.sum_mul, H, D] using
      (integral_finset_sum rotationPairs (fun p _ => hH p))
  rw [hi, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have h := integral_planeRotationDerivative_mul (ne_of_lt ((mem_rotationPairs p.1 p.2).mp hp)) (df p) hf₁
  rw [roundSphereRestrictionLp_norm_sq]
  change (∫ x : RoundSphere3, D p x * D p x ∂roundSphere3Measure) =
      -(∫ x : RoundSphere3, planeRotationDerivative p.1 p.2 (D p) x * f x ∂roundSphere3Measure)
  rw [h, neg_neg]

/-- The actual pointwise Casimir eigenvalue for every homogeneous harmonic
polynomial, evaluated on the genuine round unit sphere. -/
theorem sphereHarmonicPolynomial_casimir (d : ℕ) (P : sphereHarmonicSubmodule d) (x : RoundSphere3) :
    planeRotationCasimir (spherePolynomialValue P.val.val) x =
      -((d : ℝ) * ((d : ℝ) + 2)) * spherePolynomialValue P.val.val x := by
  have hp : polynomialLaplacian P.val.val = 0 := mem_sphereHarmonicSubmodule_iff.mp P.property
  exact planeRotationCasimir_harmonic_on_sphere (contDiff_infty.mp (spherePolynomialValue_contDiff _) 2)
    d (fun t _ y => sphereHomogeneousValue_smul d P.val t y) (fun y => by
      rw [spherePolynomialValue_laplacian, hp]
      simp [spherePolynomialValue]) x

theorem sphereHarmonicRotation_continuous (d : ℕ) (P : sphereHarmonicSubmodule d)
    (i j : Fin 4) :
    Continuous (planeRotationDerivative i j (spherePolynomialValue P.val.val)) :=
  (contDiff_planeRotationDerivative_of_two (contDiff_infty.mp (spherePolynomialValue_contDiff _) 2) i j).continuous

/-- The sum of the six genuine rotation energies of a degree-d harmonic
is d(d+2) times its genuine spherical L² energy. -/
theorem sphereHarmonic_rotationEnergy_eq (d : ℕ) (P : sphereHarmonicSubmodule d) :
    (∑ p ∈ rotationPairs, ‖roundSphereRestrictionLp (sphereHarmonicRotation_continuous d P p.1 p.2)‖^2) =
      (d : ℝ) * ((d : ℝ) + 2) * ‖sphereHarmonicToLp d P‖^2 := by
  let f := spherePolynomialValue P.val.val
  have hc : Continuous f := (spherePolynomialValue_contDiff _).continuous
  change (∑ p ∈ rotationPairs, ‖roundSphereRestrictionLp (sphereHarmonicRotation_continuous d P p.1 p.2)‖^2) =
      (d : ℝ) * ((d : ℝ) + 2) * ‖roundSphereRestrictionLp hc‖^2
  rw [roundSphere_rotationEnergy_eq (contDiff_infty.mp (spherePolynomialValue_contDiff _) 2),
      roundSphereRestrictionLp_norm_sq]
  have h (x : RoundSphere3) : planeRotationCasimir f x * f x =
      (-((d : ℝ) * ((d : ℝ) + 2))) * (f x * f x) := by
    rw [sphereHarmonicPolynomial_casimir d P x]
    change (-((d : ℝ) * ((d : ℝ) + 2)) * f x) * f x = _
    ring
  change -(∫ x : RoundSphere3, planeRotationCasimir f x * f x ∂roundSphere3Measure) =
    (d : ℝ) * ((d : ℝ) + 2) * ∫ x : RoundSphere3, f x * f x ∂roundSphere3Measure
  simp only [h]
  rw [integral_const_mul, neg_mul, neg_neg]

/-- Each actual rotation generator has this uniform L² bound on the degree-d
harmonic subspace, with respect to the same spherical surface measure. -/
theorem norm_sphereHarmonic_rotation_le (d : ℕ) (P : sphereHarmonicSubmodule d)
    (p : Fin 4 × Fin 4) (hp : p ∈ rotationPairs) :
    ‖roundSphereRestrictionLp (sphereHarmonicRotation_continuous d P p.1 p.2)‖ ≤
      Real.sqrt ((d : ℝ) * ((d : ℝ) + 2)) * ‖sphereHarmonicToLp d P‖ := by
  have hsum := Finset.single_le_sum
    (f := fun p : Fin 4 × Fin 4 => ‖roundSphereRestrictionLp (sphereHarmonicRotation_continuous d P p.1 p.2)‖^2)
    (fun _ _ => sq_nonneg _) hp
  rw [sphereHarmonic_rotationEnergy_eq] at hsum
  have hn : 0 ≤ (d : ℝ) * ((d : ℝ) + 2) := by positivity
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt hn]
  exact hsum

end Burnett.A06
