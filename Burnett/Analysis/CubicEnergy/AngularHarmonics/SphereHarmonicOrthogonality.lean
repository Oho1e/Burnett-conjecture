import Burnett.Analysis.CubicEnergy.AngularHarmonics.AmbientPolynomialLaplacian
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A06

open MvPolynomial Metric MeasureTheory
open scoped BigOperators ContDiff

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))
local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

private theorem planeRotationDerivative_polynomialValue (i j : Fin 4)
    (P : SpherePolynomial) :
    planeRotationDerivative i j (spherePolynomialValue P) =
      spherePolynomialValue (X i * pderiv j P - X j * pderiv i P) := by
  funext x
  rw [planeRotationDerivative_eq_coordinates, spherePolynomialValue_fderiv_coordinate,
    spherePolynomialValue_fderiv_coordinate]
  simp [spherePolynomialValue]

private theorem contDiff_planeRotationDerivative_polynomialValue (i j : Fin 4)
    (P : SpherePolynomial) (n : ℕ) :
    ContDiff ℝ n (planeRotationDerivative i j (spherePolynomialValue P)) := by
  rw [planeRotationDerivative_polynomialValue]
  exact contDiff_infty.mp (spherePolynomialValue_contDiff _) n

private theorem integrable_spherical_product {f g : RotationSpace → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x : RoundSphere3 => f x * g x) roundSphere3Measure :=
  ((hf.mul hg).comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Double integration by parts for the six actual rotation generators on the
same round sphere and with the same sphere measure as the harmonic basis. -/
theorem integral_planeRotationCasimir_mul_polynomialValue (P Q : SpherePolynomial) :
    (∫ x : RoundSphere3, planeRotationCasimir (spherePolynomialValue P) x *
      spherePolynomialValue Q x ∂roundSphere3Measure) =
    ∫ x : RoundSphere3, spherePolynomialValue P x *
      planeRotationCasimir (spherePolynomialValue Q) x ∂roundSphere3Measure := by
  let f := spherePolynomialValue P
  let g := spherePolynomialValue Q
  have hf : ContDiff ℝ 1 f := contDiff_infty.mp (spherePolynomialValue_contDiff P) 1
  have hg : ContDiff ℝ 1 g := contDiff_infty.mp (spherePolynomialValue_contDiff Q) 1
  let L (p : Fin 4 × Fin 4) (x : RoundSphere3) :=
    planeRotationDerivative p.1 p.2 (planeRotationDerivative p.1 p.2 f) x * g x
  let R (p : Fin 4 × Fin 4) (x : RoundSphere3) :=
    f x * planeRotationDerivative p.1 p.2 (planeRotationDerivative p.1 p.2 g) x
  have hL (p : Fin 4 × Fin 4) : Integrable (L p) roundSphere3Measure :=
    integrable_spherical_product (continuous_planeRotationDerivative _ _
      (contDiff_planeRotationDerivative_polynomialValue _ _ P 1)) hg.continuous
  have hR (p : Fin 4 × Fin 4) : Integrable (R p) roundSphere3Measure :=
    integrable_spherical_product hf.continuous (continuous_planeRotationDerivative _ _
      (contDiff_planeRotationDerivative_polynomialValue _ _ Q 1))
  change (∫ x : RoundSphere3, planeRotationCasimir f x * g x ∂roundSphere3Measure) =
    ∫ x : RoundSphere3, f x * planeRotationCasimir g x ∂roundSphere3Measure
  calc
    _ = ∫ x, ∑ p ∈ rotationPairs, L p x ∂roundSphere3Measure := by
      simp only [planeRotationCasimir, Finset.sum_mul, L]
    _ = ∑ p ∈ rotationPairs, ∫ x, L p x ∂roundSphere3Measure :=
      integral_finset_sum _ fun p _ => hL p
    _ = ∑ p ∈ rotationPairs, ∫ x, R p x ∂roundSphere3Measure := by
      apply Finset.sum_congr rfl
      intro p hp
      have hn : p.1 ≠ p.2 := ne_of_lt ((mem_rotationPairs p.1 p.2).mp hp)
      have left := integral_planeRotationDerivative_mul hn
        (contDiff_planeRotationDerivative_polynomialValue p.1 p.2 P 1) hg
      have right := integral_planeRotationDerivative_mul hn hf
        (contDiff_planeRotationDerivative_polynomialValue p.1 p.2 Q 1)
      simp only [L, R, f, g, left, right, neg_neg]
    _ = ∫ x, ∑ p ∈ rotationPairs, R p x ∂roundSphere3Measure :=
      (integral_finset_sum _ fun p _ => hR p).symm
    _ = _ := by simp only [planeRotationCasimir, Finset.mul_sum, R]

private theorem sphereEigenvalue_strictMono :
    StrictMono (fun d : ℕ => (d : ℝ) * ((d : ℝ) + 2)) := by
  intro a b hab
  have hcast : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hpos : 0 < (b : ℝ) + (a : ℝ) + 2 := by positivity
  nlinarith only [mul_pos (sub_pos.mpr hcast) hpos]

/-- Harmonics from different polynomial degrees are orthogonal in the actual
round-sphere integral. -/
theorem sphereHarmonicBasisFunction_integral_mul_of_ne_degree {d e : ℕ} (h : d ≠ e)
    (i : Fin ((d + 1)^2)) (j : Fin ((e + 1)^2)) :
    (∫ x : RoundSphere3, sphereHarmonicBasisFunction d i x *
      sphereHarmonicBasisFunction e j x ∂roundSphere3Measure) = 0 := by
  let f := sphereHarmonicBasisFunction d i
  let g := sphereHarmonicBasisFunction e j
  let P := ((sphereHarmonicPolynomialBasis d i : SphereHomogeneous d) : SpherePolynomial)
  let Q := ((sphereHarmonicPolynomialBasis e j : SphereHomogeneous e) : SpherePolynomial)
  let a := -((d : ℝ) * ((d : ℝ) + 2))
  let b := -((e : ℝ) * ((e : ℝ) + 2))
  have eq : a * (∫ x : RoundSphere3, f x * g x ∂roundSphere3Measure) =
      b * (∫ x : RoundSphere3, f x * g x ∂roundSphere3Measure) := by
    have left (x : RoundSphere3) : planeRotationCasimir (spherePolynomialValue P) x * spherePolynomialValue Q x =
        a * (f x * g x) := by
      rw [sphereHarmonicBasisFunction_casimir d i x]
      change (a * f x) * g x = a * (f x * g x)
      ring
    have right (x : RoundSphere3) : spherePolynomialValue P x * planeRotationCasimir (spherePolynomialValue Q) x =
        b * (f x * g x) := by
      rw [sphereHarmonicBasisFunction_casimir e j x]
      change f x * (b * g x) = b * (f x * g x)
      ring
    rw [← integral_const_mul, ← integral_const_mul]
    simpa only [left, right] using integral_planeRotationCasimir_mul_polynomialValue P Q
  have hne : a ≠ b := neg_injective.ne (sphereEigenvalue_strictMono.injective.ne h)
  exact (mul_eq_zero.mp (show (a - b) * (∫ x : RoundSphere3, f x * g x ∂roundSphere3Measure) = 0 by
    rw [sub_mul, eq, sub_self])).resolve_left (sub_ne_zero.mpr hne)

abbrev SphereHarmonicIndex := Σ d : ℕ, Fin ((d + 1)^2)

def sphereHarmonicFamily (i : SphereHarmonicIndex) : C(RoundSphere3, ℝ) :=
  sphereHarmonicBasisFunction i.1 i.2

def sphereHarmonicFamilyLp (i : SphereHarmonicIndex) : RoundSphereL2 :=
  ContinuousMap.toLp 2 roundSphere3Measure ℝ (sphereHarmonicFamily i)

/-- The same per-degree real basis functions form an orthonormal family in
the actual \(L²\) space. -/
theorem sphereHarmonicFamilyLp_orthonormal : Orthonormal ℝ sphereHarmonicFamilyLp := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨d, i⟩ ⟨e, j⟩
  change inner ℝ (ContinuousMap.toLp 2 roundSphere3Measure ℝ (sphereHarmonicBasisFunction d i))
    (ContinuousMap.toLp 2 roundSphere3Measure ℝ (sphereHarmonicBasisFunction e j)) = _
  rw [ContinuousMap.inner_toLp]
  by_cases h : d = e
  · subst e
    simpa [mul_comm] using sphereHarmonicBasisFunction_integral_mul d i j
  · simpa [mul_comm, h] using sphereHarmonicBasisFunction_integral_mul_of_ne_degree h i j

end Burnett.A06
