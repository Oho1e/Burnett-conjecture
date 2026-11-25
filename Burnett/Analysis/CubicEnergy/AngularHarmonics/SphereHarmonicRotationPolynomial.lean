import Burnett.Analysis.CubicEnergy.AngularHarmonics.AmbientPolynomialLaplacian

set_option autoImplicit false
set_option maxHeartbeats 7200000

noncomputable section

namespace Burnett.A06

open MvPolynomial
open scoped BigOperators

private theorem realPolynomial_pderiv_comm (i j : Fin 4) (P : SpherePolynomial) :
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

private theorem polynomialLaplacian_pderiv (i : Fin 4) (P : SpherePolynomial) :
    polynomialLaplacian (pderiv i P) = pderiv i (polynomialLaplacian P) := by
  simp only [polynomialLaplacian_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [realPolynomial_pderiv_comm k i P, realPolynomial_pderiv_comm k i (pderiv k P)]

private theorem polynomialLaplacian_mul_X (i : Fin 4) (P : SpherePolynomial) :
    polynomialLaplacian (X i * P) = X i * polynomialLaplacian P + 2 * pderiv i P := by
  have term (k : Fin 4) :
      pderiv k (pderiv k (X i * P)) =
        X i * pderiv k (pderiv k P) + if i = k then 2 * pderiv i P else 0 := by
    by_cases h : i = k
    · subst k
      simp
      ring
    · simp [h]
  simp only [polynomialLaplacian_apply]
  simp_rw [term]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

/-- The formal generator of the actual coordinate-plane rotation. -/
def rotationalPolynomial (i j : Fin 4) (P : SpherePolynomial) : SpherePolynomial :=
  X i * pderiv j P - X j * pderiv i P

theorem rotationalPolynomial_isHomogeneous {d : ℕ} {P : SpherePolynomial} (hP : P.IsHomogeneous d)
    (i j : Fin 4) : (rotationalPolynomial i j P).IsHomogeneous d := by
  rcases d with _ | d
  · rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hP
    rw [hP]
    simp [rotationalPolynomial, isHomogeneous_zero]
  · have hij : (X i * pderiv j P).IsHomogeneous (1 + d) := (isHomogeneous_X (R := ℝ) i).mul hP.pderiv
    have hji : (X j * pderiv i P).IsHomogeneous (1 + d) := (isHomogeneous_X (R := ℝ) j).mul hP.pderiv
    simpa only [rotationalPolynomial, Nat.add_comm, Nat.succ_eq_add_one] using hij.sub hji

theorem rotationalPolynomial_laplacian (i j : Fin 4) (P : SpherePolynomial) :
    polynomialLaplacian (rotationalPolynomial i j P) =
      rotationalPolynomial i j (polynomialLaplacian P) := by
  simp only [rotationalPolynomial, map_sub, polynomialLaplacian_mul_X, polynomialLaplacian_pderiv]
  rw [realPolynomial_pderiv_comm i j P]
  ring

/-- Applying a coordinate-plane rotation derivative preserves the actual
homogeneous harmonic subspace in the four-variable polynomial ring. -/
def sphereHarmonicPolynomialRotation (d : ℕ) (i j : Fin 4) (P : sphereHarmonicSubmodule d) :
    sphereHarmonicSubmodule d :=
  ⟨⟨rotationalPolynomial i j P.val.val, rotationalPolynomial_isHomogeneous P.val.property i j⟩,
    mem_sphereHarmonicSubmodule_iff.mpr (by
      change polynomialLaplacian (rotationalPolynomial i j P.val.val) = 0
      rw [rotationalPolynomial_laplacian, mem_sphereHarmonicSubmodule_iff.mp P.property]
      simp [rotationalPolynomial])⟩

theorem spherePolynomialValue_rotationalPolynomial (i j : Fin 4) (P : SpherePolynomial) :
    spherePolynomialValue (rotationalPolynomial i j P) =
      planeRotationDerivative i j (spherePolynomialValue P) := by
  funext x
  rw [planeRotationDerivative_eq_coordinates, spherePolynomialValue_fderiv_coordinate,
    spherePolynomialValue_fderiv_coordinate]
  simp [rotationalPolynomial, spherePolynomialValue]

end Burnett.A06
