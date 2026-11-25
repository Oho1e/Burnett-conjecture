import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.A06

open MvPolynomial
open scoped BigOperators

/-- The four real ambient coordinates of the round three-sphere. -/
abbrev SpherePolynomial := MvPolynomial (Fin 4) ℝ

/-- The polynomial whose value at a real point is its squared radius. -/
def radiusSquared : SpherePolynomial :=
  ∑ i : Fin 4, X i ^ 2

/-- The ambient polynomial Laplacian, as a real linear map. -/
def polynomialLaplacian : SpherePolynomial →ₗ[ℝ] SpherePolynomial :=
  ∑ i : Fin 4, (pderiv i : Derivation ℝ SpherePolynomial SpherePolynomial).toLinearMap.comp
    (pderiv i).toLinearMap

theorem polynomialLaplacian_apply (P : SpherePolynomial) :
    polynomialLaplacian P = ∑ i : Fin 4, pderiv i (pderiv i P) := by
  simp only [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    Derivation.coeFn_coe]

theorem radiusSquared_isHomogeneous : radiusSquared.IsHomogeneous 2 := by
  rw [radiusSquared, ← mem_homogeneousSubmodule]
  apply Submodule.sum_mem
  intro i _
  rw [mem_homogeneousSubmodule]
  simpa only [one_mul] using (isHomogeneous_X (R := ℝ) i).pow 2

theorem pderiv_radiusSquared (i : Fin 4) : pderiv i radiusSquared = 2 * X i := by
  rw [radiusSquared, map_sum]
  rw [Finset.sum_eq_single i]
  · rw [pderiv_pow, pderiv_X_self]
    simp
  · intro j _ hji
    rw [pderiv_pow, pderiv_X_of_ne hji, mul_zero]
  · simp

theorem pderiv_pderiv_radiusSquared (i : Fin 4) :
    pderiv i (pderiv i radiusSquared) = (2 : SpherePolynomial) := by
  have two_const : pderiv i (2 : SpherePolynomial) = 0 :=
    (pderiv i : Derivation ℝ SpherePolynomial SpherePolynomial).map_natCast 2
  rw [pderiv_radiusSquared, pderiv_mul, two_const, pderiv_X_self, zero_mul, mul_one, zero_add]

private theorem pderiv_pderiv_radiusSquared_mul (i : Fin 4) (P : SpherePolynomial) :
    pderiv i (pderiv i (radiusSquared * P)) =
      radiusSquared * pderiv i (pderiv i P) + 4 * (X i * pderiv i P) + 2 * P := by
  rw [show pderiv i (radiusSquared * P) = pderiv i radiusSquared * P + radiusSquared * pderiv i P
    from pderiv_mul, map_add, pderiv_mul, pderiv_mul, pderiv_pderiv_radiusSquared, pderiv_radiusSquared]
  ring

/-- Multiplication by the radius square has this exact commutator with the
ambient Laplacian on homogeneous real polynomials in four variables. -/
theorem polynomialLaplacian_radiusSquared_mul_of_homogeneous {P : SpherePolynomial} {d : ℕ}
    (hP : P.IsHomogeneous d) :
    polynomialLaplacian (radiusSquared * P) =
      radiusSquared * polynomialLaplacian P + (4 * (d : ℝ) + 8) • P := by
  calc
    _ = radiusSquared * polynomialLaplacian P +
        4 * (∑ i : Fin 4, X i * pderiv i P) + ∑ _ : Fin 4, (2 : SpherePolynomial) * P := by
      simp only [polynomialLaplacian_apply, pderiv_pderiv_radiusSquared_mul, Finset.sum_add_distrib,
        Finset.mul_sum]
    _ = _ := by
      rw [hP.sum_X_mul_pderiv, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, nsmul_eq_mul, smul_eq_C_mul]
      simp only [map_add, map_mul, map_ofNat, map_natCast]
      ring

theorem polynomialLaplacian_isHomogeneous {P : SpherePolynomial} {d : ℕ}
    (hP : P.IsHomogeneous d) : (polynomialLaplacian P).IsHomogeneous (d - 2) := by
  rw [polynomialLaplacian_apply, ← mem_homogeneousSubmodule]
  apply Submodule.sum_mem
  intro i _
  rw [mem_homogeneousSubmodule]
  simpa only [Nat.sub_sub, one_add_one_eq_two] using (hP.pderiv (i := i)).pderiv (i := i)

theorem polynomialLaplacian_eq_zero_of_low_degree {P : SpherePolynomial} {d : ℕ}
    (hP : P.IsHomogeneous d) (hd : d ≤ 1) : polynomialLaplacian P = 0 := by
  rw [polynomialLaplacian_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hc : (pderiv i P).IsHomogeneous 0 := by
    simpa only [Nat.sub_eq_zero_of_le hd] using hP.pderiv (i := i)
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hc
  rw [hc, pderiv_C]

end Burnett.A06
