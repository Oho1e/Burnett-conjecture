import Burnett.Analysis.CubicEnergy.AngularHarmonics.SpherePolynomialLaplacian

set_option autoImplicit false
set_option maxHeartbeats 3900000

noncomputable section

namespace Burnett.A06

open MvPolynomial

private theorem radius_mul_power_mul (j : ℕ) (P : SpherePolynomial) :
    radiusSquared * (radiusSquared ^ j * P) = radiusSquared ^ (j+1) * P := by
  rw [pow_succ', mul_assoc]

/-- The radial power formula used to remove a finite sequence of Laplacian errors. -/
theorem polynomialLaplacian_radiusSquared_pow_succ_mul {P : SpherePolynomial} {d : ℕ}
    (hP : P.IsHomogeneous d) (j : ℕ) :
    polynomialLaplacian (radiusSquared ^ (j+1) * P) =
      radiusSquared ^ (j+1) * polynomialLaplacian P +
        ((4 : ℝ) * ((j : ℝ)+1) * ((d : ℝ)+(j : ℝ)+2)) • (radiusSquared ^ j * P) := by
  induction j with
  | zero =>
    simpa only [pow_zero, pow_one, one_mul, mul_one, Nat.cast_zero, zero_add, add_zero,
      show (4 : ℝ) * ((d : ℝ) + 2) = 4 * (d : ℝ) + 8 by ring] using
      polynomialLaplacian_radiusSquared_mul_of_homogeneous hP
  | succ j ih =>
    have H : (radiusSquared ^ (j+1) * P).IsHomogeneous (2*(j+1)+d) :=
      (radiusSquared_isHomogeneous.pow (j+1)).mul hP
    have coef : (4 : ℝ) * ((j : ℝ)+1) * ((d : ℝ)+(j : ℝ)+2) +
        (4 * ((2*(j+1)+d : ℕ) : ℝ) + 8) =
        4 * ((j.succ : ℝ)+1) * ((d : ℝ)+(j.succ : ℝ)+2) := by
      push_cast
      ring
    rw [← radius_mul_power_mul (j+1) P, polynomialLaplacian_radiusSquared_mul_of_homogeneous H, ih,
      mul_add, mul_smul_comm, radius_mul_power_mul (j+1) (polynomialLaplacian P),
      radius_mul_power_mul j P, add_assoc, ← add_smul, coef]

/-- Each homogeneous target on a radial power has a same-degree preimage for
`P ↦ Δ(r² P)`. The correction descends by two polynomial degrees. -/
theorem exists_radiusSquared_laplacian_preimage (d j : ℕ) (P : SpherePolynomial)
    (hP : P.IsHomogeneous d) :
    ∃ U : SpherePolynomial, U.IsHomogeneous (2*j+d) ∧
      polynomialLaplacian (radiusSquared * U) = radiusSquared ^ j * P := by
  induction d using Nat.strong_induction_on generalizing j P with
  | h d ih =>
    have correction : ∃ V : SpherePolynomial, V.IsHomogeneous (2*j+d) ∧
        polynomialLaplacian (radiusSquared * V) = radiusSquared ^ (j+1) * polynomialLaplacian P := by
      by_cases hd : d ≤ 1
      · refine ⟨0, (homogeneousSubmodule (Fin 4) ℝ (2*j+d)).zero_mem, ?_⟩
        rw [polynomialLaplacian_eq_zero_of_low_degree hP hd, mul_zero, map_zero, mul_zero]
      · obtain ⟨V,hV,eq⟩ := ih (d-2) (by omega) (j+1) (polynomialLaplacian P)
          (polynomialLaplacian_isHomogeneous hP)
        have degree : 2*(j+1)+(d-2) = 2*j+d := by omega
        exact ⟨V, degree ▸ hV, eq⟩
    obtain ⟨V,hV,eq⟩ := correction
    let a : ℝ := 4 * ((j : ℝ)+1) * ((d : ℝ)+(j : ℝ)+2)
    have ha : 0 < a := by dsimp [a]; positivity
    have hRadial : (radiusSquared ^ j * P).IsHomogeneous (2*j+d) :=
      (radiusSquared_isHomogeneous.pow j).mul hP
    let S := homogeneousSubmodule (Fin 4) ℝ (2*j+d)
    refine ⟨a⁻¹ • (radiusSquared ^ j * P - V), S.smul_mem _ (S.sub_mem hRadial hV), ?_⟩
    rw [mul_smul_comm, map_smul, mul_sub, map_sub, radius_mul_power_mul j P,
      polynomialLaplacian_radiusSquared_pow_succ_mul hP j, eq, add_sub_cancel_left]
    change a⁻¹ • (a • (radiusSquared ^ j * P)) = _
    rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]

end Burnett.A06
