import Burnett.Analysis.CubicEnergy.AngularHarmonics.LaplacianRadialPowers
import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHomogeneousMonomialBasis
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option maxHeartbeats 5200000

noncomputable section

namespace Burnett.A06

open MvPolynomial

private def radiusSquaredMulLinear : SpherePolynomial →ₗ[ℝ] SpherePolynomial where
  toFun P := radiusSquared * P
  map_add' P Q := mul_add radiusSquared P Q
  map_smul' a P := mul_smul_comm a radiusSquared P

/-- Multiplication by the actual radius square raises the homogeneous degree by two. -/
def homogeneousRadiusSquaredMul (d : ℕ) : SphereHomogeneous d →ₗ[ℝ] SphereHomogeneous (d+2) :=
  (radiusSquaredMulLinear.comp (homogeneousSubmodule (Fin 4) ℝ d).subtype).codRestrict _
    (fun P => by
      change (radiusSquared * (P : SpherePolynomial)).IsHomogeneous (d+2)
      simpa only [Nat.add_comm 2 d] using radiusSquared_isHomogeneous.mul P.property)

/-- The ambient Laplacian with its actual finite homogeneous domain and codomain. -/
def homogeneousPolynomialLaplacian (d : ℕ) : SphereHomogeneous (d+2) →ₗ[ℝ] SphereHomogeneous d :=
  (polynomialLaplacian.comp (homogeneousSubmodule (Fin 4) ℝ (d+2)).subtype).codRestrict _
    (fun P => by
      change (polynomialLaplacian (P : SpherePolynomial)).IsHomogeneous d
      simpa using polynomialLaplacian_isHomogeneous P.property)

def sphereHarmonicSubmodule (d : ℕ) : Submodule ℝ (SphereHomogeneous d) :=
  LinearMap.ker (polynomialLaplacian.comp (homogeneousSubmodule (Fin 4) ℝ d).subtype)

theorem mem_sphereHarmonicSubmodule_iff {d : ℕ} {P : SphereHomogeneous d} :
    P ∈ sphereHarmonicSubmodule d ↔ polynomialLaplacian (P : SpherePolynomial) = 0 := by
  exact LinearMap.mem_ker

/-- The degree-preserving map that determines the unique radial correction. -/
def radiusSquaredLaplacian (d : ℕ) : SphereHomogeneous d →ₗ[ℝ] SphereHomogeneous d :=
  (homogeneousPolynomialLaplacian d).comp (homogeneousRadiusSquaredMul d)

theorem radiusSquaredLaplacian_surjective (d : ℕ) : Function.Surjective (radiusSquaredLaplacian d) := by
  intro P
  obtain ⟨Q,hQ,eq⟩ := exists_radiusSquared_laplacian_preimage d 0 (P : SpherePolynomial) P.property
  have degree : Q.IsHomogeneous d := by simpa only [Nat.mul_zero, zero_add] using hQ
  refine ⟨⟨Q,degree⟩, Subtype.ext ?_⟩
  change polynomialLaplacian (radiusSquared * Q) = (P : SpherePolynomial)
  simpa only [pow_zero, one_mul] using eq

def radiusSquaredLaplacianEquiv (d : ℕ) : SphereHomogeneous d ≃ₗ[ℝ] SphereHomogeneous d :=
  LinearEquiv.ofBijective (radiusSquaredLaplacian d)
    ⟨LinearMap.injective_iff_surjective.mpr (radiusSquaredLaplacian_surjective d),
      radiusSquaredLaplacian_surjective d⟩

private theorem homogeneousPolynomialLaplacian_harmonic (d : ℕ) (H : sphereHarmonicSubmodule (d+2)) :
    homogeneousPolynomialLaplacian d (H : SphereHomogeneous (d+2)) = 0 := by
  apply Subtype.ext
  change polynomialLaplacian ((H : SphereHomogeneous (d+2)) : SpherePolynomial) = 0
  exact mem_sphereHarmonicSubmodule_iff.mp H.property

private def fischerSum (d : ℕ) :
    (sphereHarmonicSubmodule (d+2) × SphereHomogeneous d) →ₗ[ℝ] SphereHomogeneous (d+2) :=
  (sphereHarmonicSubmodule (d+2)).subtype.coprod (homogeneousRadiusSquaredMul d)

private theorem fischerSum_injective (d : ℕ) : Function.Injective (fischerSum d) := by
  intro P Q eq
  have lap := congrArg (homogeneousPolynomialLaplacian d) eq
  change homogeneousPolynomialLaplacian d ((P.1 : SphereHomogeneous (d+2)) +
      homogeneousRadiusSquaredMul d P.2) =
    homogeneousPolynomialLaplacian d ((Q.1 : SphereHomogeneous (d+2)) +
      homogeneousRadiusSquaredMul d Q.2) at lap
  rw [map_add, map_add, homogeneousPolynomialLaplacian_harmonic d P.1,
    homogeneousPolynomialLaplacian_harmonic d Q.1, zero_add, zero_add] at lap
  have radial : P.2 = Q.2 := (radiusSquaredLaplacianEquiv d).injective lap
  refine Prod.ext (Subtype.ext ?_) radial
  change (P.1 : SphereHomogeneous (d+2)) + homogeneousRadiusSquaredMul d P.2 =
    (Q.1 : SphereHomogeneous (d+2)) + homogeneousRadiusSquaredMul d Q.2 at eq
  rw [radial] at eq
  exact add_right_cancel eq

private theorem fischerSum_surjective (d : ℕ) : Function.Surjective (fischerSum d) := by
  intro P
  obtain ⟨Q,eq⟩ := radiusSquaredLaplacian_surjective d (homogeneousPolynomialLaplacian d P)
  have harmonic : P - homogeneousRadiusSquaredMul d Q ∈ sphereHarmonicSubmodule (d+2) := by
    apply mem_sphereHarmonicSubmodule_iff.mpr
    change ((homogeneousPolynomialLaplacian d (P - homogeneousRadiusSquaredMul d Q) :
      SphereHomogeneous d) : SpherePolynomial) = 0
    rw [map_sub]
    change ((homogeneousPolynomialLaplacian d P - radiusSquaredLaplacian d Q :
      SphereHomogeneous d) : SpherePolynomial) = 0
    rw [eq, sub_self]
    rfl
  refine ⟨(⟨P - homogeneousRadiusSquaredMul d Q,harmonic⟩,Q), ?_⟩
  change P - homogeneousRadiusSquaredMul d Q + homogeneousRadiusSquaredMul d Q = P
  exact sub_add_cancel _ _

/-- The algebraic Fischer decomposition of a real homogeneous polynomial
into its harmonic part and the radius square times its residual polynomial. -/
def sphereFischerEquiv (d : ℕ) :
    (sphereHarmonicSubmodule (d+2) × SphereHomogeneous d) ≃ₗ[ℝ] SphereHomogeneous (d+2) :=
  LinearEquiv.ofBijective (fischerSum d) ⟨fischerSum_injective d,fischerSum_surjective d⟩

theorem sphereFischerEquiv_apply (d : ℕ) (H : sphereHarmonicSubmodule (d+2)) (Q : SphereHomogeneous d) :
    (sphereFischerEquiv d (H,Q) : SpherePolynomial) =
      ((H : SphereHomogeneous (d+2)) : SpherePolynomial) + radiusSquared * (Q : SpherePolynomial) :=
  rfl

private theorem twice_choose_two_succ (n : ℕ) : 2 * (n+1).choose 2 = n*(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n.succ+1 = (n+1)+1 from rfl, Nat.choose_succ_succ' (n+1) 1, Nat.choose_one_right]
    calc
      _ = 2*(n+1).choose 2 + 2*(n+1) := by ring
      _ = _ := by rw [ih]; ring

private theorem choose_three_difference_four_variables (d : ℕ) :
    (d+5).choose 3 = (d+3).choose 3 + (d+3)^2 := by
  have e₁ : (d+5).choose 3 = (d+4).choose 2 + (d+4).choose 3 :=
    Nat.choose_succ_succ' (d+4) 2
  have e₂ : (d+4).choose 3 = (d+3).choose 2 + (d+3).choose 3 :=
    Nat.choose_succ_succ' (d+3) 2
  have e₃ : (d+4).choose 2 = (d+3) + (d+3).choose 2 := by
    rw [Nat.choose_succ_succ' (d+3) 1, Nat.choose_one_right]
  rw [e₁,e₂,e₃]
  calc
    _ = (d+3).choose 3 + (2*(d+3).choose 2 + (d+3)) := by ring
    _ = _ := by rw [twice_choose_two_succ (d+2)]; ring

private theorem sphereHarmonic_finrank_add_two (d : ℕ) :
    Module.finrank ℝ (sphereHarmonicSubmodule (d+2)) = (d+3)^2 := by
  letI : Module.Free ℝ (sphereHarmonicSubmodule (d+2)) :=
    Module.Free.of_divisionRing ℝ (sphereHarmonicSubmodule (d+2))
  have dim := (sphereFischerEquiv d).finrank_eq
  rw [Module.finrank_prod, sphereHomogeneous_finrank, sphereHomogeneous_finrank,
    show d+2+3 = d+5 by omega, choose_three_difference_four_variables] at dim
  omega

theorem sphereHarmonicSubmodule_eq_top_of_low_degree {d : ℕ} (hd : d ≤ 1) :
    sphereHarmonicSubmodule d = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro P
  exact mem_sphereHarmonicSubmodule_iff.mpr (polynomialLaplacian_eq_zero_of_low_degree P.property hd)

/-- The real harmonic homogeneous polynomials in four ambient variables
have the degree-dependent multiplicity used for the round three-sphere. -/
theorem sphereHarmonic_finrank (d : ℕ) :
    Module.finrank ℝ (sphereHarmonicSubmodule d) = (d+1)^2 := by
  cases d with
  | zero =>
    rw [sphereHarmonicSubmodule_eq_top_of_low_degree (by decide : (0 : ℕ) ≤ 1),
      finrank_top, sphereHomogeneous_finrank]
    decide
  | succ d =>
    cases d with
    | zero =>
      rw [sphereHarmonicSubmodule_eq_top_of_low_degree (by decide : (1 : ℕ) ≤ 1),
        finrank_top, sphereHomogeneous_finrank]
      decide
    | succ d => exact sphereHarmonic_finrank_add_two d

end Burnett.A06
