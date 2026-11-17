import Burnett.Counterexamples.RotatingNull.AngularHamilton

/-!
# The actual canonical Hamilton derivative for the flat Minkowski test

P is the original one-half Minkowski quadratic Hamiltonian. Both base and
momentum partials are true Frechet derivatives in the fixed canonical
coordinates. The frequency gradient and vanishing base derivative are
computed, so the canonical Poisson formula agrees with the earlier
flatHamilton as a theorem, never as a supplied law. The separated test has
full joint smoothness off the zero covector, positive one-homogeneity and
compact BASE support. No compact frequency support or cotangent-flow
existence theorem is assumed.
-/

noncomputable section
namespace Burnett.RotatingNullMoments.CanonicalHamilton
open Burnett.RicciSymbol
open scoped ContDiff BigOperators

abbrev Base := Burnett.CubicExplicit.Space

def momentumBasis (i : Index) : Covector := Pi.single i 1

def P (_x : Base) (ξ : Covector) : ℝ := symbolNorm NullScreen.minkowskiInverse ξ / 2

def basePartial (i : Index) (a : Base → Covector → ℝ) (x : Base) (ξ : Covector) : ℝ :=
  fderiv ℝ (fun y => a y ξ) x (Burnett.CubicExplicit.basis i)

def momentumPartial (i : Index) (a : Base → Covector → ℝ) (x : Base) (ξ : Covector) : ℝ :=
  fderiv ℝ (a x) ξ (momentumBasis i)

/-- The canonical Hamilton field expressed by actual coordinate Frechet partials. -/
def canonicalHamilton (a : Base → Covector → ℝ) (x : Base) (ξ : Covector) : ℝ :=
  ∑ i, (momentumPartial i P x ξ * basePartial i a x ξ -
    basePartial i P x ξ * momentumPartial i a x ξ)

theorem P_eq_coordinates (x : Base) (ξ : Covector) :
    P x ξ = (-(ξ 0)^2 + (ξ 1)^2 + (ξ 2)^2 + (ξ 3)^2) / 2 := by
  rw [P, MinkowskiNull.symbolNorm_eq_coordinates]

theorem P_joint_smooth : ContDiff ℝ ∞ (fun p : Base × Covector => P p.1 p.2) := by
  have hc (i : Index) : ContDiff ℝ ∞ (fun p : Base × Covector => p.2 i) :=
    (contDiff_apply ℝ ℝ i).comp contDiff_snd
  simp_rw [P_eq_coordinates]
  exact ((((hc 0).pow 2).neg.add ((hc 1).pow 2)).add ((hc 2).pow 2) |>.add ((hc 3).pow 2)).div_const 2

theorem momentum_hasFDerivAt (x : Base) (ξ : Covector) :
    HasFDerivAt (P x)
      ((2 : ℝ)⁻¹ • (-(2 * ξ 0) • (ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ) +
        (2 * ξ 1) • ContinuousLinearMap.proj 1 + (2 * ξ 2) • ContinuousLinearMap.proj 2 +
        (2 * ξ 3) • ContinuousLinearMap.proj 3)) ξ := by
  have hp (i : Index) : HasFDerivAt (fun ζ : Covector => (ζ i)^2)
      ((2 * ξ i) • (ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ)) ξ := by
    simpa using ((ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ).hasFDerivAt (x := ξ)).pow 2
  have h := ((((hp 0).neg.add (hp 1)).add (hp 2)).add (hp 3)).const_mul ((2 : ℝ)⁻¹)
  convert h using 1
  · ext ζ
    rw [P_eq_coordinates]
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  · ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, smul_eq_mul]
    ring

theorem momentumPartial_P (i : Index) (x : Base) (ξ : Covector) :
    momentumPartial i P x ξ = raiseCovector NullScreen.minkowskiInverse ξ i := by
  unfold momentumPartial
  rw [(momentum_hasFDerivAt x ξ).fderiv]
  fin_cases i <;> simp [momentumBasis, raiseCovector, NullScreen.minkowskiInverse,
    ContinuousLinearMap.proj_apply]

theorem basePartial_P (i : Index) (x : Base) (ξ : Covector) : basePartial i P x ξ = 0 := by
  unfold basePartial P
  simp

theorem canonicalHamilton_eq_flatHamilton (a : Base → Covector → ℝ) (x : Base) (ξ : Covector) :
    canonicalHamilton a x ξ = flatHamilton a x ξ := by
  unfold canonicalHamilton
  simp_rw [momentumPartial_P, basePartial_P, zero_mul, sub_zero]
  rfl

theorem separatedSymbol_joint_smooth (φ : Base → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiffOn ℝ ∞ (fun p : Base × Covector => separatedTest φ p.1 p.2) {p | p.2 ≠ 0} :=
  separatedTest_smooth φ hφ

theorem separatedSymbol_positive_one_homogeneous (φ : Base → ℝ) (x : Base)
    (r : ℝ) (_hr : 0 < r) (ξ : Covector) :
    separatedTest φ x (r • ξ) = r * separatedTest φ x ξ :=
  separatedTest_homogeneous φ x r ξ

/-- Only the base support is compact. No compactness in frequency is asserted. -/
theorem separatedSymbol_compact_base_support (φ : Base → ℝ) (hc : HasCompactSupport φ) :
    ∃ K : Set Base, IsCompact K ∧ ∀ x ∉ K, ∀ ξ : Covector, separatedTest φ x ξ = 0 :=
  ⟨tsupport φ, hc, fun x hx ξ => separatedTest_zero_outside_base_support φ x hx ξ⟩

theorem canonicalHamilton_separated_null (φ : Base → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (x : Base) (ξ : Covector) (hξ : ξ ≠ 0)
    (hn : symbolNorm NullScreen.minkowskiInverse ξ = 0) :
    canonicalHamilton (separatedTest φ) x ξ =
      ξ 1 * ξ 2 * Burnett.CubicExplicit.D 0 φ x +
      ∑ j : Fin 3, ξ j.succ * oddAngular ξ * Burnett.CubicExplicit.D j.succ φ x := by
  rw [canonicalHamilton_eq_flatHamilton]
  exact flatHamilton_separated_null φ (hφ.differentiable (by simp)) x ξ hξ hn

theorem canonicalHamilton_spatial_error_bound (φ : Base → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (x : Base) (ξ : Covector) (hξ : ξ ≠ 0)
    (hn : symbolNorm NullScreen.minkowskiInverse ξ = 0) :
    |canonicalHamilton (separatedTest φ) x ξ - ξ 1 * ξ 2 * Burnett.CubicExplicit.D 0 φ x| ≤
      (ξ 0)^2 * ∑ j : Fin 3, |Burnett.CubicExplicit.D j.succ φ x| := by
  rw [canonicalHamilton_eq_flatHamilton]
  exact flatHamilton_spatial_error_bound φ (hφ.differentiable (by simp)) x ξ hξ hn

end Burnett.RotatingNullMoments.CanonicalHamilton
