import Burnett.Analysis.PrincipalEnergy.Freezing.LeftFourierSeriesAction
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedSpatialProfilesSchwartz
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedAngularModes

set_option autoImplicit false
set_option maxHeartbeats 1850000
noncomputable section

namespace Burnett.A03

open Filter Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff BigOperators

/-- The pointwise Fourier expansion of the actual cut-off symbol identifies
the full left-placed series with precisely its radian Fourier integral. -/
theorem actual_left_radian_skew_series
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (S P : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hSP : S ≤ P)
    (support : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S) (L : ℕ) (hL : 7 < L)
    (ρ : CoordinateSpace → ℝ) (hρ : ContDiff ℝ ∞ ρ) (compactρ : HasCompactSupport ρ)
    (a : CoordinateSpace → CoordinateSpace → ℝ) (centers U : Set CoordinateSpace)
    (hU : IsOpen U) (sphereU : sphere (0 : CoordinateSpace) 1 ⊆ U)
    (hfreq : ∀ x : CoordinateSpace, ContDiffOn ℝ ∞ (a x) U)
    (hspatial : ∀ r : ℕ, ∀ ξ ∈ U, ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ r (a x) ξ))
    (hHigher : ∀ H : ℕ, ∃ B : ℝ, 0 ≤ B ∧ SpatialAngularJetBound a centers U S L H B)
    (odd : ∀ x ξ, a x (-ξ) = -a x ξ)
    (hom : ∀ x (t : ℝ), 0 < t → ∀ ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (hM : 0 ≤ M) (hMixed : SpatialAngularJetBound a centers U S L 16 M)
    (c : CoordinateSpace) (hc : c ∈ centers) (ℓ : ℝ) (hℓ : 0 < ℓ) (hSmall : ℓ ≤ 1)
    (input : SchwartzMap CoordinateSpace ℂ) (x : CoordinateSpace)
    (expansion : ∀ ξ : CoordinateSpace,
      HasSum (fun k : Index → ℤ => ∑ j : Fin 2, localizedRealSpatialModeProfile P k ρ c ℓ j x *
         localizedRealSpatialAngularMode P k χ a c ℓ j ξ)
        ((χ (ℓ⁻¹ • (x - c))) ^ 2 * (a x ξ - a c ξ))) :
    HasSum (fun k : Index → ℤ => ∑ j : Fin 2,
      (localizedRealSpatialModeProfile P k ρ c ℓ j x : ℂ) *
        radianSkewAction (localizedRealSpatialAngularMode P k χ a c ℓ j) input x)
      (radianSkewAction (fun ξ => (χ (ℓ⁻¹ • (x - c))) ^ 2 * (a x ξ - a c ξ)) input x) := by
  classical
  obtain ⟨Ka, hKa, Angular⟩ := exists_localized_angular_mode_sphere_jet_bound χ hχ S P hS hP hSP support L
  let I := Index → ℤ
  let g (k : I) (j : Fin 2) := localizedRealSpatialModeProfile P k ρ c ℓ j x
  let b (k : I) (j : Fin 2) := localizedRealSpatialAngularMode P k χ a c ℓ j
  let D (k : I) (_ : Fin 2) := Ka * M * ℓ / (spatialLatticeWeight k)^L
  have hAngle (k : I) (j : Fin 2) :=
    Angular a centers U hU sphereU hfreq hspatial hHigher odd hom M hM hMixed c hc ℓ hℓ hSmall k j
  have hD (k : I) (j : Fin 2) : 0 ≤ D k j := by dsimp only [D, spatialLatticeWeight]; positivity
  obtain ⟨y, hy⟩ := hρ.continuous.norm.exists_forall_ge_of_hasCompactSupport compactρ.norm
  let B := ‖ρ y‖
  have profileBound (k : I) (j : Fin 2) : ‖g k j‖ ≤ B := by
    let q := ℓ⁻¹ • (x - c)
    have cs : ‖ρ q * Real.cos (spatialModePhase P k q)‖ ≤ B := by
      rw [norm_mul, Real.norm_eq_abs (Real.cos _)]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (norm_nonneg _)).trans (by simpa only [mul_one] using hy q)
    have sn : ‖ρ q * Real.sin (spatialModePhase P k q)‖ ≤ B := by
      rw [norm_mul, Real.norm_eq_abs (Real.sin _)]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (norm_nonneg _)).trans (by simpa only [mul_one] using hy q)
    by_cases eq : j = 0
    · simpa only [g, localizedRealSpatialModeProfile, if_pos eq, localizedSpatialCosineProfile, q] using cs
    · simpa only [g, localizedRealSpatialModeProfile, if_neg eq, localizedSpatialSineProfile, q] using sn
  have majority : Summable (fun k : I => (2 * B * Ka * M * ℓ) * (1 / (spatialLatticeWeight k)^L)) := by
    simpa only [pow_zero] using (summable_spatial_lattice_weighted_decay L 0 hL (by decide)).mul_left
      (2 * B * Ka * M * ℓ)
  have weights : Summable (fun k : I => ∑ j : Fin 2, ‖g k j‖ * D k j) := by
    apply Summable.of_nonneg_of_le
      (fun k => Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hD k j)) _ majority
    intro k
    calc
      _ ≤ ∑ j : Fin 2, B * D k j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (profileBound k j) (hD k j)
      _ = _ := by rw [Fin.sum_univ_two]; dsimp only [D]; ring
  exact hasSum_left_radian_skew_modes g b D (fun k j => (hAngle k j).1) (fun k j => (hAngle k j).2.1) hD
    (fun k j ξ hξ => by simpa only [norm_iteratedFDeriv_zero] using (hAngle k j).2.2.2 0 (by decide) ξ hξ)
    _ expansion weights input x

end Burnett.A03
