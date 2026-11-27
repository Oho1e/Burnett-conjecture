import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedSpatialProfilesSchwartz
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedAngularModes
import Burnett.Analysis.PrincipalEnergy.Freezing.FiniteSeparatedPatchEnergy

set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open Burnett.A02.FrequencySplit Burnett.A02.FieldAndCoefficientReview
open scoped ContDiff ComplexConjugate BigOperators

/-- A single cutoff realizes the pointwise separated Fourier expansion and
the energy bound for every finite truncation of its actual modes. -/
theorem exists_actual_finite_fourier_patch_energy_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap CoordinateSpace ℂ)
    (symm : ∀ a d i j k, C a d i j k = C d a i k j)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (S P R : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hSP : S < P) (hR : 0 < R)
    (support : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S) (L : ℕ) (hL : 7 < L) :
    ∃ (ρ : CoordinateSpace → ℝ) (hρ : ContDiff ℝ ∞ ρ)
      (hSuppρ : tsupport ρ ⊆ ball (0 : CoordinateSpace) P) (K : ℝ),
      0 ≤ K ∧ HasCompactSupport ρ ∧
      (∀ (a : CoordinateSpace → CoordinateSpace → ℝ) (c : CoordinateSpace) (ℓ : ℝ),
        0 < ℓ → ℓ ≤ 1 → ∀ ξ : CoordinateSpace, ContDiff ℝ ∞ (fun x => a x ξ) →
        ∀ x : CoordinateSpace,
          HasSum (fun k : Index → ℤ => ∑ j : Fin 2, localizedRealSpatialModeProfile P k ρ c ℓ j x *
            localizedRealSpatialAngularMode P k χ a c ℓ j ξ)
            ((χ (ℓ⁻¹ • (x - c))) ^ 2 * (a x ξ - a c ξ))) ∧
      ∀ (a : CoordinateSpace → CoordinateSpace → ℝ) (centers U : Set CoordinateSpace),
        IsOpen U → sphere (0 : CoordinateSpace) 1 ⊆ U →
        (∀ x : CoordinateSpace, ContDiffOn ℝ ∞ (a x) U) →
        (∀ r : ℕ, ∀ ξ ∈ U, ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ r (a x) ξ)) →
        (∀ H : ℕ, ∃ B : ℝ, 0 ≤ B ∧ SpatialAngularJetBound a centers U S L H B) →
        (∀ x ξ, a x (-ξ) = -a x ξ) →
        (∀ x (t : ℝ), 0 < t → ∀ ξ, a x (t • ξ) = t * a x ξ) →
        ∀ M : ℝ, 0 ≤ M → SpatialAngularJetBound a centers U S L 16 M →
        ∀ c ∈ centers, ∀ (ℓ : ℝ) (hℓ : 0 < ℓ), ℓ ≤ 1 →
        ∀ z : J → SchwartzMap CoordinateSpace ℂ, (∀ i x, conj (z i x) = z i x) →
          tsupport (fieldValueArray z) ⊆ ball c (R * ℓ) →
        ∀ modes : Finset (Index → ℤ),
          let f (k : Index → ℤ) (j : Fin 2) := localizedRealSpatialModeSchwartz P k ρ hρ hSuppρ c ℓ hℓ j
          let b (k : Index → ℤ) (j : Fin 2) := localizedRealSpatialAngularMode P k χ a c ℓ j
          (∑ k ∈ modes, ∑ j : Fin 2, ‖separatedModeEnergy C z (f k j) (b k j)‖) ≤
            K * M * ℓ * euclideanFieldGradientL3 z ^ 3 := by
  obtain ⟨ρ, Rρ, smoothρ, compactρ, _, supportρ, _, rangeρ, jetρ, expansion⟩ :=
    exists_localized_spatial_real_fourier_expansion χ hχ S P hS hP hSP support
  obtain ⟨Kprofile, hKprofile, profileSum⟩ := exists_weighted_spatial_profile_sum_bound P L hL
  obtain ⟨Kangular, hKangular, angular⟩ :=
    exists_localized_angular_mode_sphere_jet_bound χ hχ S P hS hP hSP.le support L
  obtain ⟨Kenergy, hKenergy, energySum⟩ := exists_finite_separated_patch_energy_bound C symm R hR
  let B := max 1 Rρ
  have hB : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have supportJet (r : ℕ) (hr : r ≤ 2) (y : CoordinateSpace) : ‖iteratedFDeriv ℝ r ρ y‖ ≤ B := by
    interval_cases r
    · rw [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (rangeρ y).1]
      exact (rangeρ y).2.trans (le_max_left _ _)
    · exact (jetρ y).1.trans (le_max_right _ _)
    · exact (jetρ y).2.trans (le_max_right _ _)
  let K := Kenergy * Kprofile * B * Kangular
  refine ⟨ρ, smoothρ, supportρ, K, by dsimp only [K]; positivity, compactρ, ?_, ?_⟩
  · intro a c ℓ hℓ hSmall ξ hξ x
    simpa [Fin.sum_univ_two, localizedRealSpatialModeProfile, localizedRealSpatialAngularMode] using
      expansion a c ℓ hℓ hSmall ξ hξ x
  · intro a centers U hU hSphere hfreq hspatial hHigher hOdd hHom M hM mixed
      c hc ℓ hℓ hSmall z hz suppZ modes f b
    let D (k : Index → ℤ) (_ : Fin 2) := Kangular * M * ℓ / (spatialLatticeWeight k)^L
    have hAngular (k : Index → ℤ) (j : Fin 2) :=
      angular a centers U hU hSphere hfreq hspatial hHigher hOdd hHom M hM mixed c hc ℓ hℓ hSmall k j
    have hD (k : Index → ℤ) (j : Fin 2) : 0 ≤ D k j := by
      dsimp only [D, spatialLatticeWeight]
      positivity
    have hReal (k : Index → ℤ) (j : Fin 2) (x : CoordinateSpace) : conj (f k j x) = f k j x := by
      change conj (localizedRealSpatialModeSchwartz P k ρ smoothρ supportρ c ℓ hℓ j x) =
        localizedRealSpatialModeSchwartz P k ρ smoothρ supportρ c ℓ hℓ j x
      rw [localized_real_spatial_mode_schwartz_apply]
      simp
    let A := Kprofile * B * (Kangular * M)
    have hA : 0 ≤ A := by dsimp only [A]; positivity
    have hSum (r : ℕ) (hr : r ≤ 2) :
        (∑ k ∈ modes, ∑ j : Fin 2, D k j * schwartzProfileJetLInfinity r (f k j)) ≤ A * ℓ * (ℓ⁻¹)^r := by
      have each (k : Index → ℤ) :
          (∑ j : Fin 2, D k j * schwartzProfileJetLInfinity r (f k j)) =
            D k 0 * spatialProfileJetLInfinity r (localizedSpatialCosineProfile P k ρ c ℓ) +
              D k 1 * spatialProfileJetLInfinity r (localizedSpatialSineProfile P k ρ c ℓ) := by
        have profileNorm (j : Fin 2) : schwartzProfileJetLInfinity r (f k j) =
            spatialProfileJetLInfinity r (localizedRealSpatialModeProfile P k ρ c ℓ j) :=
          localized_real_spatial_mode_schwartz_Linfinity P k ρ smoothρ supportρ c ℓ hℓ j r
        rw [Fin.sum_univ_two, profileNorm 0, profileNorm 1]
        simp [localizedRealSpatialModeProfile]
      simp_rw [each]
      have weights := profileSum ρ B smoothρ hB supportJet c ℓ hℓ (fun k => D k 0) (fun k => D k 1)
        (Kangular * M) (mul_nonneg hKangular hM) (fun k => ⟨hD k 0, le_rfl⟩)
        (fun k => ⟨hD k 1, le_rfl⟩) r hr
      exact weights.2.2 modes
    have sum := energySum A hA (Index → ℤ) c ℓ hℓ hSmall z hz suppZ modes f b D
      (fun k j => (hAngular k j).1) (fun k j => (hAngular k j).2.1)
      (fun k j => (hAngular k j).2.2.1) hD (fun k j => (hAngular k j).2.2.2) hReal hSum
    exact sum.trans_eq (by dsimp only [A, K]; ring)

end Burnett.A03
