import Burnett.Analysis.PrincipalEnergy.Freezing.FiniteFourierPatchEnergy
import Burnett.Analysis.PrincipalEnergy.Freezing.FiniteModeEnergyLinearity

set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open Burnett.A02.FrequencySplit Burnett.A02.FieldAndCoefficientReview
open scoped ContDiff ComplexConjugate BigOperators

/-- The finite Fourier operator itself supplies the supported test direction
in the principal cubic action, with the same one-scale leading bound. -/
theorem exists_actual_finite_fourier_patch_action_bound {J : Type} [Fintype J]
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
          let w (i : J) (x : CoordinateSpace) :=
            ∑ k ∈ modes, ∑ j : Fin 2, separatedSkewAction (f k j) (b k j) (z i) x
          ‖principalPatchTestEnergy C z w‖ ≤ K * M * ℓ * euclideanFieldGradientL3 z ^ 3 := by
  obtain ⟨ρ, hρ, hSuppρ, K, hK, compact, expansion, estimate⟩ :=
    exists_actual_finite_fourier_patch_energy_bound C symm χ hχ S P R hS hP hSP hR support L hL
  obtain ⟨_, _, angular⟩ :=
    exists_localized_angular_mode_sphere_jet_bound χ hχ S P hS hP hSP.le support L
  refine ⟨ρ, hρ, hSuppρ, K, hK, compact, expansion, ?_⟩
  intro a centers U hU hSphere hfreq hspatial hHigher hOdd hHom M hM hJets
    c hc ℓ hℓ hSmall z hz hSupp modes f b w
  have hMode (k : Index → ℤ) (j : Fin 2) :=
    angular a centers U hU hSphere hfreq hspatial hHigher hOdd hHom M hM hJets c hc ℓ hℓ hSmall k j
  have eq : principalPatchTestEnergy C z w =
      ∑ k ∈ modes, ∑ j : Fin 2, separatedModeEnergy C z (f k j) (b k j) :=
    finite_mode_energy_eq_sum C z modes f b (fun k j => (hMode k j).1) (fun k j => (hMode k j).2.1)
  rw [eq]
  calc
    _ ≤ ∑ k ∈ modes, ‖∑ j : Fin 2, separatedModeEnergy C z (f k j) (b k j)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ modes, ∑ j : Fin 2, ‖separatedModeEnergy C z (f k j) (b k j)‖ :=
      Finset.sum_le_sum (fun k _ => norm_sum_le _ _)
    _ ≤ _ := estimate a centers U hU hSphere hfreq hspatial hHigher hOdd hHom M hM hJets
      c hc ℓ hℓ hSmall z hz hSupp modes

end Burnett.A03
