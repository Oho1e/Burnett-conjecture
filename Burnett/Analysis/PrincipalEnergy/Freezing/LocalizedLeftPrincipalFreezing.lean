import Burnett.Analysis.PrincipalEnergy.Freezing.ActualFourierSeriesEnergy
import Burnett.Analysis.PrincipalEnergy.Freezing.ActualLeftFourierAction
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedRemainderEnergy
import Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalFreezingWeakJets

set_option autoImplicit false
set_option maxHeartbeats 8900000
set_option maxRecDepth 4300

noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview
open scoped BigOperators ContDiff ENNReal ComplexConjugate Burnett.A03

open private patchValueComponent from Burnett.Analysis.PrincipalEnergy.Freezing.CubicEnergyLpContinuity

/-- The actual localized left principal symbol difference has the stated
principal cubic energy bound. The Fourier series and its symmetrization
difference are taken with the same angular coefficients and spatial modes. -/
theorem exists_localized_left_principal_freezing_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ)
    (symm : ∀ a d i j k, C a d i j k = C d a i k j)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (S P R : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hSP : S < P) (hR : 0 < R)
    (support : tsupport χ ⊆ closedBall (0 : E) S) (N : ℕ) (hN : 7 < N) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (a : E → E → ℝ) (centers U : Set E),
        IsOpen U → sphere (0 : E) 1 ⊆ U →
        (∀ x : E, ContDiffOn ℝ ∞ (a x) U) →
        (∀ ξ : E, ContDiff ℝ ∞ (fun x => a x ξ)) →
        (∀ r : ℕ, ∀ ξ ∈ U, ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ r (a x) ξ)) →
        (∀ H : ℕ, ∃ D : ℝ, 0 ≤ D ∧ SpatialAngularJetBound a centers U S N H D) →
        (∀ x ξ, a x (-ξ) = -a x ξ) →
        (∀ x (t : ℝ), 0 < t → ∀ ξ, a x (t • ξ) = t * a x ξ) →
        ∀ D : ℝ, 0 ≤ D → SpatialAngularJetBound a centers U S N 16 D →
        ∀ c ∈ centers, ∀ (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 →
        ∀ C₀ : ℝ≥0∞, (∀ u v i j k, eLpNorm (C u v i j k : E → ℂ) ⊤ volume ≤ C₀) →
        ∀ z : J → SchwartzMap E ℂ, (∀ i x, conj (z i x) = z i x) →
          tsupport (fieldValueArray z) ⊆ ball c (R * ℓ) →
          ∃ V : PatchFieldLpJet J,
            (∀ i : J, (V.1 i : E → ℂ) =ᵐ[volume] fun x =>
              radianSkewAction (fun ξ => (χ (ℓ⁻¹ • (x - c))) ^ 2 * (a x ξ - a c ξ)) (z i) x) ∧
            (∀ p : Index × J, HasWeakCoordinateDerivative3 (V.1 p.2) (V.2 p) p.1) ∧
            ‖principalCubicLpFunctional C z V‖ₑ ≤
              ENNReal.ofReal (A * D * ℓ * euclideanFieldGradientL3 z ^ 3) +
              (Fintype.card ((Index × J) × (Index × J)) : ℝ≥0∞) * Fintype.card J * C₀ *
                ENNReal.ofReal (B * D) * eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume *
                  euclideanFieldGradientNorm z ^ 2 := by
  classical
  obtain ⟨ρ, hρ, hSupport, A, hA, hCompact, hExpansion, hModeBound⟩ :=
    exists_actual_full_fourier_patch_energy_bound C symm χ hχ S P R hS hP hSP hR support N hN
  obtain ⟨K₁, K₂, hK₁, hK₂, hSymmBound⟩ :=
    exists_localized_symmetrization_remainder_energy_bound (J := J) N hN P R hP hR ρ hρ hSupport
  obtain ⟨Ka, hKa, hAngles⟩ := exists_localized_angular_mode_sphere_jet_bound χ hχ S P hS hP hSP.le support N
  let B := (3 * K₁ + 6 * R * K₂) * Ka
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨A, B, hA, hB, ?_⟩
  intro a centers U hU hSphere hFreq hSlice hSpat hHigh hOdd hHom D hD hSpec
    c hc ℓ hℓ hSmall C₀ hC₀ z hz hZ
  let I := Index → ℤ
  let f (k : I) (j : Fin 2) := localizedRealSpatialModeSchwartz P k ρ hρ hSupport c ℓ hℓ j
  let b (k : I) (j : Fin 2) := localizedRealSpatialAngularMode P k χ a c ℓ j
  let budget (k : I) (_ : Fin 2) := Ka * D * ℓ / spatialLatticeWeight k ^ N
  have hAngle (k : I) (j : Fin 2) :=
    hAngles a centers U hU hSphere hFreq hSpat hHigh hOdd hHom
      D hD hSpec c hc ℓ hℓ hSmall k j
  have hBudget (k : I) (j : Fin 2) : 0 ≤ budget k j ∧
      budget k j ≤ (Ka * D) * ℓ / spatialLatticeWeight k ^ N := by
    exact ⟨by dsimp only [budget, spatialLatticeWeight]; positivity, le_rfl⟩
  obtain ⟨h, _, _, Vmode, hSumMode, hWeakMode, hNormMode⟩ :=
    hModeBound a centers U hU hSphere hFreq hSpat hHigh hOdd hHom D hD hSpec
      c hc ℓ hℓ hSmall z hz hZ
  obtain ⟨v, _, Vsymm, hAe, _, hSumSymm, hWeakSymm, hNormSymm⟩ :=
    hSymmBound b budget (fun k j => (hAngle k j).1)
      (fun k j => (hAngle k j).2.1)
      (fun k j n hn => (hAngle k j).2.2.2 n (hn.trans (by norm_num)))
      c ℓ hℓ (Ka * D) (mul_nonneg hKa hD) hBudget C C₀ hC₀ z hZ
  let W := Vmode - Vsymm
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i
    have hVsum : HasSum (fun k => ∑ j, (h k j i).valueLp) (Vmode.1 i) := by
      simpa only [ContinuousLinearMap.sum_apply, patchValueComponent, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply, separatedModeFieldLpJet]
        using hSumMode.mapL (patchValueComponent J i)
    apply actual_left_series_L3_eq_sub_symmetrization_remainder f b (z i)
      (fun x ξ => (χ (ℓ⁻¹ • (x - c))) ^ 2 * (a x ξ - a c ξ))
      (fun k j => (h k j i).valueLp) (v i) (Vmode.1 i) (Vsymm.1 i)
      hVsum (hSumSymm i) (fun k j => MemLp.coeFn_toLp (h k j i).value) (hAe i)
    intro x
    exact actual_left_radian_skew_series χ hχ S P hS hP hSP.le support N hN
      ρ hρ hCompact a centers U hU hSphere hFreq hSpat hHigh hOdd hHom D hD hSpec
      c hc ℓ hℓ hSmall (z i) x (fun ξ => hExpansion a c ℓ hℓ hSmall ξ (hSlice ξ) x)
  · intro p
    exact left_weak_coordinate_of_symmetrization_remainder _ _ _ _ p.1 (hWeakMode p) (hWeakSymm p).2
  · let F := principalCubicLpFunctional C z
    have h1 : ‖F Vmode‖ₑ ≤ ENNReal.ofReal (A * D * ℓ * euclideanFieldGradientL3 z ^ 3) := by
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal hNormMode
    have h2 := hNormSymm
    rw [show ENNReal.ofReal (K₁ * (Ka * D)) +
        2 * (ENNReal.ofReal (K₁ * (Ka * D)) + ENNReal.ofReal (3 * R * K₂ * (Ka * D))) =
        ENNReal.ofReal (B * D) by
      have h1 : 0 ≤ K₁ * (Ka * D) := by positivity
      have h2 : 0 ≤ 3 * R * K₂ * (Ka * D) := by positivity
      have hTwo : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
      rw [← ENNReal.ofReal_add h1 h2, hTwo,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_add h1 (by positivity)]
      congr 1
      dsimp only [B]
      ring] at h2
    rw [show F W = F Vmode - F Vsymm by simp only [W, map_sub]]
    calc
      _ ≤ ‖F Vmode‖ₑ + ‖F Vsymm‖ₑ := by
        rw [← ofReal_norm_eq_enorm (F Vmode - F Vsymm), ← ofReal_norm_eq_enorm (F Vmode),
          ← ofReal_norm_eq_enorm (F Vsymm), ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
      _ ≤ _ := add_le_add h1 h2

end Burnett.A03
