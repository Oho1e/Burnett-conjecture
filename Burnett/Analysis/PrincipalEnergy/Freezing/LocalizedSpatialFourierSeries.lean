import Burnett.Analysis.PrincipalEnergy.Freezing.CubeFourierReconstruction
import Burnett.Analysis.SpatialFreezing.SpatialLatticeSummability
import Burnett.Analysis.PrincipalEnergy.Freezing.RescaledFourierJetDecay
import Burnett.Analysis.PrincipalEnergy.Freezing.RescaledPatchCutoff

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Burnett.A03

open Filter Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff BigOperators Topology

/-- The actual physical cosine profile, including the fixed support cutoff. -/
def localizedSpatialCosineProfile (P : ℝ) (k : Index → ℤ) (ρ : CoordinateSpace → ℝ)
    (c : CoordinateSpace) (ℓ : ℝ) (x : CoordinateSpace) : ℝ :=
  let y := ℓ⁻¹ • (x - c)
  ρ y * Real.cos (spatialModePhase P k y)

/-- The actual physical sine profile, including the same support cutoff. -/
def localizedSpatialSineProfile (P : ℝ) (k : Index → ℤ) (ρ : CoordinateSpace → ℝ)
    (c : CoordinateSpace) (ℓ : ℝ) (x : CoordinateSpace) : ℝ :=
  let y := ℓ⁻¹ • (x - c)
  ρ y * Real.sin (spatialModePhase P k y)

private theorem summable_localized_coefficients (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (S P : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hSP : S ≤ P)
    (support : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S)
    (a : CoordinateSpace → CoordinateSpace → ℝ) (c : CoordinateSpace) (ℓ : ℝ)
    (hℓ : 0 < ℓ) (hSmall : ℓ ≤ 1) (ξ : CoordinateSpace)
    (smooth : ContDiff ℝ ∞ (fun x => a x ξ)) :
    Summable (fun k : Index → ℤ => localizedSpatialFourierCoefficient P k χ a c ℓ ξ) := by
  classical
  have spatialBound (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ closedBall c S,
      ‖iteratedFDeriv ℝ j (fun z => a z ξ) x‖ ≤ B := by
    have hTop : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have cont := (smooth.continuous_iteratedFDeriv hTop).norm
    obtain ⟨x, _, mx⟩ := (isCompact_closedBall c S).exists_isMaxOn
      ⟨c, mem_closedBall_self hS⟩ cont.continuousOn
    exact ⟨‖iteratedFDeriv ℝ j (fun z => a z ξ) x‖, norm_nonneg _, isMaxOn_iff.mp mx⟩
  choose B hB bounded using spatialBound
  let M := ∑ j ∈ Finset.range 9, B j
  have hM : 0 ≤ M := Finset.sum_nonneg (fun j _ => hB j)
  obtain ⟨K, _, estimate⟩ := exists_localized_spatial_fourier_coefficient_decay χ hχ S P hS hP
    hSP support 8
  have bounds := estimate a {c} {ξ} (fun q hq => (mem_singleton_iff.mp hq).symm ▸ smooth) M hM
    (by
      intro center hCenter q hq j _ hJ x hx
      obtain rfl : center = c := mem_singleton_iff.mp hCenter
      obtain rfl : q = ξ := mem_singleton_iff.mp hq
      have jlt : j < 9 := by omega
      exact (bounded j x hx).trans
        (Finset.single_le_sum (fun n _ => hB n) (Finset.mem_range.mpr jlt)))
    c (mem_singleton c) ℓ hℓ hSmall ξ (mem_singleton ξ)
  have summable := (summable_spatial_lattice_weighted_decay 8 0 (by decide) (by decide)).mul_left (K * M * ℓ)
  apply summable.of_norm_bounded
  intro k
  simpa only [spatialLatticeWeight, pow_zero, mul_one_div] using bounds k

/-- A fixed real support cutoff supplies a genuine separated real Fourier
series for the same localized symbol in the original physical coordinates. -/
theorem exists_localized_spatial_real_fourier_expansion
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (S P : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hSP : S < P)
    (support : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S) :
    ∃ (ρ : CoordinateSpace → ℝ) (K : ℝ),
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ 0 ≤ K ∧
      tsupport ρ ⊆ ball (0 : CoordinateSpace) P ∧
      (∀ y ∈ closedBall (0 : CoordinateSpace) S, ρ y = 1) ∧
      (∀ y, 0 ≤ ρ y ∧ ρ y ≤ 1) ∧
      (∀ y, ‖iteratedFDeriv ℝ 1 ρ y‖ ≤ K ∧ ‖iteratedFDeriv ℝ 2 ρ y‖ ≤ K) ∧
      ∀ (a : CoordinateSpace → CoordinateSpace → ℝ) (c : CoordinateSpace) (ℓ : ℝ),
        0 < ℓ → ℓ ≤ 1 → ∀ ξ : CoordinateSpace,
          ContDiff ℝ ∞ (fun x => a x ξ) → ∀ x : CoordinateSpace,
            HasSum (fun k : Index → ℤ =>
              localizedSpatialCosineProfile P k ρ c ℓ x *
                (localizedSpatialFourierCoefficient P k χ a c ℓ ξ).re +
              localizedSpatialSineProfile P k ρ c ℓ x *
                (-(localizedSpatialFourierCoefficient P k χ a c ℓ ξ).im))
              ((χ (ℓ⁻¹ • (x - c))) ^ 2 * (a x ξ - a c ξ)) := by
  let inner := (S + P) / 2
  have hInner : 0 < inner := by dsimp only [inner]; linarith
  have hOuter : inner < P := by dsimp only [inner]; linarith
  have hSmallRadius : S ≤ inner := by dsimp only [inner]; linarith
  obtain ⟨ρ, K, hρ, hρCompact, hK, scaled⟩ := exists_rescaled_patch_cutoff inner P hInner hOuter
  have identity : (fun x : CoordinateSpace => ρ ((1 : ℝ)⁻¹ • (x - 0))) = ρ := by
    funext x
    simp only [sub_zero, inv_one, one_smul]
  have atUnit := scaled 0 1 zero_lt_one
  rw [identity, mul_one, mul_one] at atUnit
  obtain ⟨_, _, equalOne, supportρ, _, rangeρ, hJetsρ⟩ := atUnit
  have hOne (y : CoordinateSpace) (hy : y ∈ closedBall 0 S) : ρ y = 1 :=
    equalOne y (closedBall_subset_closedBall hSmallRadius hy)
  have hJets (y : CoordinateSpace) :
      ‖iteratedFDeriv ℝ 1 ρ y‖ ≤ K ∧ ‖iteratedFDeriv ℝ 2 ρ y‖ ≤ K := by
    have H := hJetsρ y
    simpa only [div_one, one_pow] using H.2.2.2
  refine ⟨ρ, K, hρ, hρCompact, hK, supportρ, hOne, rangeρ, hJets, ?_⟩
  intro a c ℓ hℓ hSmall ξ smooth x
  let g := rescaledLocalizedSymbolDifference χ (fun z => a z ξ) c ℓ
  have gSmooth : ContDiff ℝ ∞ g :=
    (hχ.pow 2).smul ((smooth.comp (contDiff_const.add (contDiff_id.const_smul ℓ))).sub contDiff_const)
  have squareSupport : tsupport (fun y => (χ y)^2) ⊆ tsupport χ := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := χ) (g := χ))
  have gSupport : tsupport g ⊆ closedBall (0 : CoordinateSpace) S :=
    (tsupport_smul_subset_left _ _).trans (squareSupport.trans support)
  have hρsupport : Function.support ρ ⊆ spatialFourierCube P :=
    subset_closure.trans (supportρ.trans (ball_subset_closedBall.trans
      (closed_ball_subset_spatial_fourier_cube P P le_rfl)))
  have sum := hasSum_cutoff_spatial_cube_real_series P S hP hSP g gSmooth.continuous gSupport
    (summable_localized_coefficients χ hχ S P hS hP hSP.le support a c ℓ hℓ hSmall ξ smooth)
    ρ hρsupport (fun y hy => hOne y (gSupport hy)) (ℓ⁻¹ • (x - c))
  have yBack : c + ℓ • (ℓ⁻¹ • (x - c)) = x := by
    rw [smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul, add_comm c, sub_add_cancel]
  have value : g (ℓ⁻¹ • (x - c)) = (χ (ℓ⁻¹ • (x - c))) ^ 2 * (a x ξ - a c ξ) := by
    unfold g rescaledLocalizedSymbolDifference rescaledSpatialDifference
    rw [yBack, smul_eq_mul]
  rwa [value] at sum

end Burnett.A03
