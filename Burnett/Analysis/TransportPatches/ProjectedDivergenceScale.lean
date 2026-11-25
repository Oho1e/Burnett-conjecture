import Burnett.Analysis.TransportPatches.PatchGradientMass
import Burnett.Analysis.TransportPatches.OriginalInverseJetControl

/-! Patch-uniform C03 source budget for the original fixed high-pass
physical projection on the whole coordinate space. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 4700000

noncomputable section

namespace Burnett.C03

open Set MeasureTheory Burnett.P01 Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped ENNReal NNReal ContDiff

/-- Scale-explicit estimate for the same projected Schwartz fluctuation
appearing in P01. The divergence slope and the localized gradient both
have at most one cutoff loss, and the explicit raw source absorbs their
product into the same patch-volume budget. -/
theorem exists_projectedDivergence_scale_bound
    (B D L₀ : ℝ) (hD : 0 ≤ D) (hL₀ : 0 ≤ L₀)
    (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ℓ : ℝ), 0 < ℓ →
      ∀ (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
        (Kpatch : Set CoordinateSpace), IsCompact Kpatch → tsupport χ ⊆ Kpatch →
      (∀ k x, x ∈ tsupport χ → ‖iteratedFDeriv ℝ k χ x‖ ≤ C k * ℓ⁻¹ ^ k) →
      ∀ (inv g g₀ : CoordinateSpace → Tensor2) (hi : SmoothCoordinateComponents inv)
        (hg : SmoothCoordinateComponents g) (hg₀ : SmoothCoordinateComponents g₀)
        (L : ℝ≥0) (hL : ∀ a b, LipschitzWith L (fun x => inv x a b)),
        (∀ x ∈ tsupport χ, IsSymmetricTensor (inv x)) →
        (∀ x, IsSymmetricTensor (g x)) →
        (∀ x ∈ tsupport χ, ∀ i j, coordinateRicci
          (fun y => christoffel (inv y) (coordinateJet g y)) x i j = 0) →
        (∀ x ∈ tsupport χ, ‖localizedSourceJets inv g g₀ x‖ ≤ B) →
        ∀ e : ℝ, 0 ≤ e → e ≤ 1 → (L : ℝ) ≤ L₀ * (1 + e / ℓ) →
        (∀ x ∈ tsupport χ, ‖g x - g₀ x‖ ≤ e ∧
          ‖coordinateJet g x - coordinateJet g₀ x‖ ≤ D) →
        let A := ProjectedSourceCoefficients.ofReal (fun a b x => inv x a b) hi L hL
        let z := localizedMetricSchwartz g g₀ χ hχ hc hg hg₀
        ‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤
          M * (volume Kpatch ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e) := by
  obtain ⟨M₀, hM₀, hRaw⟩ := exists_projectedRawSource_scale_bound B C hC
  obtain ⟨H, hH, hComm⟩ := exists_projectedSourceDivergenceL2_bound
  let G := C 0 * D + C 1
  let M := ‖projectionFullL2‖ * M₀ + 8 * H * L₀ * G
  have hG : 0 ≤ G := add_nonneg (mul_nonneg (hC 0) hD) (hC 1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro ℓ hℓ χ hχ hc Kpatch hK hSupp hCut inv g g₀ hi hg hg₀ L hL
    hInvSym hSym hVac hJet e he hE hSlope hField
  let A := ProjectedSourceCoefficients.ofReal (fun a b x => inv x a b) hi L hL
  let z := localizedMetricSchwartz g g₀ χ hχ hc hg hg₀
  let V := (volume Kpatch ^ ((1 : ℝ) / 2)).toReal
  let S := 1 + e / ℓ
  let T := 1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hInvEq : (ℓ⁻¹)^2 = (ℓ ^ 2)⁻¹ := inv_pow _ _
  have hQ : ‖projectionFullL2 (projectedSourceQ A z)‖ ≤ ‖projectionFullL2‖ * M₀ * V * T := by
    have hExact : projectedSourceQ A z =
        projectionMatrixToL2 (localizedWaveSourceSchwartz inv g g₀ χ hχ hc hi hg hg₀) :=
      projectedSourceQ_eq_localizedWaveSourceSchwartz inv g g₀ χ hχ hc hi hg hg₀ L hL
    rw [hExact]
    have hEstimate := hRaw ℓ hℓ χ hχ hc Kpatch hK hSupp hCut inv g g₀ hi hg hg₀
      hInvSym hSym hVac hJet e he (fun x hx => (hField x hx).1)
    rw [hInvEq] at hEstimate
    refine hEstimate.trans_eq ?_
    change ‖projectionFullL2‖ * (ENNReal.ofReal (M₀ * T) * _).toReal = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hM₀ hT)]
    change ‖projectionFullL2‖ * (M₀ * T * V) = ‖projectionFullL2‖ * M₀ * V * T
    ring
  have hMass : projectedSourceGradientMass z ≤ 4 * G * V * S := by
    have hCutZero : ∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ 0 χ x‖ ≤ C 0 := by
      simpa only [pow_zero, mul_one] using hCut 0
    have hCutOne : ∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ 1 χ x‖ ≤ C 1 * ℓ⁻¹ := by
      simpa only [pow_one] using hCut 1
    have hEstimate := localizedMetricGradientMass_le_patch_measure g g₀ hg hg₀ χ hχ hc
      Kpatch hK hSupp ℓ (C 0) (C 1) D e hℓ (hC 0) (hC 1) hD he
      hCutZero hCutOne hField
    have hLocal : 0 ≤ C 0 * D + C 1 * ℓ⁻¹ * e :=
      add_nonneg (mul_nonneg (hC 0) hD)
        (mul_nonneg (mul_nonneg (hC 1) (inv_nonneg.mpr hℓ.le)) he)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hLocal] at hEstimate
    refine hEstimate.trans ?_
    have hGScale : C 0 * D + (C 1 * ℓ⁻¹) * e ≤ G * S := by
      calc
        _ ≤ (C 0 * D + C 1 * ℓ⁻¹ * e) + (C 0 * D * (e / ℓ) + C 1) :=
          le_add_of_nonneg_right
            (add_nonneg (mul_nonneg (mul_nonneg (hC 0) hD) (div_nonneg he hℓ.le)) (hC 1))
        _ = _ := by dsimp [G, S]; ring
    calc
      _ ≤ 4 * (G * S * V) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hGScale hV) (by norm_num)
      _ = _ := by ring
  have hSlopeA : (A.slope : ℝ) ≤ L₀ * S := hSlope
  change ‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤ M * V * T
  calc
    _ ≤ ‖projectionFullL2 (projectedSourceQ A z)‖ +
        H * (A.slope : ℝ) * projectedSourceGradientMass z := hComm A z
    _ ≤ ‖projectionFullL2‖ * M₀ * V * T + H * (L₀ * S) * (4 * G * V * S) :=
      add_le_add hQ (mul_le_mul (mul_le_mul_of_nonneg_left hSlopeA hH) hMass
        (by unfold projectedSourceGradientMass; positivity) (by positivity))
    _ = ‖projectionFullL2‖ * M₀ * V * T + (4 * H * L₀ * G * V) * S^2 := by ring
    _ ≤ ‖projectionFullL2‖ * M₀ * V * T + (4 * H * L₀ * G * V) * (2 * T) :=
      add_le_add_left (mul_le_mul_of_nonneg_left (cutoff_square_le_sourceBudget ℓ e hℓ he hE)
        (by positivity)) _
    _ = _ := by dsimp [M]; ring

end Burnett.C03
