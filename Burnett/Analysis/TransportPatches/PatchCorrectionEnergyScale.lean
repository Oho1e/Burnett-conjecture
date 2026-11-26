import Burnett.Analysis.TransportPatches.TransportPatchSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option maxRecDepth 2800
set_option maxHeartbeats 2200000

noncomputable section

namespace Burnett.C03

open Burnett.C04 (correctionEnvelope)

/-- Each of the three complete correction terms carries one copy of the
patch volume. This uses the full source, the low-field norm, and both
derivative norms at the same spatial scale. -/
theorem correction_energy_le_patch_envelope
    (ℓ e v B E source low u₂ u₄ low₄ d d₁ : ℝ)
    (hℓ : 0 < ℓ) (he : 0 ≤ e) (hv : 0 ≤ v) (hB : 1 ≤ B)
    (hLow₀ : 0 ≤ low) (hU₂₀ : 0 ≤ u₂) (hU₄₀ : 0 ≤ u₄) (hLow₄₀ : 0 ≤ low₄)
    (hSource : source ≤ B * v ^ ((1 : ℝ) / 2) * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e))
    (hLow : low ≤ B * e * v ^ ((1 : ℝ) / 4))
    (hU₂ : u₂ ≤ B * (1 + e / ℓ) * v ^ ((1 : ℝ) / 2))
    (hU₄ : u₄ ≤ B * (1 + e / ℓ) * v ^ ((1 : ℝ) / 4))
    (hLow₄ : low₄ ≤ B * (1 + e / ℓ) * v ^ ((1 : ℝ) / 4))
    (hD : d ≤ B * (ℓ + e))
    (hD₁ : d₁ ≤ B * (1 + e / ℓ))
    (hEnergy : E ≤ 2 * source * (B * low * u₄) +
      B * (d * u₂ * low₄ * u₄ + d₁ * u₂ * low * u₄)) :
    E ≤ (3 * B^5) * v * correctionEnvelope ℓ e := by
  let V₂ := v ^ ((1 : ℝ) / 2)
  let V₄ := v ^ ((1 : ℝ) / 4)
  let T := 1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e
  let S := 1 + e / ℓ
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hV₂ : 0 ≤ V₂ := Real.rpow_nonneg hv _
  have hV₄ : 0 ≤ V₄ := Real.rpow_nonneg hv _
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hS : 0 ≤ S := add_nonneg zero_le_one (div_nonneg he hℓ.le)
  have hV : V₂ * V₄ * V₄ = v := by
    dsimp only [V₂, V₄]
    rw [← Real.rpow_add_of_nonneg hv (by norm_num : 0 ≤ (1 : ℝ) / 2)
      (by norm_num : 0 ≤ (1 : ℝ) / 4),
      ← Real.rpow_add_of_nonneg hv (by norm_num : 0 ≤ (1 : ℝ) / 2 + 1 / 4)
        (by norm_num : 0 ≤ (1 : ℝ) / 4)]
    norm_num
  have hSourceTerm : 2 * source * (B * low * u₄) ≤ 2 * B^4 * (e * T * S) * v := by
    calc
      _ ≤ 2 * (B * V₂ * T) * (B * (B * e * V₄) * (B * S * V₄)) := by gcongr
      _ = 2 * B^4 * (e * T * S) * (V₂ * V₄ * V₄) := by ring
      _ = _ := by rw [hV]
  have hCoefficientTerm : B * (d * u₂ * low₄ * u₄) ≤ B^5 * ((ℓ + e) * S^3) * v := by
    calc
      _ ≤ B * ((B * (ℓ + e)) * (B * S * V₂) * (B * S * V₄) * (B * S * V₄)) := by gcongr
      _ = B^5 * ((ℓ + e) * S^3) * (V₂ * V₄ * V₄) := by ring
      _ = _ := by rw [hV]
  have hDriftTerm : B * (d₁ * u₂ * low * u₄) ≤ B^5 * (e * S^3) * v := by
    calc
      _ ≤ B * ((B * S) * (B * S * V₂) * (B * e * V₄) * (B * S * V₄)) := by gcongr
      _ = B^5 * (e * S^3) * (V₂ * V₄ * V₄) := by ring
      _ = _ := by rw [hV]
  have hBfour : B^4 ≤ B^5 := by
    calc
      B^4 = B^4 * 1 := (mul_one _).symm
      _ ≤ B^4 * B := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = B^5 := (pow_succ B 4).symm
  have hBfive : B^5 ≤ 3 * B^5 := le_mul_of_one_le_left (by positivity) (by norm_num)
  refine hEnergy.trans ?_
  rw [mul_add]
  calc
    _ ≤ 2 * B^4 * (e * T * S) * v + B^5 * ((ℓ + e) * S^3) * v +
        B^5 * (e * S^3) * v := by
      simpa only [add_assoc] using add_le_add hSourceTerm (add_le_add hCoefficientTerm hDriftTerm)
    _ = 2 * B^4 * (e * T * S) * v + B^5 * ((ℓ + 2 * e) * S^3) * v := by ring
    _ ≤ 3 * B^5 * (e * T * S) * v + (3 * B^5) * ((ℓ + 2 * e) * S^3) * v := by
      have hBtwo : 2 * B^4 ≤ 3 * B^5 := by
        linarith [show 0 ≤ B^5 by positivity]
      gcongr
    _ = _ := by unfold correctionEnvelope; change _ = 3 * B^5 * v * (e * T * S + (ℓ + 2 * e) * S^3); ring

end Burnett.C03
