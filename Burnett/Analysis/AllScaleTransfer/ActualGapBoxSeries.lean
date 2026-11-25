import Burnett.Analysis.AllScaleTransfer.GapBoxSeries
import Burnett.Analysis.AllScaleTransfer.LowRatioSplit

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric MeasureTheory Burnett.Analysis
open scoped ContDiff

def gapRatio (A : Frequency ≃L[ℝ] Frequency) (s : ℕ) (ζ υ : Frequency) : ℝ :=
  radialGapDecay s * (‖A ζ‖ / ‖A υ‖)

/-- Actual dyadic scaling of the physical ratio in the two normalized
four-dimensional annular variables. -/
theorem gapRatio_eq_physical (A : Frequency ≃L[ℝ] Frequency) (j : ℤ) (s : ℕ)
    (ζ υ : Frequency) (hυ : υ ≠ 0) :
    gapRatio A s ζ υ =
      ‖A (((2 : ℝ)^(j - (s : ℤ))) • ζ)‖ / ‖A (((2 : ℝ)^j) • υ)‖ := by
  have hTwo : 0 < (2 : ℝ) := by norm_num
  have hj : 0 < (2 : ℝ)^j := zpow_pos hTwo _
  have hS : 0 < (2 : ℝ)^s := pow_pos hTwo _
  have hAυ : ‖A υ‖ ≠ 0 := by
    intro h
    apply hυ
    apply A.injective
    rw [map_zero]
    exact norm_eq_zero.mp h
  rw [gapRatio, radialGapDecay, div_pow, one_pow, zpow_sub₀ hTwo.ne', zpow_natCast,
    map_smul, map_smul, norm_smul, norm_smul,
    Real.norm_of_nonneg (div_nonneg hj.le hS.le), Real.norm_of_nonneg hj.le]
  field_simp [hj.ne', hS.ne', hAυ]

/-- The original A05 split remainder evaluated at the actual angular
coordinates and physical ratio of the normalized block. -/
def normalizedGapRemainder (A : Frequency ≃L[ℝ] Frequency)
    (angular : BoxSpace → LowRatio.Angles) (M : LowRatio.Point → ℂ) (χ₀ : ℝ → ℝ)
    (s : ℕ) (z : BoxSpace) : ℂ :=
  let ρ := gapRatio A s (firstInput z) (secondInput z)
  ρ • LowRatio.remainder M χ₀ (angular z, ρ)

theorem normalizedGapRemainder_eq_physical (A : Frequency ≃L[ℝ] Frequency)
    (angular : BoxSpace → LowRatio.Angles) (M : LowRatio.Point → ℂ) (χ₀ : ℝ → ℝ)
    (j : ℤ) (s : ℕ) (ζ υ : Frequency) (hυ : υ ≠ 0) :
    let z := joinedInputs ζ υ
    let ρ := ‖A (((2 : ℝ)^(j - (s : ℤ))) • ζ)‖ / ‖A (((2 : ℝ)^j) • υ)‖
    normalizedGapRemainder A angular M χ₀ s z =
      ρ • LowRatio.remainder M χ₀ (angular z, ρ) := by
  simp only [normalizedGapRemainder, firstInput_joined, secondInput_joined, gapRatio_eq_physical A j s ζ υ hυ]

/-- On the original two-input block, the expansion recovers the same split
remainder at the physical scaled frequencies. The chosen box extension
supplies the finite derivatives and agrees there with the original symbol. -/
theorem exists_actual_gap_box_series (S P : ℝ) (hS : 0 < S) (hSP : S < P) :
    ∃ (χ : BoxSpace → ℝ) (C : ℝ),
      ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ ball (0 : BoxSpace) P ∧
      (∀ z ∈ closedBall (0 : BoxSpace) S, χ z = 1) ∧ 0 ≤ C ∧
      ∀ (A : Frequency ≃L[ℝ] Frequency) (angular : BoxSpace → LowRatio.Angles)
        (M : LowRatio.Point → ℂ) (χ₀ : ℝ → ℝ) (g : ℕ → BoxSpace → ℂ) (B : ℝ),
        0 ≤ B →
        (∀ s, ContDiffOn ℝ 99 (g s) (ball (0 : BoxSpace) P)) →
        (∀ s n, n ≤ 40 → ∀ z ∈ ball (0 : BoxSpace) P,
          ‖iteratedFDeriv ℝ n (g s) z‖ ≤ B * radialGapDecay s) →
        ∀ s,
          let c (ab : FourierModePair) :=
            boxCubeFourierCoefficient P (modeIndex ab) (fun z => χ z • g s z)
          (∀ ab, ‖c ab‖ ≤ (C * B) * radialGapDecay s * modePairDecay ab) ∧
          ∀ (ζ υ : Frequency), υ ≠ 0 → let z := joinedInputs ζ υ
            z ∈ closedBall (0 : BoxSpace) S →
            g s z = normalizedGapRemainder A angular M χ₀ s z →
            ∀ j : ℤ,
              let ρ := ‖A (((2 : ℝ)^(j - (s : ℤ))) • ζ)‖ / ‖A (((2 : ℝ)^j) • υ)‖
              Summable (fun ab => ‖c ab * separatedBoxMode P ab z‖) ∧
              HasSum (fun ab => c ab * separatedBoxMode P ab z)
                (ρ • LowRatio.remainder M χ₀ (angular z, ρ)) := by
  obtain ⟨χ, C, hχ, hs, hOne, hC, hBox⟩ := exists_normalized_gap_box_series S P hS hSP
  refine ⟨χ, C, hχ, hs, hOne, hC, ?_⟩
  intro A angular M χ₀ g B hB smooth normBound s
  obtain ⟨hDecay, hSum⟩ := hBox g B hB smooth normBound s
  refine ⟨hDecay, ?_⟩
  intro ζ υ hυ z hz hEq j ρ
  have h := hSum z hz
  rw [hEq, normalizedGapRemainder_eq_physical A angular M χ₀ j s ζ υ hυ] at h
  exact h

end Burnett.A05.BoxFourier
