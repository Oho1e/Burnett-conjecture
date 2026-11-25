import Burnett.Analysis.AllScaleTransfer.PositiveFixedChartGapExtension
import Burnett.Analysis.AllScaleTransfer.ActualCapSignedBoxes
import Burnett.Analysis.AllScaleTransfer.PositiveRatioRemainderBudget

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff

private theorem sign_eq_of_positive_axes {x : Frequency} {s t : Bool}
    (hs : 0 < signedAxis s x) (ht : 0 < signedAxis t x) : s = t := by
  cases s <;> cases t
  · rfl
  · change 0 < -(x 0) at hs
    change 0 < x 0 at ht
    exfalso
    linarith only [hs, ht]
  · change 0 < x 0 at hs
    change 0 < -(x 0) at ht
    exfalso
    linarith only [hs, ht]
  · rfl

/-- A point of a fixed signed compact block is outside every other signed
open chart. This is what lets the four smooth extensions be added. -/
theorem signedPairK_notMem_other_signedPairV {α : ℝ} (hα : 0 < α)
    {s t : CapSigns} (hst : s ≠ t) {pq : FrequencyPair} (hK : pq ∈ signedPairK α s) :
    pq ∉ signedPairV α t := by
  intro hV
  have posK {x : Frequency} {sign : Bool} (hx : x ∈ signedClosedAnnulus α sign) :
      0 < signedAxis sign x :=
    (mul_pos hα ((by norm_num : (0 : ℝ) < 1 / 2).trans_le hx.1.1)).trans_le hx.2
  have posV {x : Frequency} {sign : Bool} (hx : x ∈ signedOpenAnnulus α sign) :
      0 < signedAxis sign x :=
    (mul_nonneg (half_pos hα).le (norm_nonneg _)).trans_lt hx.2
  exact hst (Prod.ext (sign_eq_of_positive_axes (posK hK.1) (posV hV.1))
    (sign_eq_of_positive_axes (posK hK.2) (posV hV.2)))

/-- Extend the original positive-ratio remainder in one of the fixed
annular charts. The given symbol has one-sided regularity on its ratio
window. The extension has the same value on the compact chart block and
vanishes outside the open annular chart. -/
theorem exists_actual_cap_positive_box_extension
    (B tube outer enlarged axial lo hi : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    (hAxial : 0 < axial) (hlo : 0 < lo)
    {K V : Set FrequencyPair} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (hCone : V ⊆ fixedConeAnnulus lo hi axial ×ˢ fixedConeAnnulus lo hi axial)
    {U : Set LowRatio.Angles} (hU : IsOpen U) (u v : AngleProjection)
    (hAngular : MapsTo (normalizedPairAngles u v) V U)
    {b : ℝ} (hb : 0 < b) (χ₀ : ℝ → ℝ) (oneχ₀ : χ₀ 0 = 1)
    (plateau : ∀ ρ ∈ Ioo (0 : ℝ) b, χ₀ ρ = 1) :
    ∃ (Cext : ℝ) (s₀ : ℕ), 0 ≤ Cext ∧
      ∀ (m : Form) (w : Vec) (F : NullCapChart m w),
        ‖w‖ = 1 → ‖F.toFrequency.toContinuousLinearMap‖ ≤ B →
        ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → 4 * B * (5 * δ) ≤ 1 →
        ∀ (M : LowRatio.Point → ℂ) (A₁₀₀ : ℝ), 0 ≤ A₁₀₀ →
          ContDiffOn ℝ 100 M (U ×ˢ Ico (0 : ℝ) b) →
          (∀ n ≤ 100, ∀ z ∈ U ×ˢ Ico (0 : ℝ) b,
            ‖iteratedFDerivWithin ℝ n M (U ×ˢ Ico (0 : ℝ) b) z‖ ≤ A₁₀₀) →
          let A := capFrequencyEquiv F hδ.ne'
          let angular := normalizedPairAngles u v ∘ boxToPair
          ∃ g : ℕ → BoxSpace → ℂ,
            (∀ s, ContDiff ℝ 99 (g s)) ∧
            (∀ s z, boxToPair z ∉ V → g s z = 0) ∧
            (∀ s n, n ≤ 40 → ∀ z, ‖iteratedFDeriv ℝ n (g s) z‖ ≤
              (Cext * A₁₀₀) * radialGapDecay s) ∧
            (∀ s, s₀ ≤ s → ∀ pq ∈ V, gapRatio A s pq.1 pq.2 ∈ Ioo (0 : ℝ) b) ∧
            ∀ s, s₀ ≤ s → ∀ ζ υ : Frequency, (ζ, υ) ∈ K →
              g s (joinedInputs ζ υ) = normalizedGapRemainder A angular M χ₀ s (joinedInputs ζ υ) := by
  have nonzero (pq : FrequencyPair) (hpq : pq ∈ V) : pq.1 ≠ 0 ∧ pq.2 ≠ 0 :=
    ⟨norm_pos_iff.mp (hlo.trans_le (hCone hpq).1.1.1),
      norm_pos_iff.mp (hlo.trans_le (hCone hpq).2.1.1)⟩
  obtain ⟨J, hJ, capBudget⟩ := exists_uniform_capFrequency_radial_seminorms
    B tube outer enlarged axial lo hi hB hTube hOut hOE hAxial hlo 40
  let ang := normalizedPairAngles u v
  obtain ⟨β, Cg, s₀, _, _, tβ, _, hCg, mkGap⟩ := exists_fixed_chart_positive_gap_extension
    hK hV hKV hU ang (normalizedPairAngles_contDiffOn u v nonzero) hAngular J hJ.le hb
  let D := max 1 ‖boxToPair.toContinuousLinearMap‖
  have hD : 1 ≤ D := le_max_left _ _
  let Cext := Cg * D^40
  have hCext : 0 ≤ Cext := by dsimp [Cext]; positivity
  refine ⟨Cext, s₀, hCext, ?_⟩
  intro m w F hw hF hiF δ hδ hδone small M A₁₀₀ hA₁₀₀ sM bM A angular
  let r := physicalRadialRatio A.toContinuousLinearMap
  have nonzeroA (q : Frequency) (hq : q ≠ 0) : A.toContinuousLinearMap q ≠ 0 :=
    fun h => hq (A.injective (h.trans A.map_zero.symm))
  have rn (pq : FrequencyPair) (hpq : pq ∈ V) : 0 < r pq :=
    div_pos (norm_pos_iff.mpr (nonzeroA pq.1 (nonzero pq hpq).1))
      (norm_pos_iff.mpr (nonzeroA pq.2 (nonzero pq hpq).2))
  have sr : ContDiffOn ℝ ∞ r V := by
    intro pq hpq
    exact (physicalRadialRatio_contDiffAt _ (nonzeroA pq.1 (nonzero pq hpq).1)
      (nonzeroA pq.2 (nonzero pq hpq).2)).contDiffWithinAt
  obtain ⟨_, bRatio⟩ := capBudget m w F hw hF hiF δ hδ hδone small
  have br (n : ℕ) (hn : n ≤ 40) (pq : FrequencyPair) (hpq : pq ∈ V) :
      ‖iteratedFDeriv ℝ n r pq‖ ≤ J := by
    have hp := (hCone hpq).1
    have hq := (hCone hpq).2
    exact (bRatio n hn pq.1 ⟨hp.1, Or.inl hp.2⟩ pq.2 ⟨hq.1, Or.inl hq.2⟩).1
  obtain ⟨sR, bR⟩ := LowRatio.remainder_jets_of_oneSidedC100
    hU M χ₀ oneχ₀ plateau sM A₁₀₀ bM
  obtain ⟨gPair, sg, bg, positive, eg⟩ := mkGap r (LowRatio.remainder M χ₀) A₁₀₀ hA₁₀₀ sr rn br sR
    (fun n hn z hz => bR n (hn.trans (by decide : 40 ≤ 99)) z hz)
  let g (s : ℕ) := gPair s ∘ boxToPair
  have sG (s : ℕ) : ContDiff ℝ 99 (g s) := (sg s).1.comp boxToPair.contDiff
  have gZero (s : ℕ) (z : BoxSpace) (hz : boxToPair z ∉ V) : g s z = 0 := by
    change gPair s (boxToPair z) = 0
    exact image_eq_zero_of_notMem_tsupport (fun h => hz (tβ ((sg s).2 h)))
  have bG (s n : ℕ) (hn : n ≤ 40) (z : BoxSpace) :
      ‖iteratedFDeriv ℝ n (g s) z‖ ≤ (Cext * A₁₀₀) * radialGapDecay s := by
    have hn' : (n : WithTop ℕ∞) ≤ 99 := by exact_mod_cast (hn.trans (by decide : 40 ≤ 99))
    have hnonneg : 0 ≤ radialGapDecay s := by unfold radialGapDecay; positivity
    change ‖iteratedFDeriv ℝ n (gPair s ∘ boxToPair.toContinuousLinearMap) z‖ ≤ _
    rw [boxToPair.toContinuousLinearMap.iteratedFDeriv_comp_right (sg s).1 z hn']
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ ≤ ((Cg * A₁₀₀) * radialGapDecay s) * ‖boxToPair.toContinuousLinearMap‖^n :=
        mul_le_mul_of_nonneg_right (bg s n hn (boxToPair z)) (pow_nonneg (norm_nonneg _) _)
      _ ≤ ((Cg * A₁₀₀) * radialGapDecay s) * D^40 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) n).trans
          (pow_le_pow_right₀ hD hn)
      _ = _ := by dsimp [Cext]; ring
  refine ⟨g, sG, gZero, bG, ?_, ?_⟩
  · intro s hs pq hpq
    exact positive s hs pq hpq
  · intro s hs ζ υ hpq
    change gPair s (boxToPair (joinedInputs ζ υ)) = _
    rw [boxToPair_joined, eg s hs (ζ, υ) hpq]
    simp only [normalizedGapRemainder, firstInput_joined, secondInput_joined, gapRatio, r,
      physicalRadialRatio, angular, Function.comp_apply, boxToPair_joined, ang]
    rfl

end Burnett.A05.BoxFourier
