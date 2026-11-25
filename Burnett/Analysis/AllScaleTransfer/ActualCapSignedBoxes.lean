import Burnett.Analysis.AllScaleTransfer.ActualCapAxial
import Burnett.Analysis.AllScaleTransfer.SignedAnnularCharts

set_option autoImplicit false
set_option maxHeartbeats 3400000
noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric Burnett.Analysis CapFourier ProjectiveNullCaps

/-- The actual transformed enlarged-cap support and the actual two integer
windows select exactly one of four fixed annular chart boxes. All geometry
for the finite-order box extension is furnished uniformly. -/
theorem exists_actual_cap_signed_annular_boxes (B tube outer enlarged : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged) :
    ∃ α r R : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < r ∧ r < R ∧ R < 1 ∧
      (∀ signs : CapSigns,
        IsCompact (signedPairK α signs) ∧ IsOpen (signedPairV α signs) ∧
        signedPairK α signs ⊆ signedPairV α signs ∧
        signedPairV α signs ⊆
          fixedConeAnnulus (1 / 4) 3 (α / 2) ×ˢ fixedConeAnnulus (1 / 4) 3 (α / 2) ∧
        MapsTo (normalizedPairAngles endpointTail endpointTail) (signedPairV α signs)
          (ball (0 : EndpointAngle) R ×ˢ ball (0 : EndpointAngle) R)) ∧
      ∀ (m : Form) (w : Vec) (F : NullCapChart m w),
        ‖w‖ = 1 → ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), 4 * B * (5 * δ) ≤ 1 →
          let A := capFrequencyEquiv F hδ.ne'
          let P := tsupport (enlargedCapMultiplier m δ (tube * δ^2) outer enlarged w)
          ∀ (i j : ℤ) (p q : Frequency), integerRadialWindow i p ≠ 0 →
            integerRadialWindow j q ≠ 0 → A p ∈ P → A q ∈ P →
            let ζ := ((2 : ℝ)^(-i)) • p
            let υ := ((2 : ℝ)^(-j)) • q
            ∃! signs : CapSigns, boxToPair (joinedInputs ζ υ) ∈ signedPairK α signs := by
  obtain ⟨α, hα, hαone, axis⟩ :=
    exists_enlarged_cap_support_axial_margin B tube outer enlarged hB hTube hOut hOE
  obtain ⟨r, R, hr, hrR, hR, charts⟩ := exists_signed_annular_box_charts hα hαone
  refine ⟨α, r, R, hα, hαone, hr, hrR, hR, charts, ?_⟩
  intro m w F hw hI δ hδ hSmall A P i j p q hpWin hqWin hpCap hqCap ζ υ
  rw [boxToPair_joined]
  obtain ⟨hp, hpC⟩ :=
    normalized_integer_annular_cap_support F hδ.ne' tube outer enlarged i p hpWin hpCap
  obtain ⟨hq, hqC⟩ :=
    normalized_integer_annular_cap_support F hδ.ne' tube outer enlarged j q hqWin hqCap
  exact existsUnique_signedPairK hα ⟨hp.1.le, hp.2.le⟩ ⟨hq.1.le, hq.2.le⟩
    (axis m w F hw hI δ hδ hSmall ζ hpC) (axis m w F hw hI δ hδ hSmall υ hqC)

private theorem chartLift_of_annular_membership {α : ℝ} (hα : 0 < α)
    {sign : Bool} {x : Frequency} (hx : x ∈ signedClosedAnnulus α sign) :
    signedChartLift sign (endpointTail (endpointDirection x)) = endpointDirection x := by
  have hn : 0 < ‖x‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hx.1.1
  have signPos : 0 < signedAxis sign x := (mul_pos hα hn).trans_le hx.2
  have scaled : signedAxis sign (endpointDirection x) = ‖x‖⁻¹ * signedAxis sign x := by
    cases sign
    · change -(‖x‖⁻¹ * x 0) = ‖x‖⁻¹ * -(x 0)
      ring
    · rfl
  apply signedChartLift_endpointTail sign (endpointDirection_mem_sphere (norm_pos_iff.mp hn))
  rw [scaled]
  exact mul_pos (inv_pos.mpr hn) signPos

/-- The signs recover the two actual signed unit directions from the
three-coordinate projections used in the fixed eight-dimensional box. -/
theorem actual_directions_of_signed_annular_box {α : ℝ} (hα : 0 < α)
    {signs : CapSigns} (i j : ℤ) (p q : Frequency)
    (hK : boxToPair (joinedInputs (((2 : ℝ)^(-i)) • p) (((2 : ℝ)^(-j)) • q)) ∈ signedPairK α signs) :
    let xy := normalizedPairAngles endpointTail endpointTail
      (boxToPair (joinedInputs (((2 : ℝ)^(-i)) • p) (((2 : ℝ)^(-j)) • q)))
    (signedChartLift signs.1 xy.1, signedChartLift signs.2 xy.2) =
      (endpointDirection p, endpointDirection q) := by
  intro xy
  rw [boxToPair_joined] at hK
  obtain ⟨left, right⟩ := hK
  have lp := chartLift_of_annular_membership hα left
  have lq := chartLift_of_annular_membership hα right
  rw [endpointDirection_pos_smul _ (by positivity)] at lp lq
  have hxy : xy = (endpointTail (endpointDirection p), endpointTail (endpointDirection q)) :=
    normalized_signed_box_angles i j p q
  rw [hxy]
  exact Prod.ext lp lq

/-- Selecting the given signed angular block of the symbol preserves the
actual physical ratio and both original angular directions. -/
theorem actual_signed_box_remainder_at_dyadic
    (A : Frequency ≃L[ℝ] Frequency) (M : CapSigns → LowRatio.Point → ℂ) (χ₀ : ℝ → ℝ)
    (signs : CapSigns) (j : ℤ) (s : ℕ) (p q : Frequency) (hq : q ≠ 0) :
    let ζ := ((2 : ℝ)^(-(j - (s : ℤ)))) • p
    let υ := ((2 : ℝ)^(-j)) • q
    let z := joinedInputs ζ υ
    let ρ := ‖A p‖ / ‖A q‖
    normalizedGapRemainder A (normalizedPairAngles endpointTail endpointTail ∘ boxToPair)
      (M signs) χ₀ s z =
      ρ • LowRatio.remainder (M signs) χ₀
        ((endpointTail (endpointDirection p), endpointTail (endpointDirection q)), ρ) := by
  intro ζ υ z ρ
  have hTwo : (2 : ℝ) ≠ 0 := by norm_num
  have hυ : υ ≠ 0 := smul_ne_zero (by positivity) hq
  have hpScale : ((2 : ℝ)^(j - (s : ℤ))) • ζ = p := by
    dsimp only [ζ]
    rw [smul_smul, ← zpow_add₀ hTwo, add_neg_cancel, zpow_zero, one_smul]
  have hqScale : ((2 : ℝ)^j) • υ = q := by
    dsimp only [υ]
    rw [smul_smul, ← zpow_add₀ hTwo, add_neg_cancel, zpow_zero, one_smul]
  have e := normalizedGapRemainder_eq_physical A
    (normalizedPairAngles endpointTail endpointTail ∘ boxToPair) (M signs) χ₀ j s ζ υ hυ
  dsimp only at e
  rw [hpScale, hqScale] at e
  change normalizedGapRemainder A (normalizedPairAngles endpointTail endpointTail ∘ boxToPair)
    (M signs) χ₀ s (joinedInputs ζ υ) = _
  rw [e, Function.comp_apply]
  change _ • LowRatio.remainder (M signs) χ₀
    (normalizedPairAngles endpointTail endpointTail
      (boxToPair (joinedInputs (((2 : ℝ)^(-(j - (s : ℤ)))) • p) (((2 : ℝ)^(-j)) • q))), _) = _
  rw [normalized_signed_box_angles (j - (s : ℤ)) j p q]

end Burnett.A05.BoxFourier
