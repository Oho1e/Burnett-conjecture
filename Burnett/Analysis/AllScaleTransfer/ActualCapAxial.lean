import Burnett.Analysis.AllScaleTransfer.ActualCapBoxExtension
import Burnett.Analysis.AllScaleTransfer.ActualIntegerRadialPartition

set_option autoImplicit false
set_option maxHeartbeats 3800000
noncomputable section

namespace Burnett.A05.BoxFourier

open Set Burnett.Analysis CapFourier ProjectiveNullCaps

/-- The first coordinate in the manuscript's fixed null-coordinate order. -/
theorem frequencyCoordinates_axis (p : Frequency) : (frequencyCoordinates p).1 = p 0 := rfl

/-- A uniform axial margin on the whole actual transformed enlarged-cap
support, including its zero-frequency point. -/
theorem exists_enlarged_cap_support_axial_margin (B tube outer enlarged : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      ∀ (m : Form) (w : Vec) (F : NullCapChart m w),
        ‖w‖ = 1 → ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), 4 * B * (5 * δ) ≤ 1 → ∀ p : Frequency,
          capFrequencyEquiv F hδ.ne' p ∈
            tsupport (enlargedCapMultiplier m δ (tube * δ^2) outer enlarged w) →
          α * ‖p‖ ≤ |p 0| := by
  obtain ⟨L, _, hL, _, compare⟩ :=
    exists_uniform_capFrequency_norm_compare B tube outer enlarged hB hTube hOut hOE
  let α := min 1 (L / 2)
  refine ⟨α, lt_min zero_lt_one (half_pos hL), min_le_left _ _, ?_⟩
  intro m w F hw hI δ hδ hSmall p hpSupport
  by_cases hp : p = 0
  · simp [hp]
  let A := capFrequencyEquiv F hδ.ne'
  let x := A p
  have hw0 : w ≠ 0 := by
    intro h
    simp [h] at hw
  have hx : x ≠ 0 := fun h => hp (A.injective (h.trans A.map_zero.symm))
  have hη : 0 < tube * δ^2 := mul_pos hTube (pow_pos hδ _)
  have hε : 0 ≤ enlarged * tube := mul_nonneg (hOut.trans hOE.le) hTube.le
  obtain ⟨hAngle, hCone⟩ :=
    enlargedCapMultiplier_tsupport_bounds hδ hη hOut hOE hw0 hx hpSupport
  have hCone' : |quadratic m x| ≤ (enlarged * tube) * δ^2 * ‖x‖^2 := by
    convert hCone using 1
    ring
  have hAxis := (scaled_cap_coordinate_bounds F hI (by norm_num : (0 : ℝ) ≤ 5)
    hδ hε hSmall hw hx hAngle hCone').1
  have hBack : parabolicRescale δ (F.toFrequency.symm x) = frequencyCoordinates p := by
    change parabolicRescale δ (F.toFrequency.symm (capFrequencyEquiv F hδ.ne' p)) = frequencyCoordinates p
    rw [capFrequencyEquiv_apply]
    exact chartScaledFrequency_rescale F hδ.ne' (frequencyCoordinates p)
  rw [hBack, frequencyCoordinates_axis] at hAxis
  have lower := (compare m w F hw hI δ hδ hSmall p hpSupport).1
  calc
    α * ‖p‖ ≤ (L / 2) * ‖p‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
    _ ≤ |p 0| := by linarith only [lower, hAxis]

/-- The actual integer window and enlarged-cap support give the normalized
radial bounds and retain the same physical support after rescaling. -/
theorem normalized_integer_annular_cap_support
    {m : Form} {w : Vec} (F : NullCapChart m w)
    {δ : ℝ} (hδ : δ ≠ 0) (tube outer enlarged : ℝ) (i : ℤ) (p : Frequency)
    (hWindow : integerRadialWindow i p ≠ 0)
    (hCap : capFrequencyEquiv F hδ p ∈
      tsupport (enlargedCapMultiplier m δ (tube * δ^2) outer enlarged w)) :
    let ζ := ((2 : ℝ)^(-i)) • p
    (1 / 2 < ‖ζ‖ ∧ ‖ζ‖ < 2) ∧
      capFrequencyEquiv F hδ ζ ∈
        tsupport (enlargedCapMultiplier m δ (tube * δ^2) outer enlarged w) := by
  intro ζ
  have hPos : 0 < (2 : ℝ)^(-i) := by positivity
  have hProfile : endpointHighProfile ζ ≠ 0 := by
    rw [show ζ = ((2 : ℝ)^(-i)) • p from rfl, endpointHighProfile_eq_integerRadialWindow]
    exact Complex.ofReal_ne_zero.mpr hWindow
  exact ⟨endpointHighProfile_properties.2.2 ζ hProfile,
    (capFrequencyEquiv_enlarged_tsupport_smul_iff F hδ (tube * δ^2) outer enlarged hPos.ne' p).2 hCap⟩

end Burnett.A05.BoxFourier
