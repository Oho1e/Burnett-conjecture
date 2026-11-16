import Burnett.Analysis.Cubic.OffNullGradient
import Burnett.Analysis.Cubic.OffNullCutoff

noncomputable section

namespace Burnett.CubicOffNull

open MeasureTheory Filter CubicExplicit
open X02.SobolevTestJet
open scoped Topology FourierTransform BigOperators

/-- The actual complexification of an arbitrary real C∞ compact cutoff. -/
def complexCutoff (χ : Cutoff) : SchwartzMap Space ℂ :=
  ((test_compactSupport χ).comp_left (Complex.ofReal_zero)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (test_smooth χ))

@[simp] theorem complexCutoff_apply (χ : Cutoff) (x : Space) :
    complexCutoff χ x = ((χ : Space → ℝ) x : ℂ) := rfl

theorem compact_fGradient_offNull_energy_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (χ : Cutoff) (i : Index) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ,
      ‖𝓕 (fun x => (((χ : Space → ℝ) x * CubicExplicit.D i (fSequence n) x : ℝ) : ℂ)) ξ‖^2)
      atTop (𝓝 0) := by
  simpa only [complexCutoff_apply, Complex.ofReal_mul] using
    localized_fGradient_offNull_energy_tendsto_zero hδ (complexCutoff χ) i

theorem compact_wGradient_offNull_energy_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (χ : Cutoff) (i : Index) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ,
      ‖𝓕 (fun x => (((χ : Space → ℝ) x * CubicExplicit.D i (wSequence n) x : ℝ) : ℂ)) ξ‖^2)
      atTop (𝓝 0) := by
  simpa only [complexCutoff_apply, Complex.ofReal_mul] using
    localized_wGradient_offNull_energy_tendsto_zero hδ (complexCutoff χ) i

/-- Sum of all four positive Euclidean gradient-component energies. -/
theorem compact_fGradient_total_offNull_energy_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (χ : Cutoff) :
    Tendsto (fun n => ∑ i : Index, ∫ ξ in offNullRegion δ,
      ‖𝓕 (fun x => (((χ : Space → ℝ) x * CubicExplicit.D i (fSequence n) x : ℝ) : ℂ)) ξ‖^2)
      atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using
    tendsto_finset_sum Finset.univ (fun i _ => compact_fGradient_offNull_energy_tendsto_zero hδ χ i)

theorem compact_wGradient_total_offNull_energy_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (χ : Cutoff) :
    Tendsto (fun n => ∑ i : Index, ∫ ξ in offNullRegion δ,
      ‖𝓕 (fun x => (((χ : Space → ℝ) x * CubicExplicit.D i (wSequence n) x : ℝ) : ℂ)) ξ‖^2)
      atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using
    tendsto_finset_sum Finset.univ (fun i _ => compact_wGradient_offNull_energy_tendsto_zero hδ χ i)

end Burnett.CubicOffNull
