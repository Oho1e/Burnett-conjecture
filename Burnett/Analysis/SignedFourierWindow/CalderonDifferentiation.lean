import Burnett.Analysis.SignedFourierWindow.CalderonExceptional
import Mathlib.MeasureTheory.Covering.DensityTheorem

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

/-- The pointwise control outside the exceptional region holds almost
everywhere for integrable data, without a continuity assumption. -/
theorem ae_enorm_le_centeredMax (f : Space → ℂ) (hf : Integrable f) :
    ∀ᵐ x ∂volume, ‖f x‖ₑ ≤ centeredMax (fun y => ‖f y‖ₑ) x := by
  letI : IsUnifLocDoublingMeasure (volume : Measure Space) := by
    refine ⟨16,?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr x
    have hp : 0<r := hr
    rw [Measure.addHaar_closedBall_mul volume x (by norm_num : (0:ℝ) ≤ 2) hp.le,
      Measure.addHaar_closedBall_center volume x]
    norm_num [show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin]
  have diff := IsUnifLocDoublingMeasure.ae_tendsto_average (μ := (volume : Measure Space)) hf.norm.locallyIntegrable 1
  filter_upwards [diff] with x hx
  have mem : ∀ᶠ r : ℝ in 𝓝[>] 0, x ∈ closedBall x (1*r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mem_closedBall_self (by simpa using (show 0<r from hr).le)
  have lim := hx (fun _ : ℝ => x) id tendsto_id mem
  rw [← ofReal_norm_eq_enorm]
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp lim)
  filter_upwards [self_mem_nhdsWithin] with r hr
  change ENNReal.ofReal (⨍ y in closedBall x r, ‖f y‖) ≤ _
  rw [ofReal_setAverage hf.norm.integrableOn (Filter.Eventually.of_forall (fun y => norm_nonneg (f y)))]
  simp only [ofReal_norm_eq_enorm]
  exact le_iSup (fun t : {t : ℝ // 0<t} =>
    (∫⁻ y in closedBall x t, ‖f y‖ₑ) / volume (closedBall x t)) ⟨r,hr⟩

end Burnett.Analysis.SignedFourierWindow
