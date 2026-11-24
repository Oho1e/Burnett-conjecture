import Mathlib.MeasureTheory.Measure.WithDensity

/-! Weighted restrictions on measurable chart overlap subtypes. -/

set_option autoImplicit false

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open scoped ENNReal

/-- The weighted restriction of the subtype pullback, pushed back to the
ambient space, is the restriction of the weighted ambient measure. -/
theorem map_comap_subtype_coe_restrict_withDensity
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (w : X → ℝ≥0∞)
    {U S : Set X} (hU : MeasurableSet U) (hS : MeasurableSet S) (hSU : S ⊆ U) :
    (((μ.comap (Subtype.val : U → X)).restrict ((Subtype.val : U → X) ⁻¹' S)).withDensity
      (w ∘ (Subtype.val : U → X))).map Subtype.val = (μ.withDensity w).restrict S := by
  apply Measure.ext
  intro T hT
  rw [Measure.map_apply measurable_subtype_coe hT, withDensity_apply _ (measurable_subtype_coe hT),
    restrict_withDensity hS, withDensity_apply _ hT,
    Measure.restrict_restrict (measurable_subtype_coe hT), Measure.restrict_restrict hT,
    ← preimage_inter]
  calc
    _ = ∫⁻ x in (Subtype.val : U → X) '' ((Subtype.val : U → X) ⁻¹' (T ∩ S)), w x ∂μ :=
      setLIntegral_subtype hU _ w
    _ = _ := by
      rw [image_preimage_eq_inter_range, Subtype.range_coe,
        inter_eq_left.mpr (inter_subset_right.trans hSU)]

end Burnett.Microlocal.Overlap
