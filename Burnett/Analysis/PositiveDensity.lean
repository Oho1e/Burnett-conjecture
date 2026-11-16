import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Local positive densities preserve null sets and L-infinity seminorms

The density is assumed a.e. measurable and a.e. positive only on U. The
actual measures withDensity and restrict are used throughout. No uniform
lower bound on the density, finite total mass, or global positivity is used.
-/

noncomputable section

namespace Burnett.Analysis.PositiveDensity

open MeasureTheory Filter
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w : X → ℝ≥0∞} {U S : Set X}

/-- Reverse absolute continuity is derived from the actual locally positive density. -/
theorem restrict_absolutelyContinuous_withDensity
    (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hw : AEMeasurable w (μ.restrict U)) (hpos : ∀ᵐ x ∂μ.restrict U, 0 < w x) :
    μ.restrict S ≪ (μ.withDensity w).restrict S := by
  rw [restrict_withDensity hS]
  exact withDensity_absolutelyContinuous'
    (hw.mono_measure (Measure.restrict_mono hSU le_rfl))
    ((ae_restrict_of_ae_restrict_of_subset hSU hpos).mono (fun _ h => ne_of_gt h))

/-- The forward direction does not need the positivity or measurability of w. -/
theorem withDensity_restrict_absolutelyContinuous (w : X → ℝ≥0∞)
    (hS : MeasurableSet S) :
    (μ.withDensity w).restrict S ≪ μ.restrict S := by
  rw [restrict_withDensity hS]
  exact withDensity_absolutelyContinuous _ _

/-- Equality of the actual ae filters, derived rather than assumed. -/
theorem ae_restrict_withDensity_eq
    (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hw : AEMeasurable w (μ.restrict U)) (hpos : ∀ᵐ x ∂μ.restrict U, 0 < w x) :
    ae ((μ.withDensity w).restrict S) = ae (μ.restrict S) := by
  exact le_antisymm (withDensity_restrict_absolutelyContinuous w hS).ae_le
    (restrict_absolutelyContinuous_withDensity hS hSU hw hpos).ae_le

theorem restrict_withDensity_null_iff
    (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hw : AEMeasurable w (μ.restrict U)) (hpos : ∀ᵐ x ∂μ.restrict U, 0 < w x)
    (A : Set X) :
    ((μ.withDensity w).restrict S) A = 0 ↔ (μ.restrict S) A = 0 :=
  ⟨fun h => (restrict_absolutelyContinuous_withDensity hS hSU hw hpos) h,
    fun h => (withDensity_restrict_absolutelyContinuous w hS) h⟩

theorem ae_restrict_withDensity_iff
    (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hw : AEMeasurable w (μ.restrict U)) (hpos : ∀ᵐ x ∂μ.restrict U, 0 < w x)
    (p : X → Prop) :
    (∀ᵐ x ∂(μ.withDensity w).restrict S, p x) ↔ ∀ᵐ x ∂μ.restrict S, p x := by
  rw [ae_restrict_withDensity_eq hS hSU hw hpos]

/-- Essential suprema, hence genuine L-infinity seminorms, are unchanged. -/
theorem eLpNorm_top_restrict_withDensity_eq {F : Type*} [ENorm F]
    (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hw : AEMeasurable w (μ.restrict U)) (hpos : ∀ᵐ x ∂μ.restrict U, 0 < w x)
    (f : X → F) :
    eLpNorm f ∞ ((μ.withDensity w).restrict S) = eLpNorm f ∞ (μ.restrict S) := by
  simp only [eLpNorm_exponent_top, eLpNormEssSup, essSup,
    ae_restrict_withDensity_eq hS hSU hw hpos]

theorem eLpNorm_top_restrict_withDensity_le_iff {F : Type*} [ENorm F]
    (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hw : AEMeasurable w (μ.restrict U)) (hpos : ∀ᵐ x ∂μ.restrict U, 0 < w x)
    (f : X → F) (C : ℝ≥0∞) :
    eLpNorm f ∞ ((μ.withDensity w).restrict S) ≤ C ↔
      eLpNorm f ∞ (μ.restrict S) ≤ C := by
  rw [eLpNorm_top_restrict_withDensity_eq hS hSU hw hpos]

section OpenSets
variable [TopologicalSpace X] [OpensMeasurableSpace X] [μ.IsOpenPosMeasure]

/-- A density positive a.e. on U gives positive mass to nonempty open V contained in U. -/
theorem withDensity_open_pos
    (hw : AEMeasurable w (μ.restrict U)) (hpos : ∀ᵐ x ∂μ.restrict U, 0 < w x)
    {V : Set X} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    0 < μ.withDensity w V := by
  have hn := restrict_withDensity_null_iff hV.measurableSet hVU hw hpos Set.univ
  have hn' : μ.withDensity w V = 0 ↔ μ V = 0 := by simpa only [Measure.restrict_apply_univ] using hn
  have hnz : μ.withDensity w V ≠ 0 := fun hz => hV.measure_ne_zero μ hne (hn'.mp hz)
  exact hnz.bot_lt

/-- Pointwise positivity is a sufficient local input; no global positive extension is needed. -/
theorem withDensity_open_pos_of_forall
    (hU : MeasurableSet U) (hw : AEMeasurable w (μ.restrict U))
    (hpos : ∀ x ∈ U, 0 < w x)
    {V : Set X} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    0 < μ.withDensity w V :=
  withDensity_open_pos hw (ae_restrict_of_forall_mem hU hpos) hV hne hVU

end OpenSets
end Burnett.Analysis.PositiveDensity


