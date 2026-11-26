import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualGaugeThreeTerms
import Burnett.Analysis.FrozenTransport.PatchCorrection.OriginalPatchSourceIdentity

set_option autoImplicit false
set_option maxHeartbeats 4300000

noncomputable section

namespace Burnett.V11

open MeasureTheory Matrix Burnett.A06 Burnett.A07 Burnett.A08 Burnett.P01 Burnett.V08
open Burnett.A02.FrequencySplit (E)
open scoped BigOperators ENNReal Matrix
open private inner_eq_of_schwartz from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension

private abbrev Field := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2

/-- The actual matrix entry used in the projected-source identity is the
finite sum of its true ordered low-slot representatives. Its weak divergence
is the sum of the already expanded three terms for those same representatives. -/
theorem originalGaugeTestedOperator_eq_orderedEntries (ϑ : ℝ → ℝ) (κ : ℝ)
    (m : Fin 4 → Fin 4 → ℝ) (ρ : ℝ) (a : E → ℝ) (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen)
    (z : ProjectionSchwartzMatrix) (I J : TensorSlot) (T : Field → LP2) (entries : TensorSlot → Field → LP2)
    (tested : ∀ u v : Field, inner ℂ (v.toLp 2 volume) (T u) =
      originalGaugeRadianPair ϑ gaugeCorrectionInfrared gaugeCorrectionInfrared κ m ρ a C S z I J u v)
    (each : ∀ (k : TensorSlot) (u v : Field), inner ℂ (v.toLp 2 volume) (entries k u) =
      radianHighPair (gaugeRawEntry ϑ gaugeCorrectionInfrared gaugeCorrectionInfrared κ m ρ a C S k I J)
        (Burnett.C03.projectedGaugeComplement z k.1 k.2) u v) :
    T = (fun u => ∑ k : TensorSlot, entries k u) ∧
    ∀ (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) (u v : Field),
      weakDivergenceCommutatorPair d T u v =
        ∑ k : TensorSlot, weakDivergenceCommutatorPair d (entries k) u v := by
  classical
  have entrySum : T = (fun u => ∑ k : TensorSlot, entries k u) := by
    funext u
    apply inner_eq_of_schwartz
    intro v
    rw [tested u v, originalGaugeRadianPair, inner_sum]
    exact Finset.sum_congr rfl (fun k _ => (each k u v).symm)
  refine ⟨entrySum, ?_⟩
  intro d u v
  rw [entrySum]
  simp only [weakDivergenceCommutatorPair, inner_sum, Finset.sum_sub_distrib]

end Burnett.V11
