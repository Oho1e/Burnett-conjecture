import Burnett.Geometry.ManifoldVolumeRegularity

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open MeasureTheory Set
open scoped ContDiff ENNReal Manifold
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear

/-- A nonempty open gap between two nested sets is detected by a finite measure
that is positive on nonempty open sets. -/
theorem measure_lt_of_open_gap {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {A B U : Set X}
    (hA : MeasurableSet A) (hAB : A ⊆ B) (hU : IsOpen U) (hne : U.Nonempty)
    (hUB : U ⊆ B \ A) : μ A < μ B := by
  have hd : 0 < μ (B \ A) := (hU.measure_pos μ hne).trans_le (measure_mono hUB)
  have hsum : μ (B \ A) + μ A = μ B := by
    simpa only [inter_eq_right.mpr hAB] using measure_diff_add_inter (μ := μ) B hA
  calc
    μ A = μ A + 0 := (add_zero _).symm
    _ < μ A + μ (B \ A) := ENNReal.add_lt_add_left (measure_ne_top μ A) hd
    _ = μ B := (add_comm _ _).trans hsum

/-- A smooth nondegenerate metric has a finite volume measure in its geometric
measure class, positive on every nonempty open set. -/
theorem exists_finite_equivalent_volume {M : Type*} [TopologicalSpace M]
    [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) :
    ∃ μ : Measure M, IsFiniteMeasure μ ∧ μ.IsOpenPosMeasure ∧
      ManifoldVolume.geometricMeasure g ≪ μ ∧ μ ≪ ManifoldVolume.geometricMeasure g := by
  let V := ManifoldVolume.geometricMeasure g
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace CoordinateSpace M
  letI : IsLocallyFiniteMeasure V := ManifoldVolumeRegularity.geometricMeasure_isLocallyFiniteMeasure g hg
  obtain ⟨μ, hfin, hVμ, hμV⟩ := exists_isFiniteMeasure_absolutelyContinuous V
  refine ⟨μ, hfin, ⟨fun U hU hne hzero => ?_⟩, hVμ, hμV⟩
  exact (ManifoldVolumeRegularity.geometricMeasure_open_pos g hg hn hU hne).ne' (hVμ hzero)

end Burnett.Geometry.FiniteCausalVolume
