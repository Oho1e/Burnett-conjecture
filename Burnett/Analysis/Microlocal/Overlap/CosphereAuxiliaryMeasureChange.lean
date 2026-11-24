import Burnett.Analysis.Microlocal.Overlap.NormalizedChartAuxiliaryMeasureChange
import Burnett.Geometry.Cotangent.CosphereMeasure
import Burnett.Counterexamples.Bianchi.UnitNormalization

/-! The ambient auxiliary change on the genuine unit cosphere subtypes. -/

set_option autoImplicit false
set_option maxHeartbeats 830000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension (cotangentNormalize)
open Burnett.Geometry.UnitCosphere (Cosphere fromAmbient measurableEmbedding_coe map_fromAmbient_eq_of_unitNull)
open scoped ContDiff Manifold


variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Change actual auxiliary unit covectors by positive radial normalization in the same fiber. -/
abbrev renormalizeUnitCosphere (r r' : Metric (M := M)) (p : Cosphere r) : Cosphere r' :=
  CotangentUnitNormalization.shellNormalize r r' p

variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

private theorem measurable_renormalizeUnitCosphere (r r' : Metric (M := M)) :
    Measurable (renormalizeUnitCosphere r r') :=
  (measurableEmbedding_coe r').measurable_comp_iff.mp
    ((measurable_cotangentNormalize r').comp (measurableEmbedding_coe r).measurable)

/-- The ambient change of the carried measures induces the weighted pushforward
on the actual old and new unit cospheres. -/
theorem fromAmbient_changeAuxiliary (r r' : Metric (M := M)) (B : Field (M := M))
    (hnB : IsNondegenerate B) (μ μ' : Measure (CotangentBundle M))
    (hNull : μ (cotangentUnitNull r B hnB)ᶜ = 0)
    (hNull' : μ' (cotangentUnitNull r' B hnB)ᶜ = 0)
    (hChange : μ' = renormalizeCotangentPhysicalMeasure r' μ) :
    fromAmbient r' μ' =
      ((fromAmbient r μ).withDensity (fun p : Cosphere r => cotangentAuxiliaryWeight r' p.val)).map
        (renormalizeUnitCosphere r r') := by
  let i : Cosphere r → CotangentBundle M := Subtype.val
  let i' : Cosphere r' → CotangentBundle M := Subtype.val
  let w := cotangentAuxiliaryWeight r'
  let F := renormalizeUnitCosphere r r'
  let α := fromAmbient r μ
  let β := fromAmbient r' μ'
  let γ := (α.withDensity (w ∘ i)).map F
  have hi : MeasurableEmbedding i := measurableEmbedding_coe r
  have hi' : MeasurableEmbedding i' := measurableEmbedding_coe r'
  have hF : Measurable F := measurable_renormalizeUnitCosphere r r'
  have hiF : i' ∘ F = cotangentNormalize r' ∘ i := rfl
  have hPush : β.map i' = γ.map i' := by
    change β.map i' = ((α.withDensity (w ∘ i)).map F).map i'
    rw [show β.map i' = μ' from map_fromAmbient_eq_of_unitNull r' B hnB μ' hNull',
      hChange, Measure.map_map hi'.measurable hF, hiF,
      ← Measure.map_map (measurable_cotangentNormalize r') hi.measurable,
      ← map_withDensity_comp i hi.measurable α w (measurable_cotangentAuxiliaryWeight r'),
      show α.map i = μ from map_fromAmbient_eq_of_unitNull r B hnB μ hNull]
    rfl
  change β = γ
  ext S _
  have h := congrArg (fun m : Measure (CotangentBundle M) => m (i' '' S)) hPush
  simpa only [hi'.map_apply, hi'.injective.preimage_image] using h

end Burnett.Microlocal.Overlap
