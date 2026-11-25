import Burnett.Geometry.Cotangent.WeightedMomentumTransport
import Mathlib.Topology.Metrizable.Urysohn

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 3700

noncomputable section

namespace Burnett.Geometry.ActualTestLift

open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold ENNReal
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.FullMomentumLift

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

attribute [local instance] puncturedMeasurable puncturedBorel unitNullMeasurable unitNullBorel

/-- The actual weighted lift preserves the pairing of every quadratic fibre
observable, with integrability against the same unit measure. -/
theorem actualWeightedLift_quadratic_pairing (r : Metric (M := M)) (g : Field (M := M))
    (hn : IsNondegenerate g) (μ : Measure (cotangentUnitNull r g hn)) (s : CotangentBundle M → ℝ)
    (hs : ContinuousOn s (cotangentUnitNull r g hn)) (hpos : ∀ p ∈ cotangentUnitNull r g hn, 0 < s p)
    (Q : CotangentBundle M → ℝ) (hQ : Measurable (fun p : puncturedCotangent (M := M) => Q p.val))
    (hscale : ∀ p ∈ puncturedCotangent, ∀ a > (0 : ℝ), Q (cotangentScale a p) = a ^ 2 * Q p) :
    (Integrable (fun p : puncturedCotangent (M := M) => Q p.val) (actualWeightedLift r g hn s hpos μ) ↔
      Integrable (fun p : cotangentUnitNull r g hn => Q p.val) μ) ∧
      (∫ p : puncturedCotangent (M := M), Q p.val ∂actualWeightedLift r g hn s hpos μ) =
        ∫ p : cotangentUnitNull r g hn, Q p.val ∂μ := by
  let L := actualUnitSection r g hn s hpos
  have hL := continuous_actualUnitSection r g hn s hs hpos
  exact weightedLift_pairing_cancel μ L (fun p => s p.val) hL.measurable hs.restrict.measurable
    (fun p => (hpos p.val p.property).ne') (fun p => Q p.val) hQ (fun p => Q p.val)
    (fun p => hscale p.val (cotangentUnitNull_covector_ne_zero r g hn p.property) _ (hpos p.val p.property))

/-- The local squared auxiliary norm has exactly the original unit measure
of the compact base set as its lifted moment. -/
theorem actualWeightedLift_local_second_moment [T2Space M] (r : Metric (M := M)) (g : Field (M := M))
    (hn : IsNondegenerate g) (μ : Measure (cotangentUnitNull r g hn)) [IsLocallyFiniteMeasure μ]
    (s : CotangentBundle M → ℝ) (hs : ContinuousOn s (cotangentUnitNull r g hn))
    (hpos : ∀ p ∈ cotangentUnitNull r g hn, 0 < s p) (K : Set M) (hK : IsCompact K)
    (hg : IsSmooth g) (hgs : IsSymmetric g) :
    let Q := {p : puncturedCotangent (M := M) | p.val.1 ∈ K}
    let V := {p : cotangentUnitNull r g hn | p.val.1 ∈ K}
    (∫⁻ p : puncturedCotangent (M := M),
      ENNReal.ofReal (Q.indicator (fun p : puncturedCotangent (M := M) => (cotangentNorm r p.val) ^ 2) p)
      ∂actualWeightedLift r g hn s hpos μ) = μ V ∧ μ V < (⊤ : ℝ≥0∞) := by
  intro Q V
  letI := cotangentBundle_t2Space (M := M)
  let L := actualUnitSection r g hn s hpos
  let b (p : puncturedCotangent (M := M)) := (cotangentNorm r p.val) ^ 2
  let B : puncturedCotangent (M := M) → ℝ := Q.indicator b
  let j : cotangentUnitNull r g hn → ℝ := V.indicator (fun _ => 1)
  have hQ : IsClosed Q := hK.isClosed.preimage (continuous_cotangent_projection.comp continuous_subtype_val)
  have hV : IsCompact V := isCompact_cotangentUnitNullSubtype_preimage r g hg hn hgs hK
  have hNorm : Continuous (fun p : puncturedCotangent (M := M) => cotangentNorm r p.val) :=
    (contMDiffOn_cotangentNorm r).continuousOn.restrict
  have hb : Measurable B := (hNorm.pow 2).measurable.indicator hQ.measurableSet
  have hscale (p : cotangentUnitNull r g hn) : B (L p) = s p.val ^ 2 * j p := by
    have hbase : (L p).val.1 = p.val.1 := cotangentScale_projection _ _
    have hsq : (cotangentNorm r p.val) ^ 2 = 1 :=
      (cotangentNorm_sq r (cotangentUnitNull_covector_ne_zero r g hn p.property)).trans p.property.1
    have hLspec : (L p).val = cotangentScale (s p.val) p.val := rfl
    by_cases hp : p.val.1 ∈ K
    · have hpQ : L p ∈ Q := by change (L p).val.1 ∈ K; rwa [hbase]
      have hpV : p ∈ V := hp
      change Q.indicator b (L p) = s p.val ^ 2 * V.indicator (fun _ => 1) p
      rw [indicator_of_mem hpQ, indicator_of_mem hpV]
      change (cotangentNorm r (L p).val) ^ 2 = s p.val ^ 2 * 1
      rw [hLspec, cotangentNorm_scale r p.val (hpos p.val p.property), mul_pow, hsq]
    · have hpQ : L p ∉ Q := by change (L p).val.1 ∉ K; rwa [hbase]
      have hpV : p ∉ V := hp
      change Q.indicator b (L p) = s p.val ^ 2 * V.indicator (fun _ => 1) p
      rw [indicator_of_notMem hpQ, indicator_of_notMem hpV, mul_zero]
  have hL := continuous_actualUnitSection r g hn s hs hpos
  have hEq := weightedLift_lintegral_cancel μ L (fun p => s p.val) hL.measurable hs.restrict.measurable
    (fun p => (hpos p.val p.property).ne') B hb j hscale
  have hj : (fun p => ENNReal.ofReal (j p)) = V.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    by_cases hp : p ∈ V <;> simp [j, hp]
  refine ⟨?_, hV.measure_lt_top⟩
  change (∫⁻ p, ENNReal.ofReal (B p) ∂weightedLift μ L (fun p => s p.val)) = μ V
  rw [hEq, hj, lintegral_indicator_const hV.measurableSet, one_mul]

/-- This same weighted lift is a Radon measure and is supported on the actual
punctured characteristic cone. The Radon property uses compact preimages in
the unit bundle over compact base sets. -/
theorem actualWeightedLift_regular_null [T2Space M] [SecondCountableTopology M]
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hgs : IsSymmetric g)
    (μ : Measure (cotangentUnitNull r g hn)) [IsLocallyFiniteMeasure μ] (s : CotangentBundle M → ℝ)
    (hs : ContinuousOn s (cotangentUnitNull r g hn)) (hpos : ∀ p ∈ cotangentUnitNull r g hn, 0 < s p) :
    (actualWeightedLift r g hn s hpos μ).Regular ∧
    actualWeightedLift r g hn s hpos μ {p | dualEnergy g hn p.val ≠ 0} = 0 := by
  letI := finiteDimensional_cotangentModel
  letI := cotangentBundle_t2Space (M := M)
  letI := cotangentBundle_secondCountable (M := M)
  letI : LocallyCompactSpace (ModelProd CoordinateSpace CotangentModel) :=
    CotangentModelWithCorners.locallyCompactSpace
  letI : LocallyCompactSpace (CotangentBundle M) :=
    ChartedSpace.locallyCompactSpace (ModelProd CoordinateSpace CotangentModel) (CotangentBundle M)
  letI : LocallyCompactSpace (puncturedCotangent (M := M)) := isOpen_puncturedCotangent.locallyCompactSpace
  let L := actualUnitSection r g hn s hpos
  let πN (p : cotangentUnitNull r g hn) := p.val.1
  let πP (p : puncturedCotangent (M := M)) := p.val.1
  have hL := continuous_actualUnitSection r g hn s hs hpos
  have hπ : Continuous πP := continuous_cotangent_projection.comp continuous_subtype_val
  have hK := lift_compact_preimage_of_base_compact πN πP L hπ hL
    (fun p => cotangentScale_projection _ _)
    (fun K hK => isCompact_cotangentUnitNullSubtype_preimage r g hg hn hgs hK)
  refine ⟨weightedLift_regular μ L (fun p => s p.val) hL hs.restrict (fun p => (hpos p.val p.property).ne') hK, ?_⟩
  let Z : Set (puncturedCotangent (M := M)) := {p | dualEnergy g hn p.val = 0}
  have hZ : IsClosed Z := isClosed_eq ((contMDiff_dualEnergy g hg hn hgs).continuous.comp continuous_subtype_val)
    continuous_const
  have hLZ (p : cotangentUnitNull r g hn) : L p ∈ Z := by
    change dualEnergy g hn (cotangentScale (s p.val) p.val) = 0
    rw [dualEnergy_cotangentScale, p.property.2, mul_zero]
  exact weightedLift_concentrated μ L (fun p => s p.val) hL.measurable Z hZ.measurableSet hLZ

end Burnett.Geometry.ActualTestLift
