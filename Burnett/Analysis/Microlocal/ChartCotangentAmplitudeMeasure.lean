import Burnett.Analysis.Microlocal.ChartAmplitudeMeasure
import Burnett.Analysis.Microlocal.OriginalVolumeAuxiliaryAmplitude

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.F05.ChartCotangentAmplitudeMeasure

open MeasureTheory Matrix Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitNullCompactness
open Burnett.F05.ActualChartAuxiliarySection Burnett.F05.OriginalVolumeAuxiliaryAmplitude
open Burnett.F05.ActualCoordinateRicciDensity Burnett.F05.ChartVolumeAmplitude
open Burnett.F05.ActualCoordinateCurlDensity (chartRoundAmplitude)
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.CountableAuxiliaryCharts
open Burnett.Microlocal.FixedChartGeometricDensity Burnett.Microlocal.MatrixMeasureAssembly
open Burnett.Microlocal.RicciRow (backgroundInverse)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open scoped ComplexOrder ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- Each fixed-chart amplitude component, pushed to the actual unit cotangent bundle. -/
def cotangentAmplitudeMeasure (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v)) (i j : Pair) :
    ComplexMeasure (CotangentBundle M) :=
  (chartAmplitudeMeasure q.ball (chartAuxiliaryInverse r q) ν hfin i j).map (chartAuxiliaryRay r q)

theorem cotangentAmplitudeMeasure_apply (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (i j : Pair) (s : Set (CotangentBundle M)) (hs : MeasurableSet s) :
    cotangentAmplitudeMeasure r q ν hfin i j s =
      ∫ p in chartAuxiliaryRay r q ⁻¹' s, chartAuxiliaryAmplitude r q ν hfin p i j ∂traceMeasure ν := by
  have hm : Measurable (chartAuxiliaryRay r q) := (continuous_chartAuxiliaryRay r q).measurable
  rw [cotangentAmplitudeMeasure, VectorMeasure.map_apply _ hm hs]
  exact chartAmplitudeMeasure_apply q.ball (chartAuxiliaryInverse r q)
    (fun a b => (continuous_apply b).comp
      ((continuous_apply a).comp (continuous_chartAuxiliaryInverse r q)))
    (chartAuxiliaryNorm_pos r q) ν hfin i j _ (hm hs)

/-- The radial map carries the same chart trace with the square of the
auxiliary covector norm as the weight on the round amplitude. -/
theorem cotangentAmplitudeMeasure_apply_round (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hscale : ∀ᵐ p ∂traceMeasure ν,
      chartAuxiliaryAmplitude r q ν hfin p =
        (symbolNorm (chartAuxiliaryInverse r q p.1) (roundCovector p) : ℂ) •
          chartRoundAmplitude q.ball ν hfin p)
    (i j : Pair) (s : Set (CotangentBundle M)) (hs : MeasurableSet s) :
    cotangentAmplitudeMeasure r q ν hfin i j s =
      ∫ p in chartAuxiliaryRay r q ⁻¹' s,
        (symbolNorm (chartAuxiliaryInverse r q p.1) (roundCovector p) : ℂ) *
          chartRoundAmplitude q.ball ν hfin p i j ∂traceMeasure ν := by
  rw [cotangentAmplitudeMeasure_apply r q ν hfin i j s hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hscale] with p hp
  exact congrFun (congrFun hp i) j

theorem cotangentAmplitudeMeasure_positive (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hP : ∀ᵐ p ∂traceMeasure ν, (chartAuxiliaryAmplitude r q ν hfin p).PosSemidef)
    (s : Set (CotangentBundle M)) (hs : MeasurableSet s) :
    Matrix.PosSemidef (fun i j => cotangentAmplitudeMeasure r q ν hfin i j s : Matrix Pair Pair ℂ) := by
  have hm : Measurable (chartAuxiliaryRay r q) := (continuous_chartAuxiliaryRay r q).measurable
  have hEntries : (fun i j => cotangentAmplitudeMeasure r q ν hfin i j s) =
      (fun i j => chartAmplitudeMeasure q.ball (chartAuxiliaryInverse r q) ν hfin i j
        (chartAuxiliaryRay r q ⁻¹' s)) := by
    funext i j
    exact VectorMeasure.map_apply _ hm hs
  rw [hEntries]
  exact chartAmplitudeMeasure_positive q.ball (chartAuxiliaryInverse r q)
    (fun a b => (continuous_apply b).comp
      ((continuous_apply a).comp (continuous_chartAuxiliaryInverse r q)))
    (chartAuxiliaryNorm_pos r q) ν hfin hP _ (hm hs)

theorem cotangentAmplitudeMeasure_zero_off_unit (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (i j : Pair) (s : Set (CotangentBundle M)) (hs : MeasurableSet s)
    (hout : ∀ p ∈ s, dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p ≠ 1) :
    cotangentAmplitudeMeasure r q ν hfin i j s = 0 := by
  have hpre : chartAuxiliaryRay r q ⁻¹' s = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun p hp =>
      hout (chartAuxiliaryRay r q p) hp (chartAuxiliaryRay_unit r q p)
  rw [cotangentAmplitudeMeasure_apply r q ν hfin i j s hs, hpre, Measure.restrict_empty,
    integral_zero_measure]

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- One refinement gives chartwise measures on the actual cotangent bundle
and the original and projected Fourier pairings on their common chart trace. -/
theorem exists_countable_originalVolume_cotangentAmplitudes {I : Type*} [Countable I]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B)
    (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (charts : I → CompactChartInput M) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∀ i,
      let q := charts i
      let w := originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)
      ∃ ν : (JetSlot → ℂ) → Measure (Chart q.ball), ∃ hfin : ∀ v, IsFiniteMeasure (ν v),
        RepresentsCompactJetPairings q.ball w (s ∘ t) ν hfin ∧
        Burnett.P01.RepresentsVolumeProjectedPairings B g q (s ∘ t) ν hfin ∧
        (∀ᵐ p ∂traceMeasure ν, ∀ v : Pair → ℂ,
          let k (a b : Index) := (chartAuxiliaryAmplitude r q ν hfin p *ᵥ v) (a, b)
          let η := auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)
          IsSymmetricComplexTensor k ∧
            ∀ a b, complexRicciSymbol (backgroundInverse B q.center p.1) η k a b = 0) ∧
        (∀ E : Set (CotangentBundle M), MeasurableSet E →
          Matrix.PosSemidef
            (fun a b => cotangentAmplitudeMeasure r q ν hfin a b E : Matrix Pair Pair ℂ)) ∧
        ∀ (a b : Pair) (E : Set (CotangentBundle M)), MeasurableSet E →
          cotangentAmplitudeMeasure r q ν hfin a b E =
            ∫ p in chartAuxiliaryRay r q ⁻¹' E,
              (symbolNorm (chartAuxiliaryInverse r q p.1) (roundCovector p) : ℂ) *
                chartRoundAmplitude q.ball ν hfin p a b ∂traceMeasure ν := by
  obtain ⟨t, ht, hCharts⟩ := Burnett.P01.exists_countable_originalVolume_projected_mixedPairings
    r B g hB hg hnB hsB hsG hconv hb charts s hs
  refine ⟨t, ht, fun i => ?_⟩
  obtain ⟨ν, hfin, hRep, hProj⟩ := hCharts i
  have hS := ae_originalVolume_auxiliaryAmplitude r B g hB hg hsB hsG hnB hnG
    hconv hb hv (charts i) (s ∘ t) (hs.comp ht) ν hfin hRep
  exact ⟨ν, hfin, hRep, hProj, hS.mono (fun _ h => h.2.2.2),
    fun E hE => cotangentAmplitudeMeasure_positive r (charts i) ν hfin
      (hS.mono fun _ h => h.1) E hE,
    fun a b E hE => cotangentAmplitudeMeasure_apply_round r (charts i) ν hfin
      (hS.mono fun _ h => h.2.2.1) a b E hE⟩

end Burnett.F05.ChartCotangentAmplitudeMeasure
