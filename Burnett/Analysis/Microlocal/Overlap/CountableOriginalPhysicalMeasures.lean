import Burnett.Analysis.Microlocal.Overlap.OriginalPhysicalJetMeasure

/-! One common refinement supplies the physical measures of a countable chart family. -/

set_option autoImplicit false
set_option maxHeartbeats 550000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.Geometry.UnitNullCompactness (CotangentBundle cotangentUnitNull)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryRay)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.PhysicalDensity (physicalContraction)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- The original and projected pairings and the positive local physical
measures of every chart use a single strict refinement and the same
represented trace in each chart. -/
theorem exists_countable_originalVolume_physicalJetMeasures {I : Type*} [Countable I]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (charts : I → CompactChartInput M) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∃ ν : ∀ i : I, (JetSlot → ℂ) → Measure (Chart (charts i).ball),
      ∃ hfin : ∀ i a, IsFiniteMeasure (ν i a), ∀ i,
        let q := charts i
        let μ := cotangentPhysicalJetMeasure r B hSig.isNondegenerate q (ν i) (hfin i)
        RepresentsCompactJetPairings q.ball
          (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
            (q.cutoff_support.trans q.ball_in_chart)) (s ∘ t) (ν i) (hfin i) ∧
        Burnett.P01.RepresentsVolumeProjectedPairings B g q (s ∘ t) (ν i) (hfin i) ∧
        IsFiniteMeasure μ ∧ μ (cotangentUnitNull r B hSig.isNondegenerate)ᶜ = 0 ∧
        ∀ S : Set (CotangentBundle M), MeasurableSet S →
          ((μ S).toReal : ℂ) =
            ∫ z in (chartAuxiliaryRay r q ⁻¹' S) ∩ chartAuxiliaryNull r B hSig.isNondegenerate q,
              (1 / 4 : ℂ) * physicalContraction (backgroundInverse B q.center z.1)
                (chartAuxiliaryAmplitude r q (ν i) (hfin i) z) ∂traceMeasure (ν i) := by
  obtain ⟨t, ht, hCharts⟩ := Burnett.P01.exists_countable_originalVolume_projected_mixedPairings
    r B g hB hg hSig.isNondegenerate hSig.isSymmetric hsG hconv hb charts s hs
  choose ν hfin hRep hProj using hCharts
  refine ⟨t, ht, ν, hfin, fun i => ⟨hRep i, hProj i, ?_, ?_, ?_⟩⟩
  · exact isFiniteMeasure_cotangentPhysicalJetMeasure
      r B hSig.isNondegenerate (charts i) (ν i) (hfin i) hB
  · exact cotangentPhysicalJetMeasure_compl_null
      r B hSig.isNondegenerate (charts i) (ν i) (hfin i) hB hSig.isSymmetric
  · intro S hS
    exact original_cotangentPhysicalJetMeasure_apply_eq_setIntegral
      r B g hB hg hSig hsG hnG hconv hb hv (charts i) (s ∘ t) (hs.comp ht) (ν i) (hfin i) (hRep i) hS

end Burnett.Microlocal.Overlap
