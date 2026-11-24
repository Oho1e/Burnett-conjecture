import Burnett.Analysis.Microlocal.Overlap.NormalizedChartAuxiliaryMeasureChange
import Burnett.Analysis.Microlocal.PhysicalChartCover

/-! The common original chart laws determine the global auxiliary change on the cotangent bundle. -/

set_option autoImplicit false
set_option maxHeartbeats 1300000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- If two ambient measures realize the same normalized original chart witnesses
at the two auxiliary metrics, the new ambient measure is the precise weighted
renormalization of the old one. -/
theorem original_globalPhysicalMeasure_changeAuxiliary_of_chartLaws
    (r r' : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (charts : ℕ → CompactChartInput M) (cover : (⋃ i, (charts i).cutoffLocusAbove (1 / 2)) = univ)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : ∀ i : ℕ, (JetSlot → ℂ) → Measure (Chart (charts i).ball))
    (hfin : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let q := charts i
      RepresentsCompactJetPairings q.ball
        (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
          (q.cutoff_support.trans q.ball_in_chart)) σ (ν i) (hfin i))
    (μ μ' : Measure (CotangentBundle M))
    (hLaws : ∀ i, let q := charts i
      let S := (fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus
      μ.restrict S =
        (normalizedCotangentPhysicalMeasure q r B hSig.isNondegenerate (ν i) (hfin i)).restrict S ∧
      μ'.restrict S =
        (normalizedCotangentPhysicalMeasure q r' B hSig.isNondegenerate (ν i) (hfin i)).restrict S) :
    μ' = renormalizeCotangentPhysicalMeasure r' μ := by
  let S (i : ℕ) := (fun p : CotangentBundle M => p.proj) ⁻¹' (charts i).nonzeroLocus
  have hCover : (⋃ i, S i) = univ := by
    apply eq_univ_of_forall
    intro p
    have hp : p.proj ∈ ⋃ i, (charts i).cutoffLocusAbove (1 / 2) := cover.symm ▸ mem_univ _
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨i, (charts i).cutoffLocusAbove_subset_nonzeroLocus
      (by norm_num : (0 : ℝ) < (1 / 2)) hi⟩
  apply Measure.ext_of_iUnion_eq_univ hCover
  intro i
  have hS : MeasurableSet (S i) :=
    ((charts i).isOpen_nonzeroLocus.preimage continuous_cotangent_projection).measurableSet
  obtain ⟨hOld, hNew⟩ := hLaws i
  have hLocal := original_normalizedCotangentPhysicalMeasure_changeAuxiliary
    r r' B g hB hg hSig hsG hnG hconv hb hv (charts i) σ hσ (ν i) (hfin i) (hRep i)
  have hLocalRestrict := renormalizeCotangentPhysicalMeasure_restrict_base r'
    (normalizedCotangentPhysicalMeasure (charts i) r B hSig.isNondegenerate (ν i) (hfin i))
    (U := (charts i).nonzeroLocus) hS
  rw [renormalizeCotangentPhysicalMeasure_restrict_base r' μ
    (U := (charts i).nonzeroLocus) hS, hOld, ← hLocalRestrict, ← hLocal, ← hNew]

end Burnett.Microlocal.Overlap
