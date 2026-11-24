import Burnett.Analysis.Microlocal.Overlap.RepresentedCotangentMoment
import Burnett.Analysis.Microlocal.Overlap.GlobalOriginalPhysicalMeasure

set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open ManifoldMetricSequence BackgroundConnection CurvatureDifference UnitNullCompactness
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D Space)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M] [Nonempty M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- One original refinement and one locally finite regular measure give the
Ricci moments on every chart represented along that refinement. The selected
countable chart family has such representatives and covers the base. -/
theorem exists_originalVacuum_globalPhysicalMeasure_and_representedChartMoments
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∃ charts : ℕ → CompactChartInput M,
        (⋃ i, (charts i).cutoffLocusAbove (1 / 2)) = univ ∧
        ∃ ν : ∀ i : ℕ, (JetSlot → ℂ) → Measure (Chart (charts i).ball),
          ∃ hf : ∀ i v, IsFiniteMeasure (ν i v),
            (∀ i, let q := charts i
              RepresentsCompactJetPairings q.ball
                (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
                  (q.cutoff_support.trans q.ball_in_chart)) (s ∘ t) (ν i) (hf i) ∧
              Burnett.P01.RepresentsVolumeProjectedPairings B g q (s ∘ t) (ν i) (hf i)) ∧
            ∃ μ : Measure (CotangentBundle M), IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
              μ (cotangentUnitNull r B hSig.isNondegenerate)ᶜ = 0 ∧
              (∀ K : Set M, IsCompact K → μ ((fun p : CotangentBundle M => p.proj) ⁻¹' K) < ⊤) ∧
              ∀ (q : CompactChartInput M) (νq : (JetSlot → ℂ) → Measure (Chart q.ball))
                  (hfq : ∀ v, IsFiniteMeasure (νq v)),
                RepresentsCompactJetPairings q.ball
                  (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
                    (q.cutoff_support.trans q.ball_in_chart)) (s ∘ t) νq hfq →
                let S := (fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus
                μ.restrict S = (normalizedCotangentPhysicalMeasure q r B hSig.isNondegenerate νq hfq).restrict S ∧
                ∀ ψ : D, tsupport (ψ : Space → ℝ) ⊆ {x | (q.cutoff : Space → ℝ) x ≠ 0} →
                  ∀ b d : Index,
                    let R (x : Space) := (ψ : Space → ℝ) x *
                      coordinateRicci (computedConnection (coordinateBilinear B q.center)) x b d
                    let F (p : CotangentBundle M) := (ψ : Space → ℝ) (chartAt CoordinateSpace q.center p.proj) *
                      (cotangentCoords q.center p b * cotangentCoords q.center p d)
                    let V := ManifoldVolume.coordinateMeasure B q.center
                    Integrable R V ∧ IntegrableOn F S μ ∧ (∫ x, R x ∂V) = ∫ p in S, F p ∂μ := by
  obtain ⟨t, ht, charts, hCover, ν, hf, hReps, μ, hLoc, hReg, hNull, hFinite, hLaw⟩ :=
    exists_originalVacuum_globalPhysicalMeasure r B g hB hg hSig hsG hnG hconv hb hv s hs
  refine ⟨t, ht, charts, hCover, ν, hf, hReps, μ, hLoc, hReg, hNull, hFinite, ?_⟩
  intro q νq hfq hRep S
  refine ⟨hLaw q νq hfq hRep, ?_⟩
  intro ψ hψ b d
  exact original_chartRicci_eq_cotangent_secondMoment r B g hB hg hSig hsG hnG hconv hb hv
    q (s ∘ t) (hs.comp ht) νq hfq hRep μ (hLaw q νq hfq hRep) ψ hψ b d

end Burnett.Microlocal.Overlap
