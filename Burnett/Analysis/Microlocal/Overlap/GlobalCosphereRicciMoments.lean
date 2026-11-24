import Burnett.Analysis.Microlocal.Overlap.GluedChartRicciMoments
import Burnett.Analysis.Microlocal.Overlap.GlobalCospherePhysicalMeasure

/-! Transport the common represented-chart Ricci moments to the actual unit cosphere. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open ManifoldMetricSequence BackgroundConnection CurvatureDifference UnitNullCompactness
open Burnett.Geometry.UnitCosphere
  (Cosphere projection hamiltonian fromAmbient fromAmbient_locallyFinite fromAmbient_regular
    fromAmbient_finiteOnCompactBase fromAmbient_offNull map_fromAmbient_eq_of_unitNull)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D Space)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- The common refinement and its countable chart witnesses give the represented chart laws
and Ricci moments on one actual unit cosphere measure. Its inclusion recovers the ambient witness. -/
theorem exists_originalVacuum_physicalMeasure_on_cosphere_and_representedChartMoments [Nonempty M]
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
              ∃ μr : Measure (Cosphere r),
                let μmap := μr.map (Subtype.val : Cosphere r → CotangentBundle M)
                μmap = μ ∧ IsLocallyFiniteMeasure μr ∧ μr.Regular ∧
                (∀ K : Set M, IsCompact K → μr (projection ⁻¹' K) < ⊤) ∧
                μr {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
                ∀ (q : CompactChartInput M) (νq : (JetSlot → ℂ) → Measure (Chart q.ball))
                    (hfq : ∀ v, IsFiniteMeasure (νq v)),
                  RepresentsCompactJetPairings q.ball
                    (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
                      (q.cutoff_support.trans q.ball_in_chart)) (s ∘ t) νq hfq →
                  let S := (fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus
                  μmap.restrict S =
                    (normalizedCotangentPhysicalMeasure q r B hSig.isNondegenerate νq hfq).restrict S ∧
                  ∀ ψ : D, tsupport (ψ : Space → ℝ) ⊆ {x | (q.cutoff : Space → ℝ) x ≠ 0} →
                    ∀ b d : Index,
                      let R (x : Space) := (ψ : Space → ℝ) x *
                        coordinateRicci (computedConnection (coordinateBilinear B q.center)) x b d
                      let F (p : CotangentBundle M) := (ψ : Space → ℝ) (chartAt CoordinateSpace q.center p.proj) *
                        (cotangentCoords q.center p b * cotangentCoords q.center p d)
                      let V := ManifoldVolume.coordinateMeasure B q.center
                      Integrable R V ∧ IntegrableOn F S μmap ∧
                      (∫ x, R x ∂V) = ∫ p in S, F p ∂μmap := by
  obtain ⟨t, ht, charts, hCover, ν, hf, hReps, μ, hLoc, hReg, hNull, hFinite, hLaw⟩ :=
    exists_originalVacuum_globalPhysicalMeasure_and_representedChartMoments
      r B g hB hg hSig hsG hnG hconv hb hv s hs
  letI : IsLocallyFiniteMeasure μ := hLoc
  letI : μ.Regular := hReg
  let μr := fromAmbient r μ
  have hmap : μr.map (Subtype.val : Cosphere r → CotangentBundle M) = μ :=
    map_fromAmbient_eq_of_unitNull r B hSig.isNondegenerate μ hNull
  refine ⟨t, ht, charts, hCover, ν, hf, hReps, μ, hLoc, hReg, hNull, hFinite, ?_⟩
  refine ⟨μr, hmap, fromAmbient_locallyFinite r μ, fromAmbient_regular r B hSig.isNondegenerate μ hNull,
    fromAmbient_finiteOnCompactBase r μ hFinite, fromAmbient_offNull r B hSig.isNondegenerate μ hNull,
    ?_⟩
  intro q νq hfq hRep S
  rw [hmap]
  exact hLaw q νq hfq hRep

end Burnett.Microlocal.Overlap
