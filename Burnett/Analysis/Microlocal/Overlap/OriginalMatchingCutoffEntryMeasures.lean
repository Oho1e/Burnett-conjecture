import Burnett.Analysis.Microlocal.Overlap.MatchingCutoffDensityPairings
import Burnett.Analysis.Microlocal.Overlap.CompactInteriorEntryMeasures

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.F05.ChartVolumeAmplitude
open Burnett.F05.OverlapCovariantGradient (overlapJetCoefficient)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped BigOperators ComplexConjugate ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The two independently represented original gradient densities with
matching cutoffs have the corresponding weighted Borel-set entries. -/
theorem exists_original_matchingCutoff_roundEntryMeasures
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q d : CompactChartInput M)
    (hKU : q.ball.closedBall ⊆ (chartTransition q.center d.center).source)
    (hMap : MapsTo (chartTransition q.center d.center) q.ball.closedBall d.ball.closedBall)
    (hηK : tsupport (d.cutoff : E → ℝ) ⊆ chartTransition q.center d.center '' q.ball.closedBall)
    (hCut : ∀ x ∈ (chartTransition q.center d.center).source,
      (d.cutoff : E → ℝ) (chartTransition q.center d.center x) = (q.cutoff : E → ℝ) x)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (hRq : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq)
    (hRd : RepresentsCompactJetPairings d.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB d.center d.cutoff
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd) :
    let T := roundChartWindowMap q d hKU hMap
    ∃ w : JetSlot → JetSlot → D,
      (∀ i k, EqOn (w i k : E → ℝ) (overlapJetCoefficient q.center d.center i k)
        (chartTransition q.center d.center '' q.ball.closedBall)) ∧
      ∀ (ζ : BoundedSymbol E) (_ : ContDiff ℝ ∞ (ζ : E → ℂ))
        (_ : tsupport (ζ : E → ℂ) ⊆ chartTransition q.center d.center '' q.ball.closedBall)
        (S : Set (Chart d.ball)) (_ : MeasurableSet S) (i j : JetSlot),
        (∫ p in T ⁻¹' S, ζ (T p).1 * density νq hfq p i j ∂traceMeasure νq) =
          ∫ y in S, ∑ k : JetSlot, ∑ l : JetSlot,
            ζ y.1 * conj (physicalCoefficient (w i k) y.1) * physicalCoefficient (w j l) y.1 *
              density νd hfd y k l ∂traceMeasure νd := by
  intro T
  obtain ⟨w, hw, hTests⟩ := exists_matchingCutoff_overlap_densityPairings r B g hB hg hnB hconv hb
    q d hKU hηK hCut σ hσ νq hfq νd hfd hRq hRd
  refine ⟨w, hw, ?_⟩
  intro ζ hζ hζS S hS i j
  have hCoeff (i' k : JetSlot) : Continuous (physicalCoefficient (w i' k) : E → ℂ) :=
    Complex.continuous_ofReal.comp (test_smooth (w i' k)).continuous
  refine weighted_setIntegral_roundChart_eq_of_overlap_tests q d hKU hMap νq hfq νd hfd i j
    (fun k => physicalCoefficient (w i k)) (fun l => physicalCoefficient (w j l))
    (hCoeff i) (hCoeff j) ?_ ζ hζ hζS S hS
  intro b m hb hSupp hm hd
  obtain ⟨a, _, _, hPull, hEq⟩ := hTests b m hb hSupp hm hd
  exact ⟨a, hPull, hEq i j⟩

/-- On Borel sets over a compact inner target window, the original
gradient densities with matching transported cutoffs obey the unweighted
entry transformation law. -/
theorem exists_original_matchingCutoff_compactInteriorEntryMeasures
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q d : CompactChartInput M)
    (hKU : q.ball.closedBall ⊆ (chartTransition q.center d.center).source)
    (hMap : MapsTo (chartTransition q.center d.center) q.ball.closedBall d.ball.closedBall)
    (hηK : tsupport (d.cutoff : E → ℝ) ⊆ chartTransition q.center d.center '' q.ball.closedBall)
    (hCut : ∀ x ∈ (chartTransition q.center d.center).source,
      (d.cutoff : E → ℝ) (chartTransition q.center d.center x) = (q.cutoff : E → ℝ) x)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (hRq : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq)
    (hRd : RepresentsCompactJetPairings d.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB d.center d.cutoff
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd) :
    let T := roundChartWindowMap q d hKU hMap
    ∃ w : JetSlot → JetSlot → D,
      (∀ i k, EqOn (w i k : E → ℝ) (overlapJetCoefficient q.center d.center i k)
        (chartTransition q.center d.center '' q.ball.closedBall)) ∧
      ∀ (C : Set E) (_ : IsCompact C)
        (_ : C ⊆ interior (chartTransition q.center d.center '' q.ball.closedBall))
        (S : Set (Chart d.ball)) (_ : MeasurableSet S) (_ : ∀ y ∈ S, (y.1 : E) ∈ C)
        (i j : JetSlot),
        (∫ p in T ⁻¹' S, density νq hfq p i j ∂traceMeasure νq) =
          ∫ y in S, ∑ k : JetSlot, ∑ l : JetSlot,
            conj (physicalCoefficient (w i k) y.1) * physicalCoefficient (w j l) y.1 *
              density νd hfd y k l ∂traceMeasure νd := by
  intro T
  obtain ⟨w, hw, hEntries⟩ := exists_original_matchingCutoff_roundEntryMeasures r B g hB hg hnB hconv hb
    q d hKU hMap hηK hCut σ hσ νq hfq νd hfd hRq hRd
  refine ⟨w, hw, ?_⟩
  intro C hC hInside S hS hSC i j
  exact setIntegral_roundChart_eq_on_compact_interior q d hKU hMap νq hfq νd hfd i j
    (fun k => physicalCoefficient (w i k)) (fun l => physicalCoefficient (w j l))
    C hC hInside S hS hSC (fun ζ hζ hζS => hEntries ζ hζ hζS S hS i j)

end Burnett.Microlocal.Overlap
