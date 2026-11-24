import Burnett.Analysis.Microlocal.OriginalVolumeMatrixMeasure
import Burnett.Geometry.AuxiliaryAdmissibility

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Burnett.Microlocal.CountableAuxiliaryCharts

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open Burnett.X02.SobolevTestJet (Space)
open scoped ContDiff Manifold Topology

/-- A strict refinement of the original subsequence preserves the very same
matrix-measure representation on the original window. -/
theorem RepresentsCompactJetPairings.comp_strictMono
    {K : BallData} {w : ℕ → JetSlot → ComplexL2 Space} {σ : ℕ → ℕ}
    {ν : (JetSlot → ℂ) → Measure (Chart K)} {hfin : ∀ v, IsFiniteMeasure (ν v)}
    (h : RepresentsCompactJetPairings K w σ ν hfin) (τ : ℕ → ℕ) (hτ : StrictMono τ) :
    RepresentsCompactJetPairings K w (σ ∘ τ) ν hfin := by
  obtain ⟨hr, hf, hp, ha, hs, hd, hLim⟩ := h
  refine ⟨hr, hf, hp, ha, hs, hd, ?_⟩
  intro J _ a m hA hM hD i j
  exact (hLim J a m hA hM hD i j).comp hτ.tendsto_atTop

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Two new chart cutoffs admit actual matrix measure witnesses on one
common strict refinement of a prescribed original subsequence. -/
theorem exists_common_refinement_originalVolume_pairDensities
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q d : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      (∃ νq : (JetSlot → ℂ) → Measure (Chart q.ball), ∃ hfq : ∀ v, IsFiniteMeasure (νq v),
        RepresentsCompactJetPairings q.ball (originalGradient_volumeWeightedL2 B g hB hg hnB
          q.center q.cutoff (q.cutoff_support.trans q.ball_in_chart)) (σ ∘ τ) νq hfq) ∧
      (∃ νd : (JetSlot → ℂ) → Measure (Chart d.ball), ∃ hfd : ∀ v, IsFiniteMeasure (νd v),
        RepresentsCompactJetPairings d.ball (originalGradient_volumeWeightedL2 B g hB hg hnB
          d.center d.cutoff (d.cutoff_support.trans d.ball_in_chart)) (σ ∘ τ) νd hfd) := by
  let charts (a : Bool) : CompactChartInput M := if a then q else d
  obtain ⟨τ, hτ, h⟩ := exists_countable_originalVolume_matrixDensities r B g hB hg hnB hconv hb
    charts σ hσ
  exact ⟨τ, hτ, by simpa [charts] using h true, by simpa [charts] using h false⟩

end Burnett.Microlocal.CountableAuxiliaryCharts
