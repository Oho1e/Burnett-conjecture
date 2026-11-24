import Burnett.Analysis.Microlocal.CompactAmplitudeCover
import Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeAuxiliaryControlFinite
import Burnett.Analysis.Microlocal.Overlap.IntrinsicAmplitudeOverlap
import Burnett.Geometry.GluedMeasureCompactProjection
import Burnett.Geometry.GluedMeasureSection

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 2400000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity)
open Burnett.Geometry.MeasureGluing
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- A positive control measure and a covariant four-slot amplitude density on
the actual auxiliary unit cosphere. -/
structure IntrinsicAmplitudeCovariance (r : Metric (M := M)) where
  control : Measure (Cosphere r)
  density : AmplitudeCovarianceDensity r

/-- Recover the true control and density on every compact part of any
represented chart's nonzero locus on the specified original subsequence. -/
def HasOriginalAmplitudeChartLaws
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r) : Prop :=
  ∀ (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
    (hf : ∀ v, IsFiniteMeasure (ν v)),
    RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf →
    ∀ K : Set M, IsCompact K → K ⊆ q.nonzeroLocus →
      let U := amplitudeCosphereWindow r K
      let τ := (chartAmplitudeTraceControl r q ν hf).restrict U
      A.control.restrict U = τ ∧
        ∀ᵐ p ∂τ, A.density p = chartNormalizedIntrinsicAmplitude r q ν hf p

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- Assemble the original normalized chart data into one intrinsic covariance.
Any other represented chart of the same sequence has its own control and
density recovered on each compact base window. -/
theorem original_globalIntrinsicAmplitude_of_representedCharts
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (q : ℕ → CompactChartInput M) (cover : ⋃ i, (q i).cutoffLocusAbove (1 / 2) = univ)
    (ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball))
    (hf : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let a := q i
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hnB a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i)) :
    ∃ A : IntrinsicAmplitudeCovariance r,
      IsLocallyFiniteMeasure A.control ∧
      (∀ K : Set M, IsCompact K → A.control (projection ⁻¹' K) < ⊤) ∧
      HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A := by
  let π := projection (r := r)
  let K (i : ℕ) := (q i).compactCutoffLocus (1 / 2)
  let V (i : ℕ) := (q i).cutoffLocusAbove (1 / 2)
  let U (i : ℕ) := π ⁻¹' K i
  let τ (i : ℕ) := chartAmplitudeTraceControl r (q i) (ν i) (hf i)
  let L (i : ℕ) := chartNormalizedIntrinsicAmplitude r (q i) (ν i) (hf i)
  have hCompact (i : ℕ) : IsCompact (K i) := (q i).isCompact_compactCutoffLocus (1 / 2)
  have hNested (i : ℕ) : V i ⊆ K i :=
    (q i).cutoffLocusAbove_subset_compactCutoffLocus (by norm_num)
  have hNonzero (i : ℕ) : K i ⊆ (q i).nonzeroLocus :=
    (q i).compactCutoffLocus_subset_nonzeroLocus (by norm_num)
  have hOpen (i : ℕ) : IsOpen (V i) := (q i).isOpen_cutoffLocusAbove (1 / 2)
  have hMeas (i : ℕ) : MeasurableSet (U i) :=
    ((hCompact i).isClosed.preimage (continuous_projection r)).measurableSet
  have hCover : ⋃ i, U i = univ := by
    refine eq_univ_of_forall fun p => ?_
    have hp : π p ∈ ⋃ i, V i := cover.symm ▸ mem_univ (π p)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨i, hNested i hi⟩
  have hCompare (i : ℕ) (d : CompactChartInput M) (ρ : (JetSlot → ℂ) → Measure (Chart d.ball))
      (hρ : ∀ v, IsFiniteMeasure (ρ v))
      (hD : RepresentsCompactJetPairings d.ball
        (originalGradient_volumeWeightedL2 B g hB hg hnB d.center d.cutoff
          (d.cutoff_support.trans d.ball_in_chart)) σ ρ hρ)
      {J : Set M} (hJ : IsCompact J) (hJsub : J ⊆ d.nonzeroLocus) :
      let UJ := π ⁻¹' J
      let τd := chartAmplitudeTraceControl r d ρ hρ
      let D := chartNormalizedIntrinsicAmplitude r d ρ hρ
      (τ i).restrict (U i ∩ UJ) = τd.restrict (U i ∩ UJ) ∧
        ∀ᵐ p ∂(τ i).restrict (U i ∩ UJ), L i p = D p := by
    intro UJ τd D
    have hKJ : IsCompact (K i ∩ J) := (hCompact i).inter_right hJ.isClosed
    have hSub : K i ∩ J ⊆ (q i).nonzeroLocus ∩ d.nonzeroLocus :=
      fun _ hx => ⟨hNonzero i hx.1, hJsub hx.2⟩
    have h := original_compactOverlap_intrinsicAmplitude_agree r B g hB hg hsB hsG hnB hnG
      hconv hb hv σ hσ (q i) d (ν i) (hf i) ρ hρ (hRep i) hD hKJ hSub
    simpa only [amplitudeCosphereWindow, preimage_inter, U, UJ, π, τ, τd, L, D] using h
  have hMatch (i j : ℕ) : (τ i).restrict (U i ∩ U j) = (τ j).restrict (U i ∩ U j) :=
    (hCompare i (q j) (ν j) (hf j) (hRep j) (hCompact j) (hNonzero j)).1
  obtain ⟨hLoc, hFinite⟩ := glued_locallyFinite_and_finiteOnCompactBase
    π (continuous_projection r) K V hMeas hOpen cover hNested τ
    (fun i => chartAmplitudeTraceControl_lt_top_on_compact r (q i) (ν i) (hf i) (hCompact i) (hNonzero i))
    hMatch
  refine ⟨⟨glued U τ, gluedSection U hCover L⟩, hLoc, hFinite, ?_⟩
  intro d ρ hρ hD J hJ hJsub
  let UJ := π ⁻¹' J
  let τd := chartAmplitudeTraceControl r d ρ hρ
  let D := chartNormalizedIntrinsicAmplitude r d ρ hρ
  have hUJ : MeasurableSet UJ := (hJ.isClosed.preimage (continuous_projection r)).measurableSet
  have hOn (i) := hCompare i d ρ hρ hD hJ hJsub
  refine gluedMeasureSection_restrict_of_compatible U hMeas hCover τ L UJ hUJ τd D
    (fun i => (hOn i).1) (fun i => ?_)
  rw [← (hOn i).1]
  exact (hOn i).2

end Burnett.Microlocal.Overlap
