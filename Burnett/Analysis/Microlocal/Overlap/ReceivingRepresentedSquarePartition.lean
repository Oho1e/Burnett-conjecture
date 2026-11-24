import Burnett.Analysis.Microlocal.Overlap.ReceivingSquareLocalization
import Burnett.Analysis.Microlocal.Overlap.RepresentedLocalPlateauCover
import Burnett.Geometry.MaximalChart.MetricCoordinates

/-! A finite square partition subordinate to actual original represented plateaus. -/

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1700000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped Topology ContDiff Manifold BigOperators

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The same original subsequence admits a finite smooth square partition of
any compact receiving window, with each part supported inside an actual
represented source plateau. -/
theorem exists_receiving_square_partition_on_sameSubsequence
    {I : Type*} (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (q : I → CompactChartInput M)
    (ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball))
    (hf : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let a := q i
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hn a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i))
    (c : AtlasChart M) (L : Set E) (hL : IsCompact L) (hLc : L ⊆ c.chart.target)
    (hCover : c.chart.symm '' L ⊆ ⋃ i, (q i).nonzeroLocus) :
    ∃ (n : ℕ) (d : Fin n → CompactChartInput M) (δ : Fin n → ℝ)
      (χ : Fin n → D) (ρ : ∀ i, (JetSlot → ℂ) → Measure (Chart (d i).ball))
      (hρ : ∀ i v, IsFiniteMeasure (ρ i v)),
      (∀ y ∈ L, ∑ i, (χ i : E → ℝ) y ^ 2 = 1) ∧
      ∀ i, let a := d i
        let e := (AtlasChart.atPoint a.center).transition c
        0 < δ i ∧ δ i < a.ball.radius ∧
        a.ball.closedBall ⊆ e.source ∧
        tsupport (χ i : E → ℝ) ⊆ e '' Metric.closedBall a.ball.center (δ i) ∧
        (∀ y ∈ Metric.closedBall a.ball.center (δ i), (a.cutoff : E → ℝ) y = 1) ∧
        RepresentsCompactJetPairings a.ball
          (originalGradient_volumeWeightedL2 B g hB hg hn a.center a.cutoff
            (a.cutoff_support.trans a.ball_in_chart)) σ (ρ i) (hρ i) := by
  let K := c.chart.symm '' L
  have hK : IsCompact K := hL.image_of_continuousOn (c.chart.continuousOn_symm.mono hLc)
  have hKU : K ⊆ c.chart.source := image_subset_iff.mpr (c.chart.symm_mapsTo.mono_left hLc)
  obtain ⟨S, d, δ, ρ, hρ, hKCover, hData⟩ :=
    exists_originalVolume_finite_plateauCover_on_sameSubsequence r B g hB hg hn hconv hb σ hσ
      q ν hf hRep hK c.chart.open_source hKU hCover
  let e (i : S) := (AtlasChart.atPoint (d i).center).transition c
  let U (i : S) := Metric.ball (d i).ball.center (δ i)
  let V (i : S) := e i '' U i
  have hBall (i : S) : (d i).ball.closedBall ⊆ (e i).source := by
    intro x hx
    exact ⟨(d i).ball_in_chart hx, (hData i).2.2.1 (mem_image_of_mem _ hx)⟩
  have hInner (i : S) : U i ⊆ (d i).ball.closedBall :=
    (Metric.ball_subset_ball (hData i).2.1.le).trans Metric.ball_subset_closedBall
  have hV (i : S) : IsOpen (V i) :=
    (e i).isOpen_image_of_subset_source Metric.isOpen_ball ((hInner i).trans (hBall i))
  have hLV : L ⊆ ⋃ i, V i := by
    intro y hy
    have hy' := hKCover (mem_image_of_mem c.chart.symm hy)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy'
    let f := chartAt E (d i).center
    have hf₀ : c.chart.symm y ∈ f.source := hi.1
    have hf₁ : f (c.chart.symm y) ∈ U i := hi.2
    have hEq : e i (f (c.chart.symm y)) = y := by
      change c.chart (f.symm (f (c.chart.symm y))) = y
      rw [f.left_inv hf₀, c.chart.right_inv (hLc hy)]
    exact mem_iUnion.mpr ⟨i, ⟨_, hf₁, hEq⟩⟩
  obtain ⟨n, idx, χ, hχ, hSum⟩ := exists_squareCutoffs_subordinateTo_openCover V hV L hL hLV
  refine ⟨n, fun i => d (idx i), fun i => δ (idx i), χ, fun i => ρ (idx i),
    fun i => hρ (idx i), hSum, ?_⟩
  intro i
  obtain ⟨hδ, hδR, _, _, _, hPlateau, hRep'⟩ := hData (idx i)
  exact ⟨hδ, hδR, hBall (idx i), (hχ i).trans (image_mono Metric.ball_subset_closedBall), hPlateau, hRep'⟩

end Burnett.Microlocal.Overlap
