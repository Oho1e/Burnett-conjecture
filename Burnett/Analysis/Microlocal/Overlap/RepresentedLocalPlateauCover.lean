import Burnett.Analysis.Microlocal.Overlap.OriginalCutoffRefinement

/-! Compact receiving windows can use finitely many represented original cutoffs. -/

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1500000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- A compact part of a receiving chart is covered by finitely many closed
plateau cutoffs of the original sequence. Each whole chart ball lies in the
receiving open set, and every pairing uses the prescribed subsequence. -/
theorem exists_originalVolume_finite_plateauCover_on_sameSubsequence
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
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hCover : K ⊆ ⋃ i, (q i).nonzeroLocus) :
    let core (a : CompactChartInput M) (δ : ℝ) :=
      let e := chartAt CoordinateSpace a.center
      e.source ∩ e ⁻¹' Metric.ball a.ball.center δ
    ∃ (S : Finset K) (d : S → CompactChartInput M) (δ : S → ℝ)
      (ν' : ∀ i, (JetSlot → ℂ) → Measure (Chart (d i).ball))
      (hfin : ∀ i v, IsFiniteMeasure (ν' i v)),
      K ⊆ ⋃ i : S, core (d i) (δ i) ∧
      ∀ i : S, let a := d i
        0 < δ i ∧ δ i < a.ball.radius ∧
        (chartAt CoordinateSpace a.center).symm '' a.ball.closedBall ⊆ U ∧
        tsupport (a.cutoff : CoordinateSpace → ℝ) ⊆ Metric.ball a.ball.center a.ball.radius ∧
        (∀ y, 0 ≤ (a.cutoff : CoordinateSpace → ℝ) y ∧ (a.cutoff : CoordinateSpace → ℝ) y ≤ 1) ∧
        (∀ y ∈ Metric.closedBall a.ball.center (δ i), (a.cutoff : CoordinateSpace → ℝ) y = 1) ∧
        RepresentsCompactJetPairings a.ball
          (originalGradient_volumeWeightedL2 B g hB hg hn a.center a.cutoff
            (a.cutoff_support.trans a.ball_in_chart)) σ (ν' i) (hfin i) := by
  classical
  intro core
  have hAt (x : K) : ∃ (a : CompactChartInput M) (δ : ℝ)
      (ρ : (JetSlot → ℂ) → Measure (Chart a.ball)) (hρ : ∀ v, IsFiniteMeasure (ρ v)),
      x.val ∈ core a δ ∧
      0 < δ ∧ δ < a.ball.radius ∧
      (chartAt CoordinateSpace a.center).symm '' a.ball.closedBall ⊆ U ∧
      tsupport (a.cutoff : CoordinateSpace → ℝ) ⊆ Metric.ball a.ball.center a.ball.radius ∧
      (∀ y, 0 ≤ (a.cutoff : CoordinateSpace → ℝ) y ∧ (a.cutoff : CoordinateSpace → ℝ) y ≤ 1) ∧
      (∀ y ∈ Metric.closedBall a.ball.center δ, (a.cutoff : CoordinateSpace → ℝ) y = 1) ∧
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hn a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ ρ hρ := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hCover x.property)
    obtain ⟨L, δ, χ, hL, hχ, hCenter, hPos, hInner, hBall, hSupport, hRange, hOne, ρ, hρ, hData⟩ :=
      exists_originalVolume_sameChart_plateau_on_sameSubsequence r B g hB hg hn hconv hb (q i)
        hi hU (hKU x.property) σ hσ (ν i) (hf i) (hRep i)
    let a : CompactChartInput M := ⟨(q i).center, L, hL, χ, hχ⟩
    let e := chartAt CoordinateSpace (q i).center
    have hx : x.val ∈ core a δ := by
      refine ⟨hi.1, ?_⟩
      change e x.val ∈ Metric.ball L.center δ
      rw [hCenter]
      exact Metric.mem_ball_self hPos
    have hImage : e.symm '' L.closedBall ⊆ U := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hBall hy
      rw [e.left_inv hz.2.1]
      exact hz.1
    exact ⟨a, δ, ρ, hρ, hx, hPos, hInner, hImage, hSupport, hRange, hOne, hData⟩
  choose d δ ρ hρ hCore hData using hAt
  have hOpen (x : K) : IsOpen (core (d x) (δ x)) :=
    (chartAt CoordinateSpace (d x).center).isOpen_inter_preimage Metric.isOpen_ball
  have hC : K ⊆ ⋃ x : K, core (d x) (δ x) := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hCore ⟨x, hx⟩⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover (fun x => core (d x) (δ x)) hOpen hC
  refine ⟨S, fun i => d i.val, fun i => δ i.val, fun i => ρ i.val, fun i => hρ i.val,
    ?_, fun i => hData i.val⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hS hx)
  exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩

end Burnett.Microlocal.Overlap
