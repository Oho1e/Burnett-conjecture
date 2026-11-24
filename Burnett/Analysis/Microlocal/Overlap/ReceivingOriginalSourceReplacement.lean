import Burnett.Analysis.Microlocal.Overlap.ReceivingChartSourceTransport
import Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical

/-! The finite replacement expressed in the actual represented input of the original extraction. -/

set_option autoImplicit false
set_option maxRecDepth 3300
set_option maxHeartbeats 2250000

noncomputable section
namespace Burnett.Microlocal.AtlasVolumeGradient

open Set Filter MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Microlocal.AtlasOverlapKernel (transportedHalfDensitySchwartz)
open Burnett.Microlocal.BesselLocalization (coeffMul)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.Overlap
open Burnett.F05.OverlapCovariantGradient (originalVolumeGradientSchwartz)
open Burnett.X02.SobolevTestJet (D)
open scoped Topology Manifold ContDiff BigOperators

open private coeffMul_originalVolumeAngularInput from Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

theorem coeffMul_tsupport_subset_real (a : D) (f : SchwartzMap E ℂ) :
    tsupport (coeffMul a f : E → ℂ) ⊆ tsupport (a : E → ℝ) := by
  apply closure_mono
  intro x hx
  by_contra h
  have hz : a.val x = 0 := by simpa [Function.mem_support] using h
  exact hx (by
    change ((a : E → ℝ) x : ℂ) * f x = 0
    rw [hz, Complex.ofReal_zero, zero_mul])

/-- Exact ordered cutoffs recover the actual receiving field strongly, with
each source term taken from the already represented original input. -/
theorem exists_receivingSourceCutoffs_of_originalVolume
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (q : CompactChartInput M) (d : AtlasChart M)
    (hOuter : q.ball.closedBall ⊆ ((AtlasChart.atPoint q.center).transition d).source)
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus ∩ d.chart.source)
    (η : D) (hη : tsupport (η : E → ℝ) ⊆ d.chart '' K)
    (hηd : tsupport (η : E → ℝ) ⊆ d.chart.target) (i : JetSlot) :
    let c := AtlasChart.atPoint q.center
    let S := q.ball.closedBall
    let hS : IsCompact S := isCompact_closedBall _ _
    let hKS : c.chart '' K ⊆ S := fun _ ⟨_x, hx, he⟩ =>
      he ▸ q.cutoff_support (subset_tsupport _ (hSub hx).1.2)
    let f := originalVolumeAngularInput B g hB hg hn q
    ∃ (α : JetSlot → D) (hαS : ∀ k, tsupport (α k : E → ℝ) ⊆ c.chart '' K),
      (∀ k x, x ∈ c.chart '' K →
        (α k : E → ℝ) x = (η : E → ℝ) (c.transition d x) *
          ((q.cutoff : E → ℝ) x)⁻¹ * inverseJetEntry c d i k x) ∧
      let F (n : ℕ) (k : JetSlot) := transportedHalfDensitySchwartz c d S hS hOuter
        (coeffMul (α k) (f n k)) ((coeffMul_tsupport_subset_real _ _).trans ((hαS k).trans hKS))
      Tendsto (fun n => (fixedVolumeGradientSchwartz B g hB hg hn d η hηd n i).toLp 2 volume -
        ∑ k : JetSlot, (F n k).toLp 2 volume) atTop (𝓝 0) := by
  intro c S hS hKS f
  let L := c.chart '' K
  have hKL : IsCompact L :=
    hK.image_of_continuousOn (c.chart.continuousOn.mono (fun _ hx => (hSub hx).1.1))
  have hLE : L ⊆ (c.transition d).source := hKS.trans hOuter
  have hηL : tsupport (η : E → ℝ) ⊆ (c.transition d) '' L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hη hx
    refine ⟨c.chart y, mem_image_of_mem _ hy, ?_⟩
    change d.chart (c.chart.symm (c.chart y)) = d.chart y
    rw [c.chart.left_inv (hSub hy).1.1]
  obtain ⟨a, haS, ha⟩ := exists_ordered_source_cutoffs c d L hKL hLE η hηL i
  have hANZ (k : JetSlot) (x : E) (hx : x ∈ tsupport (a k : E → ℝ)) :
      (q.cutoff : E → ℝ) x ≠ 0 := by
    obtain ⟨y, hy, rfl⟩ := haS k hx
    exact (hSub hy).1.2
  let α (k : JetSlot) := cutoffQuotient (a k) q.cutoff (hANZ k)
  have hαS (k : JetSlot) : tsupport (α k : E → ℝ) ⊆ L := tsupport_mul_subset_left.trans (haS k)
  refine ⟨α, hαS, ?_, ?_⟩
  · intro k x hx
    change (a k : E → ℝ) x * ((q.cutoff : E → ℝ) x)⁻¹ = _
    rw [ha k x (hLE hx)]
    ring
  · let hA (k : JetSlot) := (haS k).trans hKS
    let hAc (k : JetSlot) := (hA k).trans q.ball_in_chart
    have hEq (n : ℕ) (k : JetSlot) : coeffMul (α k) (f n k) =
        fixedVolumeGradientSchwartz B g hB hg hn c (a k) (hAc k) n k := by
      rw [coeffMul_originalVolumeAngularInput B g hB hg hn q (a k) (hA k) (hANZ k),
        fixedVolumeGradientSchwartz_eq_preferred]
      rfl
    have hErr := fixedVolumeGradient_sub_sum_transportedSource_tendsto_zero r B g hB hg hn hconv c d S hS hOuter
      η (hηL.trans (image_mono hKS)) hηd i a hA ha
    dsimp only at hErr ⊢
    have hTransport (n : ℕ) (k : JetSlot) :
        transportedHalfDensitySchwartz c d S hS hOuter (coeffMul (α k) (f n k))
          ((coeffMul_tsupport_subset_real _ _).trans ((hαS k).trans hKS)) =
        transportedHalfDensitySchwartz c d S hS hOuter (fixedVolumeGradientSchwartz B g hB hg hn c (a k) (hAc k) n k)
          ((fixedVolumeGradientSchwartz_tsupport B g hB hg hn c (a k) (hAc k) n k).trans (hA k)) := by
      apply SchwartzMap.ext
      intro x
      simp only [Burnett.Microlocal.AtlasOverlapKernel.coe_transportedHalfDensitySchwartz, hEq]
    simpa only [hTransport] using hErr

end Burnett.Microlocal.AtlasVolumeGradient
