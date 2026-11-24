import Burnett.Analysis.Microlocal.Overlap.ReceivingChartGradientError
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartHalfDensity

/-! Bind the original receiving gradients to the actual zero-extended half-density transport. -/

set_option autoImplicit false
set_option maxRecDepth 3300
set_option maxHeartbeats 1750000

noncomputable section
namespace Burnett.Microlocal.AtlasVolumeGradient

open Set Filter MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Microlocal.AtlasOverlapKernel
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped Topology Manifold ContDiff BigOperators

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- The ordered original source fields are pushed forward by the actual
overlap half-density operator. Their sum strongly recovers the localized
original gradient in the receiving chart. -/
theorem fixedVolumeGradient_sub_sum_transportedSource_tendsto_zero
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (c d : AtlasChart M)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (η : D) (hη : tsupport (η : E → ℝ) ⊆ (c.transition d) '' K)
    (hηd : tsupport (η : E → ℝ) ⊆ d.chart.target)
    (i : JetSlot) (a : JetSlot → D) (hS : ∀ j, tsupport (a j : E → ℝ) ⊆ K)
    (ha : ∀ j x, x ∈ (c.transition d).source →
      (a j : E → ℝ) x = (η : E → ℝ) (c.transition d x) * inverseJetEntry c d i j x) :
    let hs (j : JetSlot) : tsupport (a j : E → ℝ) ⊆ c.chart.target :=
      (hS j).trans (fun _ hx => (hKU hx).1)
    let U (n : ℕ) (j : JetSlot) := fixedVolumeGradientSchwartz B g hB hg hn c (a j) (hs j) n j
    let V (n : ℕ) (j : JetSlot) := transportedHalfDensitySchwartz c d K hK hKU (U n j)
      ((fixedVolumeGradientSchwartz_tsupport B g hB hg hn c (a j) (hs j) n j).trans (hS j))
    Tendsto (fun n => (fixedVolumeGradientSchwartz B g hB hg hn d η hηd n i).toLp 2 volume -
      ∑ j : JetSlot, (V n j).toLp 2 volume) atTop (𝓝 0) := by
  intro hs U V
  let v (n : ℕ) : SchwartzMap E ℂ := ∑ j : JetSlot, V n j
  have hSum (n : ℕ) (x : E) : v n x = ∑ j : JetSlot, V n j x :=
    map_sum (SchwartzMap.delta ℂ ℂ x) (V n) Finset.univ
  have hImg : IsCompact ((c.transition d) '' K) :=
    hK.image_of_continuousOn ((c.transition d).continuousOn.mono hKU)
  have hv (n : ℕ) : tsupport (v n : E → ℂ) ⊆ (c.transition d) '' K := by
    apply closure_minimal _ hImg.isClosed
    intro y hy
    by_contra hout
    exact hy (by
      rw [hSum]
      apply Finset.sum_eq_zero
      intro j _
      change transportedHalfDensity c d K (U n j) y = 0
      simp only [transportedHalfDensity, indicator_of_notMem hout])
  have hV (n : ℕ) (x : E) (hx : x ∈ K) : v n (c.transition d x) =
      (Real.sqrt |(fderiv ℝ (c.transition d) x).det|)⁻¹ • (∑ j, U n j x) := by
    have hProd := overlapJacobianWeight_inverse_mul c d (hKU hx)
    rw [overlapJacobianWeight_eq c d (hKU hx)] at hProd
    have hPos : 0 < Real.sqrt |(fderiv ℝ (c.transition d) x).det| :=
      Real.sqrt_pos.2 (abs_pos.2 (chartDerivative_det_ne_zero c d x (hKU hx)))
    have hW : overlapJacobianWeight d c (c.transition d x) =
        (Real.sqrt |(fderiv ℝ (c.transition d) x).det|)⁻¹ := by
      rw [← one_div]
      exact (eq_div_iff hPos.ne').2 ((mul_comm _ _).trans hProd)
    rw [hSum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change transportedHalfDensity c d K (U n j) (c.transition d x) = _
    rw [transportedHalfDensity, indicator_of_mem (mem_image_of_mem _ hx),
      overlapTransition_reverse_apply c d (hKU hx), hW]
  have hErr := fixedVolumeGradient_sub_transportedSourceSum_tendsto_zero r B g hB hg hn hconv c d K hK hKU
    η hη hηd i a hs ha v hv hV
  let toL := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)
  have hToL (n : ℕ) : (v n).toLp 2 volume = ∑ j, (V n j).toLp 2 volume :=
    map_sum toL (V n) Finset.univ
  simpa only [hToL] using hErr

end Burnett.Microlocal.AtlasVolumeGradient
