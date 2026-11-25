import Burnett.Analysis.Microlocal.Overlap.RawFirstOrderIntrinsicSymbol
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-! Compactly supported tests suffice to read back the actual first-order symbol. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 5200000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function Set Burnett.Geometry
open ConnectionDifference ManifoldMetric MaximalChart
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped BigOperators ContDiff Manifold Topology

local notation "E" => CoordinateSpace

theorem receivingRawFirstOrderRow_congr_of_eventuallyEq
    {J L : Type*} [Fintype J] [Fintype L]
    (a : J → E → ℝ) (v : J → E) (i : J → JetSlot)
    (b : L → E → ℝ) (j : L → JetSlot) {u w : JetSlot → E → ℂ} {x : E}
    (h : ∀ k, u k =ᶠ[𝓝 x] w k) :
    receivingRawFirstOrderRow a v i b j u x = receivingRawFirstOrderRow a v i b j w x := by
  unfold receivingRawFirstOrderRow
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro k _
    rw [(h (i k)).fderiv_eq]
  · apply Finset.sum_congr rfl
    intro k _
    rw [(h (j k)).eq_of_nhds]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

omit [IsManifold Model ∞ M] in
/-- Compatibility of the actual local first-order action on compact smooth
tests in the overlap implies compatibility on the smooth test germs. -/
theorem hasCompatibleRawFirstOrderActions_of_compactChartTests
    {Rows J L : Type} [Fintype J] [Fintype L]
    {Y : M → Type} [∀ x, AddCommGroup (Y x)] [∀ x, Module ℂ (Y x)]
    (coordinates : ∀ (c : AtlasChart M) (x : M), x ∈ c.chart.source → Y x ≃ₗ[ℂ] (Rows → ℂ))
    (a : AtlasChart M → Rows → J → E → ℝ) (v : AtlasChart M → Rows → J → E)
    (i : AtlasChart M → Rows → J → JetSlot)
    (b : AtlasChart M → Rows → L → E → ℝ) (j : AtlasChart M → Rows → L → JetSlot)
    (hCompact : ∀ (c d : AtlasChart M) (x : M) (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source)
      (u : JetSlot → E → ℂ),
      (∀ k, ContDiff ℝ ∞ (u k) ∧ HasCompactSupport (u k) ∧ tsupport (u k) ⊆ (c.transition d).target) →
      (fun s => receivingRawFirstOrderRow (a c s) (v c s) (i c s) (b c s) (j c s)
        (fun k y => rawReceivingJetTransition c d y (fun l => u l (c.transition d y)) k) (c.chart x)) =
        ((coordinates d x hd).symm.trans (coordinates c x hc))
          (fun s => receivingRawFirstOrderRow (a d s) (v d s) (i d s) (b d s) (j d s) u (d.chart x))) :
    HasCompatibleRawFirstOrderActions coordinates a v i b j := by
  intro c d x hc hd u hu
  let e := c.transition d
  have heSource : c.chart x ∈ e.source := by
    refine ⟨c.chart.mapsTo hc, ?_⟩
    change c.chart.symm (c.chart x) ∈ d.chart.source
    rwa [c.chart.left_inv hc]
  have heEq : e (c.chart x) = d.chart x := by
    change d.chart (c.chart.symm (c.chart x)) = d.chart x
    rw [c.chart.left_inv hc]
  have heTarget : d.chart x ∈ e.target := heEq ▸ e.mapsTo heSource
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds heTarget)
  let β : ContDiffBump (d.chart x) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hβ : tsupport (β : E → ℝ) ⊆ e.target := by
    rw [β.tsupport_eq]
    exact (Metric.closedBall_subset_ball (half_lt_self hε)).trans hBall
  let w (k : JetSlot) (y : E) : ℂ := (β y : ℂ) * u k y
  have hw (k : JetSlot) : ContDiff ℝ ∞ (w k) ∧ HasCompactSupport (w k) ∧ tsupport (w k) ⊆ e.target := by
    have hSupp : tsupport (w k) ⊆ tsupport (β : E → ℝ) := by
      apply closure_mono
      intro y hy
      by_contra h
      exact hy (by simp [w, notMem_support.mp h])
    exact ⟨(Complex.ofRealCLM.contDiff.comp β.contDiff).mul (hu k),
      β.hasCompactSupport.of_isClosed_subset isClosed_closure hSupp, hSupp.trans hβ⟩
  have hRight (k : JetSlot) : w k =ᶠ[𝓝 (d.chart x)] u k := by
    filter_upwards [β.eventuallyEq_one] with y hy
    change β y = 1 at hy
    simp [w, hy]
  have heCont : Tendsto e (𝓝 (c.chart x)) (𝓝 (d.chart x)) := by
    rw [← heEq]
    exact (e.continuousOn.continuousAt (e.open_source.mem_nhds heSource)).tendsto
  have hLeft (k : JetSlot) : (fun y => rawReceivingJetTransition c d y (fun l => w l (e y)) k) =ᶠ[𝓝 (c.chart x)]
      (fun y => rawReceivingJetTransition c d y (fun l => u l (e y)) k) := by
    filter_upwards [heCont.eventually (eventually_all.mpr hRight)] with y hy
    exact congrArg (fun z => rawReceivingJetTransition c d y z k) (funext hy)
  have h := hCompact c d x hc hd w hw
  have hl :
      (fun s => receivingRawFirstOrderRow (a c s) (v c s) (i c s) (b c s) (j c s)
        (fun k y => rawReceivingJetTransition c d y (fun l => w l (e y)) k) (c.chart x)) =
      fun s => receivingRawFirstOrderRow (a c s) (v c s) (i c s) (b c s) (j c s)
        (fun k y => rawReceivingJetTransition c d y (fun l => u l (e y)) k) (c.chart x) :=
    funext (fun s => receivingRawFirstOrderRow_congr_of_eventuallyEq _ _ _ _ _ hLeft)
  have hr :
      (fun s => receivingRawFirstOrderRow (a d s) (v d s) (i d s) (b d s) (j d s) w (d.chart x)) =
      fun s => receivingRawFirstOrderRow (a d s) (v d s) (i d s) (b d s) (j d s) u (d.chart x) :=
    funext (fun s => receivingRawFirstOrderRow_congr_of_eventuallyEq _ _ _ _ _ hRight)
  exact hl.symm.trans (h.trans (congrArg _ hr))

end Burnett.Microlocal.Overlap
