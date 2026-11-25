import Burnett.Analysis.Microlocal.Overlap.SymmetricJetRawChartSections
import Burnett.Analysis.Microlocal.Overlap.RawFirstOrderProjectedRows

/-! Read chart compatibility from one first-order action on actual compact sections. -/
set_option autoImplicit false
set_option maxRecDepth 4400
set_option maxHeartbeats 6100000
set_option synthInstance.maxHeartbeats 360000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped BigOperators ContDiff Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

private theorem rawReceivingJetTransition_differentiableAt_apply
    (c d : AtlasChart M) (x : E) (hx : x ∈ (c.transition d).source)
    (w : E → JetSlot → ℂ) (hw : ∀ i, DifferentiableAt ℝ (fun y => w y i) x) (k : JetSlot) :
    DifferentiableAt ℝ (fun y => rawReceivingJetTransition c d y (w y) k) x := by
  let basisEntry (i : JetSlot) : JetSlot → ℂ := Pi.single i 1
  have hW (y : E) : w y = ∑ i : JetSlot, w y i • basisEntry i := by
    calc
      w y = ∑ i : JetSlot, Pi.single i (w y i) := (LinearMap.sum_single_apply _ (w y)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        change Pi.single i (w y i) = w y i • (Pi.single i (1 : ℂ) : JetSlot → ℂ)
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hApply : (fun y => rawReceivingJetTransition c d y (w y) k) =
      (fun y => ∑ i : JetSlot, w y i * rawReceivingJetTransition c d y (basisEntry i) k) := by
    funext y
    conv_lhs => rw [hW y]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hApply]
  exact DifferentiableAt.fun_sum fun i _ =>
    (hw i).mul (rawReceivingJetTransition_differentiableAt c d x hx (basisEntry i) k)

variable [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M]

/-- The actual action on smooth compact symmetric sections yields compatible
local rows on the ordered coordinates after composition with the canonical
projection. Compact test sections are lifted inside the actual chart overlap. -/
theorem hasCompatibleRawFirstOrderActions_of_actualSymmetricSectionAction
    {Rows J L : Type} [Fintype J] [Fintype L]
    {Y : M → Type} [∀ x, AddCommGroup (Y x)] [∀ x, Module ℂ (Y x)]
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (A : smoothCompactSymmetricJet M →ₗ[ℂ] (∀ x : M, Y x))
    (coordinates : ∀ (c : AtlasChart M) (x : M), x ∈ c.chart.source → Y x ≃ₗ[ℂ] (Rows → ℂ))
    (a : AtlasChart M → Rows → J → E → ℝ) (v : AtlasChart M → Rows → J → E)
    (i : AtlasChart M → Rows → J → JetSlot)
    (b : AtlasChart M → Rows → L → E → ℝ) (j : AtlasChart M → Rows → L → JetSlot)
    (hRepresentation : ∀ (c : AtlasChart M) (x : M) (hc : x ∈ c.chart.source)
      (s : smoothCompactSymmetricJet M),
      coordinates c x hc (A s x) =
        fun r => receivingRawFirstOrderRow (a c r) (v c r) (i c r) (b c r) (j c r)
          (fun k y => symmetricJetComponent c s k (c.chart.symm y)) (c.chart x)) :
    HasCompatibleRawFirstOrderActions coordinates
      (fun c r h y => a c r h.1 y / 2) (fun c r h => v c r h.1) (fun c r => projectedRowSlot (i c r))
      (fun c r h y => b c r h.1 y / 2) (fun c r => projectedRowSlot (j c r)) := by
  apply hasCompatibleRawFirstOrderActions_of_compactChartTests
  intro c d x hc hd u hu
  let e := c.transition d
  have hx : c.chart x ∈ e.source := by
    refine ⟨c.chart.mapsTo hc, ?_⟩
    change c.chart.symm (c.chart x) ∈ d.chart.source
    rwa [c.chart.left_inv hc]
  let K := ⋃ k, tsupport (u k)
  have hK : IsCompact K := isCompact_iUnion (fun k => (hu k).2.1)
  have hKd : K ⊆ d.chart.target := by
    intro y hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    exact ((hu k).2.2 hk).1
  have hSupport (k : JetSlot) : support (u k) ⊆ K := by
    exact (subset_tsupport (u k)).trans (subset_iUnion (fun l : JetSlot => tsupport (u l)) k)
  have hU (k : JetSlot) : ContDiff ℝ ∞ (u k) := (hu k).1
  obtain ⟨s, hRight, hLeft⟩ := exists_compactSymmetricJet_rawChartTest B hB hn d u hU K hK hKd hSupport
  let transport (k : JetSlot) (y : E) := rawReceivingJetTransition c d y (fun l => u l (e y)) k
  have heDiff : DifferentiableAt ℝ e (c.chart x) :=
    ((c.smooth_transition d).contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hTransport (k : JetSlot) : DifferentiableAt ℝ (transport k) (c.chart x) :=
    rawReceivingJetTransition_differentiableAt_apply c d (c.chart x) hx (fun y l => u l (e y))
      (fun l => (((hU l).contDiffAt).differentiableAt (by simp)).comp _ heDiff) k
  have hC (k : JetSlot) :
      (fun y => symmetrizeOrderedJet (fun l => transport l y) k) =ᶠ[𝓝 (c.chart x)]
        (fun y => symmetricJetComponent c s k (c.chart.symm y)) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    rw [hLeft c y hy]
    exact congrFun (rawReceivingJetTransition_symmetrizeOrderedJet_on_overlap c d hy (fun l => u l (e y))).symm k
  have hD (k : JetSlot) : (fun y => symmetrizeOrderedJet (fun l => u l y) k) =ᶠ[𝓝 (d.chart x)]
      (fun y => symmetricJetComponent d s k (d.chart.symm y)) := by
    filter_upwards [d.chart.open_target.mem_nhds (d.chart.mapsTo hd)] with y hy
    exact (hRight y hy k).symm
  have hExpress (r : Rows) :
      receivingRawFirstOrderRow (fun h y => a c r h.1 y / 2) (fun h => v c r h.1) (projectedRowSlot (i c r))
          (fun h y => b c r h.1 y / 2) (projectedRowSlot (j c r)) transport (c.chart x) =
        coordinates c x hc (A s x) r := by
    rw [receivingRawFirstOrderRow_projected _ _ _ _ _ _ _ hTransport, hRepresentation c x hc s]
    exact receivingRawFirstOrderRow_congr_of_eventuallyEq _ _ _ _ _ hC
  have hExpressRight (r : Rows) :
      receivingRawFirstOrderRow (fun h y => a d r h.1 y / 2) (fun h => v d r h.1) (projectedRowSlot (i d r))
          (fun h y => b d r h.1 y / 2) (projectedRowSlot (j d r)) u (d.chart x) =
        coordinates d x hd (A s x) r := by
    rw [receivingRawFirstOrderRow_projected _ _ _ _ _ _ _
        (fun k => ((hU k).contDiffAt).differentiableAt (by simp)),
      hRepresentation d x hd s]
    exact receivingRawFirstOrderRow_congr_of_eventuallyEq _ _ _ _ _ hD
  change (fun r => receivingRawFirstOrderRow _ _ _ _ _ transport (c.chart x)) = _
  rw [funext hExpress, funext hExpressRight]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

end Burnett.Microlocal.Overlap
