import Burnett.Analysis.Microlocal.Overlap.RawFirstOrderSymbolChange
import Burnett.Analysis.Microlocal.Overlap.UnweightedReceivingFirstOrderRange
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartGeometricBridge

/-! Intrinsic cotangent coordinates for the principal row extracted from a chart action. -/
set_option autoImplicit false
set_option maxRecDepth 4200
set_option maxHeartbeats 4400000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Matrix Burnett.Geometry
open ConnectionDifference ManifoldMetric MaximalChart
open Burnett.Geometry.FixedCotangentChart (fixedCovector inverseFrame inverseFrame_change)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.UnitNullCompactness (covectorCLM)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped BigOperators ContDiff InnerProduct Manifold Matrix Topology

open private inner_eq_covectorCLM from Burnett.Analysis.Microlocal.Overlap.ReceivingChartGeometricBridge
open private covectorCLM_basis_values from Burnett.Geometry.Cotangent.FixedChartNaturality
open private sum_groupRow_mul from Burnett.Analysis.Microlocal.RowKernelDensity

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The grouped matrix symbol evaluated on an ordered jet is the principal
row evaluated by the actual covector of the same cosphere point. -/
theorem receivingRawFirstOrderSymbol_mulVec_fixedCovector
    {r : Metric (M := M)} {Rows J : Type} [Fintype J] (c : AtlasChart M) (p : Cosphere r)
    (hp : projection p ∈ c.chart.source)
    (a : Rows → J → E → ℝ) (v : Rows → J → E) (i : Rows → J → JetSlot) (w : JetSlot → ℂ) :
    (fun s : Rows => receivingRawFirstOrderSymbol c (a s) (v s) (i s) p) *ᵥ w =
      fun s => rawFirstOrderPrincipalEvaluation (a s) (v s) (i s) (c.chart (projection p))
        (fixedCovector c p.val) w := by
  have hξ : covectorCLM (atlasChartUnitCovector c p) = fixedCovector c p.val := by
    have h : atlasChartUnitCovector c p = fun j => fixedCovector c p.val (coordinateBasis j) :=
      funext (atlasChartUnitCovector_of_mem c p hp)
    rw [h, covectorCLM_basis_values]
  funext s
  simp only [Matrix.mulVec, dotProduct, receivingRawFirstOrderSymbol, sum_groupRow_mul,
    rawFirstOrderPrincipalEvaluation, inner_eq_covectorCLM]
  change (∑ h, (a s h (c.chart (projection p)) : ℂ) *
    (covectorCLM (atlasChartUnitCovector c p) (v s h) : ℂ) * w (i s h)) = _
  rw [hξ]

/-- The actual compatibility of the first-order action on the overlap
implies its principal symbol change at the same unit cotangent point. -/
theorem receivingRawFirstOrderSymbol_mulVec_change_of_chart_action
    {r : Metric (M := M)} {RowsC RowsD Jc Jd Lc Ld : Type}
    [Fintype Jc] [Fintype Jd] [Fintype Lc] [Fintype Ld]
    (c d : AtlasChart M) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) (hd : projection p ∈ d.chart.source)
    (ac : RowsC → Jc → E → ℝ) (vc : RowsC → Jc → E) (ic : RowsC → Jc → JetSlot)
    (bc : RowsC → Lc → E → ℝ) (jc : RowsC → Lc → JetSlot)
    (ad : RowsD → Jd → E → ℝ) (vd : RowsD → Jd → E) (id : RowsD → Jd → JetSlot)
    (bd : RowsD → Ld → E → ℝ) (jd : RowsD → Ld → JetSlot)
    (inputChange : E → (JetSlot → ℂ) →ₗ[ℂ] (JetSlot → ℂ))
    (outputChange : (RowsD → ℂ) →ₗ[ℂ] (RowsC → ℂ))
    (hInput : ∀ w k, DifferentiableAt ℝ (fun y => inputChange y w k) (c.chart (projection p)))
    (hActual : ∀ u : JetSlot → E → ℂ, (∀ k, ContDiff ℝ ∞ (u k)) →
      (fun s => receivingRawFirstOrderRow (ac s) (vc s) (ic s) (bc s) (jc s)
        (fun k y => inputChange y (fun l => u l (c.transition d y)) k) (c.chart (projection p))) =
      outputChange (fun s => receivingRawFirstOrderRow (ad s) (vd s) (id s) (bd s) (jd s) u
        (d.chart (projection p))))
    (w : JetSlot → ℂ) :
    (fun s : RowsC => receivingRawFirstOrderSymbol c (ac s) (vc s) (ic s) p) *ᵥ
        inputChange (c.chart (projection p)) w =
      outputChange ((fun s : RowsD => receivingRawFirstOrderSymbol d (ad s) (vd s) (id s) p) *ᵥ w) := by
  let x := projection p
  have hSource : c.chart x ∈ (c.transition d).source := by
    refine ⟨c.chart.mapsTo hc, ?_⟩
    change c.chart.symm (c.chart x) ∈ d.chart.source
    rwa [c.chart.left_inv hc]
  have hTransition : c.transition d (c.chart x) = d.chart x := by
    change d.chart (c.chart.symm (c.chart x)) = d.chart x
    rw [c.chart.left_inv hc]
  have hDifferentiable : DifferentiableAt ℝ (c.transition d) (c.chart x) :=
    ((c.smooth_transition d).contDiffAt ((c.transition d).open_source.mem_nhds hSource)).differentiableAt
      (by simp)
  have hCotangent : fixedCovector c p.val = (fixedCovector d p.val).comp (fderiv ℝ (c.transition d) (c.chart x)) := by
    change p.val.2.comp (inverseFrame c x) =
      (p.val.2.comp (inverseFrame d x)).comp (fderiv ℝ (c.transition d) (c.chart x))
    rw [inverseFrame_change d c x hd hc, ContinuousLinearMap.comp_assoc]
  have hAction : ∀ u : JetSlot → E → ℂ, (∀ k, ContDiff ℝ ∞ (u k)) →
      (fun s => receivingRawFirstOrderRow (ac s) (vc s) (ic s) (bc s) (jc s)
        (fun k y => inputChange y (fun l => u l (c.transition d y)) k) (c.chart x)) =
      outputChange (fun s => receivingRawFirstOrderRow (ad s) (vd s) (id s) (bd s) (jd s) u
        (c.transition d (c.chart x))) := by
    intro u hu
    rw [hTransition]
    exact hActual u hu
  have h := rawFirstOrderPrincipal_change_of_actual_chart_action ac vc ic bc jc ad vd id bd jd
    (c.chart x) (c.transition d) _ hDifferentiable.hasFDerivAt inputChange outputChange hInput hAction
    (fixedCovector d p.val) w
  rw [hTransition, ← hCotangent] at h
  rw [receivingRawFirstOrderSymbol_mulVec_fixedCovector c p hc, receivingRawFirstOrderSymbol_mulVec_fixedCovector d p hd]
  exact h

end Burnett.Microlocal.Overlap
