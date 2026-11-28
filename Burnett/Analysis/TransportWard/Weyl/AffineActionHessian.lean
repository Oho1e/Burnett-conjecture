import Burnett.Analysis.TransportWard.Weyl.EulerActionIntegral

/-! The Hessian of the actual first-order `ΓΓ` density, evaluated on the complete
lower metric and first-jet directions. -/

set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V03.Palatini

open Filter Set Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

open private coordinateMetricFirstJet_line contDiffOn_coordinateMetricFirstJet from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet
open private hasDerivAt_comp_fieldSegment from Burnett.Analysis.FrozenTransport.V03SegmentTaylor

local notation "E" => CoordinateSpace

private abbrev ActionState (ι : Type*) := Mat × (ActionSlot ι → ℝ)

private def actionState {ι : Type*} [Fintype ι] (S : ι → Mat) (g : E → ι → ℝ) (x : E) :
    ActionState ι :=
  (assembleMetricComponents S (g x), coordinateMetricFirstJet g x)

private def actionStateDomain {ι : Type*} : Set (ActionState ι) :=
  Prod.fst ⁻¹' nonsingularMetricDomain

private theorem isOpen_actionStateDomain {ι : Type*} [Fintype ι] :
    IsOpen (actionStateDomain : Set (ActionState ι)) :=
  isOpen_nonsingularMetricDomain.preimage continuous_fst

private def actionDensityOnState {ι : Type*} [Fintype ι] (S : ι → Mat) (z : ActionState ι) : ℝ :=
  metricActionDensity z.1 (metricJetOfComponents S z.2)

private theorem contDiffOn_actionDensityOnState {ι : Type*} [Fintype ι] (S : ι → Mat) :
    ContDiffOn ℝ ∞ (actionDensityOnState S) actionStateDomain := by
  have hC (s t : ActionSlot ι) :
      ContDiffOn ℝ ∞ (fun z : ActionState ι => metricActionCoefficient S s t z.1) actionStateDomain :=
    (contDiffOn_metricActionCoefficient S s t).comp contDiff_fst.contDiffOn (fun _ hz => hz)
  have hp (s : ActionSlot ι) : ContDiff ℝ ∞ (fun z : ActionState ι => z.2 s) :=
    (contDiff_apply ℝ ℝ s).comp contDiff_snd
  change ContDiffOn ℝ ∞ (fun z : ActionState ι => metricActionDensity z.1 (metricJetOfComponents S z.2))
    actionStateDomain
  simp only [metricActionDensity_eq_coefficient_sum]
  exact contDiffOn_const.mul (ContDiffOn.sum fun s _ =>
    ContDiffOn.sum fun t _ => ((hC s t).mul (hp s).contDiffOn).mul (hp t).contDiffOn)

private theorem contDiffOn_actionState {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g : E → ι → ℝ) {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (actionState S g) U :=
  ((assembleMetricComponents S).contDiff.comp_contDiffOn hg).prodMk
    (contDiffOn_pi.mpr fun s => contDiffOn_coordinateMetricFirstJet hU g hg s)

private theorem actionState_affine {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h : E → ι → ℝ) (x : E) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) (t : ℝ) :
    actionState S (fun y => g y + t • h y) x =
      fieldSegment (actionState S g x) (actionState S h x) t := by
  apply Prod.ext
  · change assembleMetricComponents S (g x + t • h x) =
      assembleMetricComponents S (g x) + t • assembleMetricComponents S (h x)
    simp only [map_add, map_smul]
  · exact coordinateMetricFirstJet_line g h x t hg hh

private theorem actionDensityOnState_eq_coordinateDensity {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g : E → ι → ℝ) (x : E) (hg : DifferentiableAt ℝ g x) :
    actionDensityOnState S (actionState S g x) =
      metricActionDensity (assembledCoordinateMetric S g x) (coordinateJet (assembledCoordinateMetric S g) x) := by
  rw [coordinateJet_assembledCoordinateMetric S g x hg]
  rfl

private theorem coordinateWeakActionVariation_eq_stateDerivative {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g h : E → ι → ℝ) (x : E) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) (hn : Matrix.det (assembleMetricComponents S (g x)) ≠ 0) :
    coordinateWeakActionVariation S g h x =
      fderiv ℝ (actionDensityOnState S) (actionState S g x) (actionState S h x) := by
  let z := actionState S g x
  let v := actionState S h x
  have h0 : fieldSegment z v 0 ∈ actionStateDomain := by
    simpa only [fieldSegment, zero_smul, add_zero] using (show z ∈ actionStateDomain from hn)
  have hd := hasDerivAt_comp_fieldSegment (actionDensityOnState S) isOpen_actionStateDomain
    (contDiffOn_actionDensityOnState S) z v 0 h0
  have hEq : (fun u =>
      let k := metricAffineVariation (assembledCoordinateMetric S g) (assembledCoordinateMetric S h) u
      metricActionDensity (k x) (coordinateJet k x)) =
      (fun u => actionDensityOnState S (fieldSegment z v u)) := by
    funext u
    have hAffine : metricAffineVariation (assembledCoordinateMetric S g) (assembledCoordinateMetric S h) u =
        assembledCoordinateMetric S (fun y => g y + u • h y) := by
      funext y
      simp only [metricAffineVariation, assembledCoordinateMetric, map_add, map_smul]
    have hu : DifferentiableAt ℝ (fun y => g y + u • h y) x :=
      hg.add (hh.fun_const_smul u)
    change metricActionDensity ((metricAffineVariation (assembledCoordinateMetric S g)
      (assembledCoordinateMetric S h) u) x)
        (coordinateJet (metricAffineVariation (assembledCoordinateMetric S g)
          (assembledCoordinateMetric S h) u) x) = _
    rw [hAffine, ← actionDensityOnState_eq_coordinateDensity S _ x hu,
      actionState_affine S g h x hg hh]
  have h := hasDerivAt_metricActionDensity_assembledAffineVariation S g h x hg hh hn
  rw [hEq] at h
  exact h.unique (by simpa only [fieldSegment, zero_smul, add_zero] using hd)

/-- The full second variation of the actual density, in the directions of both
lower metric variations and both actual first variations of their spatial jets. -/
def coordinateActionHessianDensity {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g h k : E → ι → ℝ) (x : E) : ℝ :=
  secondFDeriv (actionDensityOnState S) (actionState S g x) (actionState S h x) (actionState S k x)

theorem contDiffOn_coordinateActionHessianDensity {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h k : E → ι → ℝ) {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0) :
    ContDiffOn ℝ ∞ (coordinateActionHessianDensity S g h k) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (actionDensityOnState S)) actionStateDomain :=
    (contDiffOn_actionDensityOnState S).fderiv_of_isOpen isOpen_actionStateDomain (by simp)
  have hD2 : ContDiffOn ℝ ∞ (secondFDeriv (actionDensityOnState S)) actionStateDomain :=
    hD.fderiv_of_isOpen isOpen_actionStateDomain (by simp)
  have hc := hD2.comp (contDiffOn_actionState S g hU hg) hn
  exact (hc.clm_apply (contDiffOn_actionState S h hU hh)).clm_apply (contDiffOn_actionState S k hU hk)

theorem coordinateActionHessianDensity_swap {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g h k : E → ι → ℝ) (x : E)
    (hn : Matrix.det (assembleMetricComponents S (g x)) ≠ 0) :
    coordinateActionHessianDensity S g h k x = coordinateActionHessianDensity S g k h x := by
  have hd := (contDiffOn_actionDensityOnState S).contDiffAt
    (isOpen_actionStateDomain.mem_nhds (show actionState S g x ∈ actionStateDomain from hn))
  have hSym := hd.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  exact hSym (actionState S h x) (actionState S k x)

theorem hasDerivAt_coordinateWeakActionVariation {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g h k : E → ι → ℝ) (x : E)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (hk : DifferentiableAt ℝ k x)
    (hn : Matrix.det (assembleMetricComponents S (g x)) ≠ 0) :
    HasDerivAt (fun t : ℝ => coordinateWeakActionVariation S (fun y => g y + t • h y) k x)
      (coordinateActionHessianDensity S g h k x) 0 := by
  let z := actionState S g x
  let v := actionState S h x
  let w := actionState S k x
  have h0 : fieldSegment z v 0 ∈ actionStateDomain := by
    simpa only [fieldSegment, zero_smul, add_zero] using (show z ∈ actionStateDomain from hn)
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (actionDensityOnState S)) actionStateDomain :=
    (contDiffOn_actionDensityOnState S).fderiv_of_isOpen isOpen_actionStateDomain (by simp)
  have hd : HasDerivAt (fun t => fderiv ℝ (actionDensityOnState S) (fieldSegment z v t) w)
      (coordinateActionHessianDensity S g h k x) 0 := by
    simpa only [coordinateActionHessianDensity, z, v, w, ContinuousLinearMap.apply_apply,
      Function.comp_apply, fieldSegment, zero_smul, add_zero] using
      ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp_hasDerivAt 0
        (hasDerivAt_comp_fieldSegment (fderiv ℝ (actionDensityOnState S))
          isOpen_actionStateDomain hD z v 0 h0))
  apply hd.congr_of_eventuallyEq
  have hLine : Continuous (fieldSegment z v) := continuous_const.add (continuous_id.smul continuous_const)
  filter_upwards [(isOpen_actionStateDomain.preimage hLine).mem_nhds h0] with t ht
  have hAff := actionState_affine S g h x hg hh t
  have ht' : actionState S (fun y => g y + t • h y) x ∈ actionStateDomain := by
    rw [hAff]
    exact ht
  rw [coordinateWeakActionVariation_eq_stateDerivative S (fun y => g y + t • h y) k x
    (hg.add (hh.fun_const_smul t)) hk ht', hAff]

end Burnett.V03.Palatini
