import Burnett.Analysis.Microlocal.ActualChartAuxiliarySection
import Burnett.Analysis.Microlocal.Overlap.KernelGeometry
import Burnett.Geometry.ActualChartSecondJet
import Burnett.Geometry.Cotangent.ChartTransition

/-!
# The auxiliary unit covector on a chart overlap

The chart change acts on the round section by the cotangent Jacobian
followed by round normalization. Both chart descriptions have the same
auxiliary unit representative in the actual cotangent bundle.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.OverlapCovectors

open Set Matrix
open Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.ActualChartSecondJet (contDiffOn_chartTransition_infty)
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.InverseField (matrixInverse)
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.UnitNullCompactness
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.Microlocal.CountableAuxiliaryCharts Burnett.Microlocal.FixedChartGeometricDensity
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.OverlapGradient (overlapTransition overlapTransition_eq overlapTransition_measurable)
open Burnett.Microlocal.SmoothAngularTests (sphereCoordinate sphereCoordinate_apply)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open scoped BigOperators ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem auxiliaryUnitCovector_pos_smul (A : Tensor2) (ξ : Covector) (a : ℝ) (ha : 0 < a) :
    auxiliaryUnitCovector A (a • ξ) = auxiliaryUnitCovector A ξ := by
  have h := symbolNorm_rescale A ξ a
  change symbolNorm A (a • ξ) = a ^ 2 * symbolNorm A ξ at h
  funext i
  simp only [auxiliaryUnitCovector, auxiliaryScale, h, Real.sqrt_mul (sq_nonneg a),
    Real.sqrt_sq ha.le, Pi.smul_apply, smul_eq_mul, mul_inv]
  calc
    (a⁻¹ * (Real.sqrt (symbolNorm A ξ))⁻¹) * (a * ξ i) =
        (a⁻¹ * a) * ((Real.sqrt (symbolNorm A ξ))⁻¹ * ξ i) := by ring
    _ = _ := by rw [inv_mul_cancel₀ ha.ne', one_mul]

/-- Positive rescaling of the transported covector yields the same auxiliary unit ray. -/
theorem chartAuxiliaryRay_eq_of_cotangent_transition
    (r : ManifoldMetric.Metric (M := M)) (q d : CompactChartInput M)
    (p : Chart q.ball) (p' : Chart d.ball)
    (hbase : (chartAt CoordinateSpace d.center).symm p'.1 =
      (chartAt CoordinateSpace q.center).symm p.1)
    (a : ℝ) (ha : 0 < a)
    (hξ : roundCovector p' = a • (cotangentTransitionMatrix q.center d.center
      ((chartAt CoordinateSpace q.center).symm p.1) *ᵥ roundCovector p)) :
    chartAuxiliaryRay r d p' = chartAuxiliaryRay r q p := by
  let e := chartAt CoordinateSpace q.center
  let f := chartAt CoordinateSpace d.center
  let m := e.symm p.1
  have hc : m ∈ e.source := e.symm_mapsTo (q.ball_in_chart p.1.property)
  have hd : m ∈ f.source := by
    change e.symm p.1 ∈ f.source
    rw [← hbase]
    exact f.symm_mapsTo (d.ball_in_chart p'.1.property)
  have he : e m = p.1 := e.right_inv (q.ball_in_chart p.1.property)
  have hf : f m = p'.1 := by
    change f (e.symm p.1) = p'.1
    rw [← hbase]
    exact f.right_inv (d.ball_in_chart p'.1.property)
  let T := cotangentTransitionMatrix q.center d.center m
  have hNorm : symbolNorm (chartAuxiliaryInverse r d p'.1) (T *ᵥ roundCovector p) =
      symbolNorm (chartAuxiliaryInverse r q p.1) (roundCovector p) := by
    have h := symbolNorm_cotangentTransitionMatrix r.inner
      (GlobalLeviCivita.inner_nondegenerate r) r.symm q.center d.center m hc hd (roundCovector p)
    change symbolNorm (matrixInverse (metricComponents (ManifoldMetric.coordinateMetric r d.center) (f m)))
        (T *ᵥ roundCovector p) =
      symbolNorm (matrixInverse (metricComponents (ManifoldMetric.coordinateMetric r q.center) (e m)))
        (roundCovector p) at h
    rw [hf, he] at h
    exact h
  change roundCovector p' = a • (T *ᵥ roundCovector p) at hξ
  have hAux : auxiliaryUnitCovector (chartAuxiliaryInverse r d p'.1) (roundCovector p') =
      T *ᵥ auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p) := by
    rw [hξ, auxiliaryUnitCovector_pos_smul _ _ _ ha]
    change auxiliaryScale (chartAuxiliaryInverse r d p'.1) (T *ᵥ roundCovector p) •
        (T *ᵥ roundCovector p) =
      T *ᵥ (auxiliaryScale (chartAuxiliaryInverse r q p.1) (roundCovector p) • roundCovector p)
    rw [Matrix.mulVec_smul, auxiliaryScale, auxiliaryScale, hNorm]
  change cotangentAssemble d.center (f.symm p'.1, _) = cotangentAssemble q.center (m, _)
  rw [show f.symm p'.1 = m from hbase, hAux]
  exact cotangentAssemble_change q.center d.center m hc hd _

/-- The phase points whose base belongs to both compact chart windows. -/
def roundOverlap (q d : CompactChartInput M) : Set (Chart q.ball) :=
  {p | (p.1 : CoordinateSpace) ∈ (chartTransition q.center d.center).source ∧
    chartTransition q.center d.center p.1 ∈ d.ball.closedBall}

omit [IsManifold Model ∞ M] in
theorem measurableSet_roundOverlap (q d : CompactChartInput M) :
    MeasurableSet (roundOverlap q d) := by
  let x (p : Chart q.ball) : CoordinateSpace := p.1
  let e := chartTransition q.center d.center
  have hx : Continuous x := continuous_subtype_val.comp continuous_fst
  have hA : MeasurableSet (x ⁻¹' e.source) :=
    e.open_source.measurableSet.preimage hx.measurable
  have hBall : IsClosed d.ball.closedBall := Metric.isClosed_closedBall
  have hB : MeasurableSet ((overlapTransition q.center d.center ∘ x) ⁻¹' d.ball.closedBall) :=
    hBall.measurableSet.preimage ((overlapTransition_measurable q.center d.center).comp hx.measurable)
  convert hA.inter hB using 1
  ext p
  simp only [roundOverlap, mem_setOf_eq, mem_inter_iff, mem_preimage, Function.comp_apply, x, e]
  exact and_congr_right fun h => by rw [overlapTransition_eq q.center d.center h]

omit [IsManifold Model ∞ M] in
private theorem chartTransition_reverse (c d : M) :
    (chartTransition c d).symm = chartTransition d c := by
  simp only [chartTransition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]

private theorem roundCovector_ne_zero {K : BallData}
    (p : Chart K) : roundCovector p ≠ 0 := by
  intro hz
  simpa only [hz, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_ne_one] using
    roundCovector_dual_pairing p

/-- The transported covector before restoring its round normalization. -/
def roundOverlapDirection (q d : CompactChartInput M) (p : roundOverlap q d) : CoordinateSpace :=
  WithLp.toLp 2 <| cotangentTransitionMatrix q.center d.center
    ((chartAt CoordinateSpace q.center).symm p.1.1) *ᵥ roundCovector p.1

theorem roundOverlapDirection_ne_zero (q d : CompactChartInput M) (p : roundOverlap q d) :
    roundOverlapDirection q d p ≠ 0 := by
  intro hz
  have h := cotangentTransitionMatrix_mulVec_ne_zero q.center d.center
    ((chartAt CoordinateSpace q.center).symm p.1.1)
    ((chartAt CoordinateSpace q.center).symm_mapsTo p.2.1.1) p.2.1.2
    (roundCovector_ne_zero p.1)
  apply h
  exact congrArg WithLp.ofLp hz

/-- On the overlap, apply the inverse-transpose Jacobian and restore round length one. -/
def roundOverlapTransition (q d : CompactChartInput M) (p : roundOverlap q d) :
    roundOverlap d q := by
  let e := chartTransition q.center d.center
  let v := roundOverlapDirection q d p
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr (roundOverlapDirection_ne_zero q d p)
  have hs : (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere (0 : CoordinateSpace) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv)]
    exact inv_mul_cancel₀ hv.ne'
  refine ⟨⟨⟨e p.1.1, p.2.2⟩, ⟨‖v‖⁻¹ • v, hs⟩⟩, ?_, ?_⟩
  · rw [← chartTransition_reverse q.center d.center]
    exact e.mapsTo p.2.1
  · rw [← chartTransition_reverse q.center d.center,
      e.left_inv p.2.1]
    exact p.1.1.property

theorem roundOverlapTransition_covector (q d : CompactChartInput M) (p : roundOverlap q d) :
    roundCovector (roundOverlapTransition q d p).1 =
      ((‖roundOverlapDirection q d p‖)⁻¹ : ℝ) •
        (cotangentTransitionMatrix q.center d.center ((chartAt CoordinateSpace q.center).symm p.1.1) *ᵥ
          roundCovector p.1) := rfl

theorem continuous_roundOverlapTransition (q d : CompactChartInput M) :
    Continuous (roundOverlapTransition q d) := by
  let e := chartTransition q.center d.center
  let f := chartTransition d.center q.center
  let x (p : roundOverlap q d) : CoordinateSpace := p.1.1
  have hx : Continuous x := (continuous_subtype_val.comp continuous_fst).comp continuous_subtype_val
  have hbase : Continuous (fun p => e (x p)) :=
    continuousOn_univ.mp (e.continuousOn.comp hx.continuousOn (fun p _ => p.2.1))
  have hSource (p : roundOverlap q d) : e (x p) ∈ f.source := by
    rw [show f = e.symm from (chartTransition_reverse q.center d.center).symm]
    exact e.mapsTo p.2.1
  have hDerivativeOn : ContDiffOn ℝ 0 (fderiv ℝ f) f.source :=
    (contDiffOn_chartTransition_infty d.center q.center).fderiv_of_isOpen f.open_source (by simp)
  have hDerivative : Continuous (fun p => fderiv ℝ f (e (x p))) :=
    continuousOn_univ.mp (hDerivativeOn.continuousOn.comp hbase.continuousOn (fun p _ => hSource p))
  have hT (i j : Index) : Continuous (fun p : roundOverlap q d =>
      cotangentTransitionMatrix q.center d.center ((chartAt CoordinateSpace q.center).symm p.1.1) i j) := by
    refine ((EuclideanSpace.proj j).continuous.comp (hDerivative.clm_apply
      (continuous_const (y := coordinateBasis i)))).congr fun p => ?_
    rw [cotangentTransitionMatrix, Matrix.transpose_apply, derivativeMatrix, LinearMap.toMatrix_apply]
    rfl
  have hξ (i : Index) : Continuous (fun p : roundOverlap q d => roundCovector p.1 i) :=
    ((sphereCoordinate i).continuous.comp (continuous_snd.comp continuous_subtype_val)).congr
      (fun p => sphereCoordinate_apply i p.1.2)
  have hv : Continuous (roundOverlapDirection q d) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Index => ℝ)).comp
    apply continuous_pi
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finset_sum _ fun j _ => (hT i j).mul (hξ j)
  have hangle : Continuous (fun p => (‖roundOverlapDirection q d p‖⁻¹ : ℝ) •
      roundOverlapDirection q d p) :=
    (hv.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (roundOverlapDirection_ne_zero q d p))).smul hv
  apply Continuous.subtype_mk
  exact hbase.subtype_mk _ |>.prodMk (hangle.subtype_mk _)

private theorem roundDirection_eq_of_pos_smul {K L : BallData} (p : Chart K) (p' : Chart L)
    (a : ℝ) (ha : 0 < a) (h : roundCovector p = a • roundCovector p') :
    (p.2 : CoordinateSpace) = (p'.2 : CoordinateSpace) := by
  have hSpace : (p.2 : CoordinateSpace) = a • (p'.2 : CoordinateSpace) :=
    WithLp.ofLp_injective 2 h
  have hp : ‖(p.2 : CoordinateSpace)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property
  have hp' : ‖(p'.2 : CoordinateSpace)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p'.2.property
  rw [hSpace, norm_smul, Real.norm_eq_abs, abs_of_pos ha, hp', mul_one] at hp
  simpa only [hp, one_smul] using hSpace

theorem roundOverlapTransition_leftInverse (q d : CompactChartInput M) :
    Function.LeftInverse (roundOverlapTransition d q) (roundOverlapTransition q d) := by
  intro p
  let p' := roundOverlapTransition q d p
  let p'' := roundOverlapTransition d q p'
  let m := (chartAt CoordinateSpace q.center).symm p.1.1
  have hBase : (p''.1.1 : CoordinateSpace) = p.1.1 := by
    change chartTransition d.center q.center (chartTransition q.center d.center p.1.1) = p.1.1
    rw [← chartTransition_reverse q.center d.center]
    exact (chartTransition q.center d.center).left_inv p.2.1
  have hm : (chartAt CoordinateSpace d.center).symm p'.1.1 = m :=
    chartTransition_symm_point q.center d.center p.2.1
  have hc : m ∈ (chartAt CoordinateSpace q.center).source :=
    (chartAt CoordinateSpace q.center).symm_mapsTo p.2.1.1
  have hd : m ∈ (chartAt CoordinateSpace d.center).source := p.2.1.2
  let a := (‖roundOverlapDirection q d p‖)⁻¹
  let b := (‖roundOverlapDirection d q p'‖)⁻¹
  have ha : 0 < a := inv_pos.mpr (norm_pos_iff.mpr (roundOverlapDirection_ne_zero q d p))
  have hb : 0 < b := inv_pos.mpr (norm_pos_iff.mpr (roundOverlapDirection_ne_zero d q p'))
  have hξ : roundCovector p'.1 = a • (cotangentTransitionMatrix q.center d.center m *ᵥ
      roundCovector p.1) := roundOverlapTransition_covector q d p
  have hη : roundCovector p''.1 = b • (cotangentTransitionMatrix d.center q.center
      ((chartAt CoordinateSpace d.center).symm p'.1.1) *ᵥ roundCovector p'.1) :=
    roundOverlapTransition_covector d q p'
  rw [hm, hξ, Matrix.mulVec_smul, cotangentTransitionMatrix_reverse_mulVec q.center d.center m hc hd,
    smul_smul] at hη
  exact Subtype.ext (Prod.ext (Subtype.ext hBase)
    (Subtype.ext (roundDirection_eq_of_pos_smul p''.1 p.1 (b * a) (mul_pos hb ha) hη)))

/-- The overlap change of base coordinates and round directions has its reverse as inverse. -/
def roundOverlapHomeomorph (q d : CompactChartInput M) : roundOverlap q d ≃ₜ roundOverlap d q where
  toFun := roundOverlapTransition q d
  invFun := roundOverlapTransition d q
  left_inv := roundOverlapTransition_leftInverse q d
  right_inv := roundOverlapTransition_leftInverse d q
  continuous_toFun := continuous_roundOverlapTransition q d
  continuous_invFun := continuous_roundOverlapTransition d q

theorem roundOverlapTransition_mem (q d e : CompactChartInput M) (p : roundOverlap q d)
    (hp : p.1 ∈ roundOverlap q e) :
    (roundOverlapTransition q d p).1 ∈ roundOverlap d e := by
  let x := (p.1.1 : CoordinateSpace)
  let y := chartTransition q.center d.center x
  have hm := chartTransition_symm_point q.center d.center p.2.1
  change y ∈ (chartTransition d.center e.center).source ∧
    chartTransition d.center e.center y ∈ e.ball.closedBall
  refine ⟨⟨((chartTransition q.center d.center).mapsTo p.2.1).1, ?_⟩, ?_⟩
  · change (chartAt CoordinateSpace d.center).symm y ∈ (chartAt CoordinateSpace e.center).source
    rw [hm]
    exact hp.1.2
  · change chartAt CoordinateSpace e.center ((chartAt CoordinateSpace d.center).symm y) ∈
      e.ball.closedBall
    rw [hm]
    exact hp.2

/-- Direct and successive round phase changes agree on a triple overlap. -/
theorem roundOverlapTransition_comp (q d e : CompactChartInput M) (p : roundOverlap q d)
    (hp : p.1 ∈ roundOverlap q e) :
    (roundOverlapTransition d e ⟨(roundOverlapTransition q d p).1,
      roundOverlapTransition_mem q d e p hp⟩).1 =
      (roundOverlapTransition q e ⟨p.1, hp⟩).1 := by
  let middle := roundOverlapTransition q d p
  let directInput : roundOverlap q e := ⟨p.1, hp⟩
  let viaInput : roundOverlap d e := ⟨middle.1, roundOverlapTransition_mem q d e p hp⟩
  let direct := roundOverlapTransition q e directInput
  let via := roundOverlapTransition d e viaInput
  let m := (chartAt CoordinateSpace q.center).symm p.1.1
  have hm : (chartAt CoordinateSpace d.center).symm middle.1.1 = m :=
    chartTransition_symm_point q.center d.center p.2.1
  have hBase : (via.1.1 : CoordinateSpace) = direct.1.1 := by
    change chartAt CoordinateSpace e.center ((chartAt CoordinateSpace d.center).symm middle.1.1) =
      chartAt CoordinateSpace e.center m
    rw [hm]
  have hq : m ∈ (chartAt CoordinateSpace q.center).source :=
    (chartAt CoordinateSpace q.center).symm_mapsTo p.2.1.1
  have hd : m ∈ (chartAt CoordinateSpace d.center).source := p.2.1.2
  have he : m ∈ (chartAt CoordinateSpace e.center).source := hp.1.2
  let a := (‖roundOverlapDirection q d p‖)⁻¹
  let b := (‖roundOverlapDirection d e viaInput‖)⁻¹
  let c := (‖roundOverlapDirection q e directInput‖)⁻¹
  have ha : 0 < a := inv_pos.mpr (norm_pos_iff.mpr (roundOverlapDirection_ne_zero q d p))
  have hb : 0 < b := inv_pos.mpr (norm_pos_iff.mpr (roundOverlapDirection_ne_zero d e viaInput))
  have hc : 0 < c := inv_pos.mpr (norm_pos_iff.mpr (roundOverlapDirection_ne_zero q e directInput))
  have hMid : roundCovector middle.1 = a •
      (cotangentTransitionMatrix q.center d.center m *ᵥ roundCovector p.1) :=
    roundOverlapTransition_covector q d p
  have hDirect : roundCovector direct.1 = c •
      (cotangentTransitionMatrix q.center e.center m *ᵥ roundCovector p.1) :=
    roundOverlapTransition_covector q e directInput
  have hVia : roundCovector via.1 = b • (cotangentTransitionMatrix d.center e.center
      ((chartAt CoordinateSpace d.center).symm middle.1.1) *ᵥ roundCovector middle.1) :=
    roundOverlapTransition_covector d e viaInput
  rw [hm, hMid, Matrix.mulVec_smul,
    cotangentTransitionMatrix_comp_mulVec q.center d.center e.center m hq hd he, smul_smul] at hVia
  have hRay : roundCovector via.1 = ((b * a) / c) • roundCovector direct.1 := by
    rw [hVia, hDirect, smul_smul, div_mul_cancel₀ _ hc.ne']
  exact Prod.ext (Subtype.ext hBase)
    (Subtype.ext (roundDirection_eq_of_pos_smul via.1 direct.1 _ (div_pos (mul_pos hb ha) hc) hRay))

theorem chartAuxiliaryRay_roundOverlapTransition
    (r : ManifoldMetric.Metric (M := M)) (q d : CompactChartInput M) (p : roundOverlap q d) :
    chartAuxiliaryRay r d (roundOverlapTransition q d p).1 = chartAuxiliaryRay r q p.1 := by
  exact chartAuxiliaryRay_eq_of_cotangent_transition r q d p.1 (roundOverlapTransition q d p).1
    (chartTransition_symm_point q.center d.center p.2.1) _
    (inv_pos.mpr (norm_pos_iff.mpr (roundOverlapDirection_ne_zero q d p)))
    (roundOverlapTransition_covector q d p)

/-- The two auxiliary unit coordinate arrays transform by the same cotangent Jacobian. -/
theorem auxiliaryUnitCovector_roundOverlapTransition
    (r : ManifoldMetric.Metric (M := M)) (q d : CompactChartInput M) (p : roundOverlap q d) :
    let p' := (roundOverlapTransition q d p).1
    auxiliaryUnitCovector (chartAuxiliaryInverse r d p'.1) (roundCovector p') =
      cotangentTransitionMatrix q.center d.center ((chartAt CoordinateSpace q.center).symm p.1.1) *ᵥ
        auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1.1) (roundCovector p.1) := by
  let m := (chartAt CoordinateSpace q.center).symm p.1.1
  have hc : m ∈ (chartAt CoordinateSpace q.center).source :=
    (chartAt CoordinateSpace q.center).symm_mapsTo p.2.1.1
  have hd : m ∈ (chartAt CoordinateSpace d.center).source := p.2.1.2
  have h := congrArg (cotangentCoords d.center) (chartAuxiliaryRay_roundOverlapTransition r q d p)
  rw [chartAuxiliaryRay_coords] at h
  exact h.trans (cotangentCoords_assemble_change q.center d.center m hc hd _)

end Burnett.F05.OverlapCovectors
