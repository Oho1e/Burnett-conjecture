import Burnett.Geometry.ChartDifferential
import Burnett.Geometry.MetricJetNaturality
import Burnett.Geometry.ManifoldVolumeRegularity

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.MaximalChart

open Set Filter Function LinearMap Burnett.RicciSymbol
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldMetric ManifoldMetricTransition
open scoped Manifold ContDiff Topology Matrix
open ManifoldBilinear MetricJetNaturality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- A coordinate map belonging to the smooth maximal atlas. -/
structure AtlasChart (M : Type*) [TopologicalSpace M] [ChartedSpace CoordinateSpace M] where
  chart : OpenPartialHomeomorph M CoordinateSpace
  compatible : chart ∈ IsManifold.maximalAtlas Model ∞ M

/-- The preferred chart at a point, viewed as a member of the maximal atlas. -/
def AtlasChart.atPoint (p : M) : AtlasChart M :=
  ⟨chartAt CoordinateSpace p, IsManifold.chart_mem_maximalAtlas p⟩

def AtlasChart.transition (q t : AtlasChart M) := q.chart.symm.trans t.chart

omit [IsManifold Model ∞ M] in
theorem AtlasChart.smooth_transition (q t : AtlasChart M) :
    ContDiffOn ℝ ∞ (q.transition t) (q.transition t).source := by
  have h := (IsManifold.compatible_of_mem_maximalAtlas q.compatible t.compatible).1
  change ContDiffOn ℝ ∞ _ _ at h
  simpa only [mfld_simps, AtlasChart.transition] using h

omit [IsManifold Model ∞ M] in
theorem chartTransition_fderiv_leftInverse (c d : AtlasChart M) {x : CoordinateSpace}
    (hx : x ∈ (c.transition d).source) :
    (fderiv ℝ (d.transition c) (c.transition d x)).comp
      (fderiv ℝ (c.transition d) x) = ContinuousLinearMap.id ℝ CoordinateSpace := by
  let e := c.transition d
  have hsymm : e.symm = d.transition c := by
    simp only [e, AtlasChart.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hy : e x ∈ (d.transition c).source := by
    rw [← hsymm]
    exact e.mapsTo hx
  have he : HasFDerivAt e (fderiv ℝ e x) x :=
    ((((c.smooth_transition d).differentiableOn (by simp)) x hx).differentiableAt
      (e.open_source.mem_nhds hx)).hasFDerivAt
  have hd : HasFDerivAt (d.transition c) (fderiv ℝ (d.transition c) (e x)) (e x) :=
    (((d.smooth_transition c).differentiableOn (by simp)) _ hy).differentiableAt
      ((d.transition c).open_source.mem_nhds hy) |>.hasFDerivAt
  have hf : (fun z : CoordinateSpace => z) =ᶠ[𝓝 x] (d.transition c) ∘ e := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy'
    rw [Function.comp_apply, ← hsymm, e.left_inv hy']
  exact ((hd.comp x he).congr_of_eventuallyEq hf).unique (hasFDerivAt_id x)

omit [IsManifold Model ∞ M] in
theorem chartDerivative_det_ne_zero (c d : AtlasChart M) (x : CoordinateSpace)
    (hx : x ∈ (c.transition d).source) : (fderiv ℝ (c.transition d) x).det ≠ 0 := by
  let e := c.transition d
  have hL : (fderiv ℝ (d.transition c) (e x)).toLinearMap.comp (fderiv ℝ e x).toLinearMap =
      LinearMap.id := congrArg ContinuousLinearMap.toLinearMap (chartTransition_fderiv_leftInverse c d hx)
  have hDet := congrArg LinearMap.det hL
  rw [LinearMap.det_comp, LinearMap.det_id] at hDet
  intro hn
  change LinearMap.det (fderiv ℝ e x).toLinearMap = 0 at hn
  rw [hn, mul_zero] at hDet
  exact zero_ne_one hDet

/-- Evaluate the actual geometric tensor on the derivatives of the inverse
chart, at the point represented by its Euclidean coordinate. -/
def fixedCoordinateBilinear (B : ManifoldBilinear.Field (M := M))
    (c : AtlasChart M) (x u v : CoordinateSpace) : ℝ :=
  B (c.chart.symm x) (mfderiv Model Model c.chart.symm x u) (mfderiv Model Model c.chart.symm x v)

theorem fixedCoordinateBilinear_of_preferred (B : ManifoldBilinear.Field (M := M))
    (c : M) {x : CoordinateSpace} (hx : x ∈ (chartAt CoordinateSpace c).target)
    (u v : CoordinateSpace) :
    fixedCoordinateBilinear B (.atPoint c) x u v = coordinateBilinear B c x u v := by
  have h := ChartDifferential.tangentFrame_eq_mfderiv_symm c
    ((chartAt CoordinateSpace c).symm x) ((chartAt CoordinateSpace c).symm_mapsTo hx)
  rw [(chartAt CoordinateSpace c).right_inv hx] at h
  change _ = B _ (tangentFrame c _ u) (tangentFrame c _ v)
  rw [h]
  rfl

theorem fixedCoordinateBilinear_change (B : ManifoldBilinear.Field (M := M))
    (c d : AtlasChart M) {x : CoordinateSpace} (hx : x ∈ (c.transition d).source)
    (u v : CoordinateSpace) :
    fixedCoordinateBilinear B c x u v =
      fixedCoordinateBilinear B d (c.transition d x)
        (fderiv ℝ (c.transition d) x u) (fderiv ℝ (c.transition d) x v) := by
  let e := c.transition d
  have hinv (y : CoordinateSpace) (hy : y ∈ e.source) :
      d.chart.symm (e y) = c.chart.symm y := d.chart.left_inv hy.2
  have he : d.chart.symm ∘ e =ᶠ[𝓝 x] (c.chart.symm : CoordinateSpace → M) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact hinv y hy
  have hd := (contMDiffAt_symm_of_mem_maximalAtlas d.compatible (e.mapsTo hx).1).mdifferentiableAt
    (by simp)
  have hdiff : MDifferentiableAt Model Model e x :=
    ((c.smooth_transition d).contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp) |>.mdifferentiableAt
  have hframe (z : CoordinateSpace) :
      mfderiv Model Model c.chart.symm x z = mfderiv Model Model d.chart.symm (e x) (fderiv ℝ e x z) := by
    calc
      _ = mfderiv Model Model (d.chart.symm ∘ e) x z :=
        congrArg (fun A : CoordinateSpace →L[ℝ] CoordinateSpace => A z) (he.mfderiv_eq (I := Model) (I' := Model)).symm
      _ = _ := by simpa only [mfderiv_eq_fderiv] using mfderiv_comp_apply x hd hdiff z
  unfold fixedCoordinateBilinear
  change B (c.chart.symm x) _ _ = B (d.chart.symm (e x)) _ _
  rw [hframe u, hframe v, hinv x hx]

def fixedForm (B : ManifoldBilinear.Field (M := M))
    (c : AtlasChart M) (x : CoordinateSpace) : LinearMap.BilinForm ℝ CoordinateSpace :=
  LinearMap.mk₂ ℝ (fixedCoordinateBilinear B c x)
    (by intros; simp [fixedCoordinateBilinear, map_add])
    (by intros; simp [fixedCoordinateBilinear, map_smul])
    (by intros; simp [fixedCoordinateBilinear, map_add])
    (by intros; simp [fixedCoordinateBilinear, map_smul])

theorem fixedForm_matrix_change (B : ManifoldBilinear.Field (M := M))
    (c d : AtlasChart M) {x : CoordinateSpace} (hx : x ∈ (c.transition d).source) :
    (metricComponents (fixedForm B c) x : Matrix Burnett.RicciSymbol.Index Burnett.RicciSymbol.Index ℝ) =
      TensorCoordinateChange.pullbackMetric (metricComponents (fixedForm B d) (c.transition d x))
        (derivativeMatrix (fderiv ℝ (c.transition d) x)) := by
  let L := (fderiv ℝ (c.transition d) x).toLinearMap
  have h : fixedForm B c x = (fixedForm B d (c.transition d x)).comp L L := by
    ext u v
    exact fixedCoordinateBilinear_change B c d hx u v
  simp only [metricComponents_eq_toMatrix]
  rw [h]
  exact BilinForm.toMatrix_comp (b := coordinateBasis) (c := coordinateBasis)
    (fixedForm B d (c.transition d x)) L L

omit [IsManifold Model ∞ M] in
theorem fixedJacobian_entry_smooth (c d : AtlasChart M) (a b : Index) :
    ContDiffOn ℝ ∞ (fun x => derivativeMatrix (fderiv ℝ (c.transition d) x) a b) (c.transition d).source := by
  let e := c.transition d
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    (c.smooth_transition d).fderiv_of_isOpen e.open_source (by simp)
  simp only [derivativeMatrix_apply]
  exact (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.comp_contDiffOn
    (hD.clm_apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : CoordinateSpace => coordinateBasis b) _))

theorem fixedForm_components_smooth [SecondCountableTopology M]
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (c : AtlasChart M) (i j : Index) :
    ContDiffOn ℝ ∞ (fun y => metricComponents (fixedForm B c) y i j) c.chart.target := by
  intro x hx
  let p := c.chart.symm x
  let d := AtlasChart.atPoint p
  let e := c.transition d
  have he : x ∈ e.source := ⟨hx, mem_chart_source CoordinateSpace p⟩
  have hG (k l : Index) : ContDiffOn ℝ ∞
      (fun y => metricComponents (coordinateBilinear B p) (e y) k l) e.source :=
    (ManifoldBilinear.contDiffOn_metricComponents B hB p k l).comp
      (c.smooth_transition d) (fun y hy => (e.mapsTo hy).1)
  let A := fun y => derivativeMatrix (fderiv ℝ e y)
  let G := fun y => metricComponents (coordinateBilinear B p) (e y)
  have hfun : ContDiffOn ℝ ∞ (fun y => ∑ k, (∑ l, A y l i * G y l k) * A y k j) e.source := by
    exact ContDiffOn.sum (fun k _ => (ContDiffOn.sum (fun l _ =>
      (fixedJacobian_entry_smooth c d l i).mul (hG l k))).mul (fixedJacobian_entry_smooth c d k j))
  apply ((hfun.congr ?_).contDiffAt (e.open_source.mem_nhds he)).contDiffWithinAt
  intro y hy
  have h := congrArg (fun P : Matrix Index Index ℝ => P i j) (fixedForm_matrix_change B c d hy)
  have hd (b f : Index) :
      metricComponents (fixedForm B d) (e y) b f =
      metricComponents (coordinateBilinear B p) (e y) b f :=
    fixedCoordinateBilinear_of_preferred B p (e.mapsTo hy).1 _ _
  simpa only [TensorCoordinateChange.pullbackMetric,Matrix.mul_apply,Matrix.transpose_apply,hd,A,G,e] using h

omit [IsManifold Model ∞ M] in
theorem fixedDerivativeMatrix_isUnit (c d : AtlasChart M) {x : CoordinateSpace}
    (hx : x ∈ (c.transition d).source) :
    IsUnit (derivativeMatrix (fderiv ℝ (c.transition d) x)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [det_derivativeMatrix]
  exact isUnit_iff_ne_zero.mpr (chartDerivative_det_ne_zero c d x hx)

theorem fixedForm_eq_preferred_components (B : Field (M := M)) (q : M)
    {x : CoordinateSpace} (hx : x ∈ (chartAt CoordinateSpace q).target) :
    metricComponents (fixedForm B (.atPoint q)) x = metricComponents (coordinateBilinear B q) x := by
  funext i j
  exact fixedCoordinateBilinear_of_preferred B q hx _ _

/-- Nondegeneracy of the intrinsic tensor implies nonsingularity of its actual chart matrix. -/
theorem fixedForm_det_ne_zero (B : ManifoldBilinear.Field (M := M)) (hn : ManifoldBilinear.IsNondegenerate B)
    (c : AtlasChart M) {x : CoordinateSpace} (hx : x ∈ c.chart.target) :
    Matrix.det (metricComponents (fixedForm B c) x) ≠ 0 := by
  let p := c.chart.symm x
  let d := AtlasChart.atPoint p
  have he : x ∈ (c.transition d).source := ⟨hx, mem_chart_source CoordinateSpace p⟩
  have ht : c.transition d x ∈ (chartAt CoordinateSpace p).target := ((c.transition d).mapsTo he).1
  have hA := (Matrix.isUnit_iff_isUnit_det _).mp (fixedDerivativeMatrix_isUnit c d he)
  have hG := ManifoldVolumeRegularity.coordinate_det_ne_zero B hn p ht
  rw [fixedForm_matrix_change B c d he, fixedForm_eq_preferred_components B p ht,
    TensorCoordinateChange.pullbackMetric, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero (isUnit_iff_ne_zero.mp hA) hG) (isUnit_iff_ne_zero.mp hA)

end Burnett.Geometry.MaximalChart
