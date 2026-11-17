import Burnett.Geometry.ActualChartSecondJet
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Genuine vector fields in preferred tangent charts

Coordinates use the actual tangent-bundle trivialization at c, evaluated at
chart_c.symm y. They reconstruct the tangent vector and transform by the
actual derivative of chart_d composed with chart_c.symm. TangentSpace's
underlying type is never used as an identification of different frames.

Smoothness is ContMDiff of the total-space section. It is equivalent to
smoothness in every preferred chart. On the actual open overlap the vector
transformation law can be differentiated; its nonlinear term is the actual
iterated Frechet derivative, also identified with the finite Hessian array.
No global frame, extension outside a chart, connection naturality or global
Levi-Civita identification is asserted here.
-/

noncomputable section
open Bundle Set
open scoped Manifold ContDiff Topology BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetricTransition

namespace Burnett.Geometry.ChartVectorField
variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- A section of the actual tangent fibers, with no regularity assumed. -/
abbrev Field := ∀ m : M, TangentSpace Model m

/-- Smoothness of the genuine total-space section, without coordinate fields. -/
def IsSmooth (V : Field (M := M)) : Prop :=
  ContMDiff Model (Model.prod Model) ∞
    (fun m => TotalSpace.mk' CoordinateSpace m (V m))

/-- The forward preferred tangent trivialization, at a manifold point. -/
def frameVector (V : Field (M := M)) (c m : M) : CoordinateSpace :=
  ((trivializationAt CoordinateSpace (TangentSpace Model) c) ⟨m, V m⟩).2

/-- Coordinates at the inverse image of y; only chart-target germs are used. -/
def coordinateVector (V : Field (M := M)) (c : M) (y : CoordinateSpace) : CoordinateSpace :=
  frameVector V c ((chartAt CoordinateSpace c).symm y)

theorem tangentFrame_frameVector (V : Field (M := M)) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    tangentFrame c m (frameVector V c m) = V m := by
  let e := trivializationAt CoordinateSpace (TangentSpace Model) c
  change e.symmL ℝ m (e ⟨m, V m⟩).2 = V m
  simpa only [Trivialization.symmL_apply] using e.symm_apply_apply_mk hm (V m)

theorem frameVector_change (V : Field (M := M)) (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source)
    (hd : m ∈ (chartAt CoordinateSpace d).source) :
    frameVector V d m =
      fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m) (frameVector V c m) := by
  apply tangentFrame_injective d m hd
  calc
    _ = V m := tangentFrame_frameVector V d m hd
    _ = tangentFrame c m (frameVector V c m) := (tangentFrame_frameVector V c m hc).symm
    _ = _ := tangentFrame_change c d m hc hd (frameVector V c m)

theorem coordinateVector_change (V : Field (M := M)) (c d : M) {y : CoordinateSpace}
    (hy : y ∈ (chartTransition c d).source) :
    coordinateVector V d (chartTransition c d y) =
      fderiv ℝ (chartTransition c d) y (coordinateVector V c y) := by
  simp only [coordinateVector, chartTransition_symm_point c d hy]
  have h := frameVector_change V c d ((chartAt CoordinateSpace c).symm y)
    ((chartAt CoordinateSpace c).symm_mapsTo hy.1) hy.2
  simpa only [(chartAt CoordinateSpace c).right_inv hy.1] using h

theorem contMDiffOn_frameVector (V : Field (M := M)) (hV : IsSmooth V) (c : M) :
    ContMDiffOn Model Model ∞ (frameVector V c) (chartAt CoordinateSpace c).source := by
  let e := trivializationAt CoordinateSpace (TangentSpace Model) c
  exact e.contMDiffOn_section_baseSet_iff.mp hV.contMDiffOn

theorem contDiffOn_coordinateVector (V : Field (M := M)) (hV : IsSmooth V) (c : M) :
    ContDiffOn ℝ ∞ (coordinateVector V c) (chartAt CoordinateSpace c).target := by
  exact ((contMDiffOn_frameVector V hV c).comp
    contMDiffOn_chart_symm (chartAt CoordinateSpace c).symm_mapsTo).contDiffOn

theorem coordinateVector_at_chart (V : Field (M := M)) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    coordinateVector V c (chartAt CoordinateSpace c m) = frameVector V c m := by
  simp only [coordinateVector, (chartAt CoordinateSpace c).left_inv hm]

theorem tangentFrame_coordinateVector (V : Field (M := M)) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) :
    tangentFrame c ((chartAt CoordinateSpace c).symm y) (coordinateVector V c y) =
      V ((chartAt CoordinateSpace c).symm y) :=
  tangentFrame_frameVector V c _ ((chartAt CoordinateSpace c).symm_mapsTo hy)

theorem differentiableAt_coordinateVector (V : Field (M := M)) (hV : IsSmooth V)
    (c : M) {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    DifferentiableAt ℝ (coordinateVector V c) y := by
  apply ((contDiffOn_coordinateVector V hV c).contDiffAt
    ((chartAt CoordinateSpace c).open_target.mem_nhds hy)).differentiableAt
  change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

theorem fderiv_coordinateVector_change (V : Field (M := M)) (hV : IsSmooth V)
    (c d : M) {x : CoordinateSpace} (hx : x ∈ (chartTransition c d).source) :
    (fderiv ℝ (coordinateVector V d) (chartTransition c d x)).comp
        (fderiv ℝ (chartTransition c d) x) =
      (fderiv ℝ (chartTransition c d) x).comp (fderiv ℝ (coordinateVector V c) x) +
        (fderiv ℝ (fderiv ℝ (chartTransition c d)) x).flip (coordinateVector V c x) := by
  have hφ := (ActualChartSecondJet.contDiffOn_chartTransition_infty c d).contDiffAt
    ((chartTransition c d).open_source.mem_nhds hx)
  have hφ2 : ContDiffAt ℝ 2 (chartTransition c d) x := hφ.of_le (by
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hφd := hφ2.differentiableAt (by norm_num)
  have hDφ : DifferentiableAt ℝ (fderiv ℝ (chartTransition c d)) x :=
    (hφ2.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have hc := differentiableAt_coordinateVector V hV c hx.1
  have hd := differentiableAt_coordinateVector V hV d ((chartAt CoordinateSpace d).mapsTo hx.2)
  have heq : (fun y => coordinateVector V d (chartTransition c d y)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (chartTransition c d) y (coordinateVector V c y)) := by
    filter_upwards [(chartTransition c d).open_source.mem_nhds hx] with y hy
    exact coordinateVector_change V c d hy
  calc
    _ = fderiv ℝ (fun y => coordinateVector V d (chartTransition c d y)) x :=
      (fderiv_comp' x hd hφd).symm
    _ = fderiv ℝ (fun y => fderiv ℝ (chartTransition c d) y (coordinateVector V c y)) x :=
      heq.fderiv_eq
    _ = _ := fderiv_clm_apply hDφ hc

theorem derivative_coordinateVector_change (V : Field (M := M)) (hV : IsSmooth V)
    (c d : M) {x : CoordinateSpace} (hx : x ∈ (chartTransition c d).source)
    (v : CoordinateSpace) :
    fderiv ℝ (coordinateVector V d) (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v) =
      fderiv ℝ (fderiv ℝ (chartTransition c d)) x v (coordinateVector V c x) +
        fderiv ℝ (chartTransition c d) x (fderiv ℝ (coordinateVector V c) x v) := by
  have h := congrArg (fun L : CoordinateSpace →L[ℝ] CoordinateSpace => L v)
    (fderiv_coordinateVector_change V hV c d hx)
  calc
    _ = fderiv ℝ (chartTransition c d) x (fderiv ℝ (coordinateVector V c) x v) +
        fderiv ℝ (fderiv ℝ (chartTransition c d)) x v (coordinateVector V c x) := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.flip_apply] using h
    _ = _ := add_comm _ _

omit [IsManifold Model ∞ M] in
/-- Pure finite contraction of the actual iterated derivative on arbitrary vectors. -/
theorem connectionTerm_actualHessian (c d : M) (x v w : CoordinateSpace) :
    CoordinateCovariantDerivative.connectionTerm (ActualChartSecondJet.actualHessian c d x) v w =
      fderiv ℝ (fderiv ℝ (chartTransition c d)) x v w := by
  have repr_apply : ∀ z : CoordinateSpace, ∀ i : Index, coordinateBasis.repr z i = z i :=
    fun _ _ => rfl
  have hv : v = ∑ i, v i • coordinateBasis i := by
    simpa only [repr_apply] using (coordinateBasis.sum_repr v).symm
  have hw : w = ∑ i, w i • coordinateBasis i := by
    simpa only [repr_apply] using (coordinateBasis.sum_repr w).symm
  ext a
  change (∑ b, ∑ e, ActualChartSecondJet.actualHessian c d x a b e * v b * w e) =
    (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Index => ℝ) a) (fderiv ℝ (fderiv ℝ (chartTransition c d)) x v w)
  conv_rhs => rw [hv, hw]
  simp only [ActualChartSecondJet.actualHessian, map_sum, map_smul,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    PiLp.projₗ_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [PiLp.ofLp_apply]
  ring

theorem derivative_coordinateVector_change_hessian (V : Field (M := M)) (hV : IsSmooth V)
    (c d : M) {x : CoordinateSpace} (hx : x ∈ (chartTransition c d).source)
    (v : CoordinateSpace) :
    fderiv ℝ (coordinateVector V d) (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v) =
      CoordinateCovariantDerivative.connectionTerm (ActualChartSecondJet.actualHessian c d x)
          v (coordinateVector V c x) +
        fderiv ℝ (chartTransition c d) x (fderiv ℝ (coordinateVector V c) x v) := by
  rw [connectionTerm_actualHessian]
  exact derivative_coordinateVector_change V hV c d hx v

/-- Preferred coordinate smoothness reconstructs smoothness of the actual section. -/
theorem isSmooth_of_contDiffOn_coordinateVector (V : Field (M := M))
    (hV : ∀ c : M, ContDiffOn ℝ ∞ (coordinateVector V c) (chartAt CoordinateSpace c).target) :
    IsSmooth V := by
  intro m
  let e := trivializationAt CoordinateSpace (TangentSpace Model) m
  have hm : m ∈ (chartAt CoordinateSpace m).source := mem_chart_source CoordinateSpace m
  apply (e.contMDiffAt_section_iff hm).mpr
  have htarget := (chartAt CoordinateSpace m).mapsTo hm
  have hc := ((hV m).contDiffAt ((chartAt CoordinateSpace m).open_target.mem_nhds htarget)).contMDiffAt
  have hchart : ContMDiffAt Model Model ∞ (chartAt CoordinateSpace m) m :=
    contMDiffOn_chart.contMDiffAt ((chartAt CoordinateSpace m).open_source.mem_nhds hm)
  have hcomp := hc.comp m hchart
  have heq : frameVector V m =ᶠ[𝓝 m]
      (fun p => coordinateVector V m (chartAt CoordinateSpace m p)) := by
    filter_upwards [(chartAt CoordinateSpace m).open_source.mem_nhds hm] with p hp
    exact (coordinateVector_at_chart V m p hp).symm
  exact heq.contMDiffAt_iff.mpr hcomp

theorem isSmooth_iff_contDiffOn_coordinateVector (V : Field (M := M)) :
    IsSmooth V ↔
      ∀ c : M, ContDiffOn ℝ ∞ (coordinateVector V c) (chartAt CoordinateSpace c).target :=
  ⟨fun hV c => contDiffOn_coordinateVector V hV c, isSmooth_of_contDiffOn_coordinateVector V⟩

end Burnett.Geometry.ChartVectorField
