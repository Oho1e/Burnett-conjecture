import Burnett.Geometry.MaximalChart.CurvatureTransfer
import Burnett.Counterexamples.Bianchi.Geometry

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.MaximalChart

open Set Filter Function LinearMap Burnett.RicciSymbol
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldMetric ManifoldMetricTransition
open scoped Manifold ContDiff Topology Matrix
open BackgroundConnection AffineConnection MetricJetNaturality
open CurvatureJetElimination CurvatureFiberTensor IntrinsicRicciTrace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

variable [SecondCountableTopology M]

private theorem fixedForm_differentiableConnectionAt
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hn : ManifoldBilinear.IsNondegenerate B)
    (c : AtlasChart M) {x : CoordinateSpace} (hx : x ∈ c.chart.target) :
    Burnett.Geometry.CurvatureDifference.DifferentiableConnectionAt (computedConnection (fixedForm B c)) x := by
  have hs := fixedForm_connection_smooth B hB hn c
  intro a b k
  exact ((contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hs a) b) k).contDiffAt
    (c.chart.open_target.mem_nhds hx)).differentiableAt (by simp)

/-- In the curvature trace the contracted slot is conjugated by the actual
invertible differential of the transition. -/
theorem fixedForm_coordinateTrace_change
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hs : ManifoldBilinear.IsSymmetric B) (hn : ManifoldBilinear.IsNondegenerate B)
    (c d : AtlasChart M) (x : CoordinateSpace)
    (hx : x ∈ (c.transition d).source) (u v : CoordinateSpace) :
    LinearMap.trace ℝ CoordinateSpace
        (coordinateEnd (computedConnection (fixedForm B c)) x u v) =
      LinearMap.trace ℝ CoordinateSpace
        (coordinateEnd (computedConnection (fixedForm B d)) (c.transition d x)
          (fderiv ℝ (c.transition d) x u) (fderiv ℝ (c.transition d) x v)) := by
  let e := c.transition d
  let L := (fderiv ℝ e x).toLinearMap
  let I := (fderiv ℝ (d.transition c) (e x)).toLinearMap
  let Γc := computedConnection (fixedForm B c)
  let Γd := computedConnection (fixedForm B d)
  let Cc := coordinateEnd Γc x u v
  let Cd := coordinateEnd Γd (e x) (L u) (L v)
  have hes : e.symm = d.transition c := by
    simp only [e, AtlasChart.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have heback : ContDiffOn ℝ ∞ e.symm e.target := by
    change ContDiffOn ℝ ∞ e.symm e.symm.source
    rw [hes]
    exact d.smooth_transition c
  have heder : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    (c.smooth_transition d).fderiv_of_isOpen e.open_source (by simp)
  let F (a : CoordinateSpace) (y : CoordinateSpace) : CoordinateSpace := fderiv ℝ e (e.symm y) a
  have hF (a : CoordinateSpace) : ContDiffOn ℝ ∞ (F a) e.target :=
    (heder.comp heback e.symm.mapsTo).clm_apply contDiffOn_const
  have hFxy (a : CoordinateSpace) (z : CoordinateSpace) (hz : z ∈ e.source) :
      F a (e z) = fderiv ℝ e z a := by
    dsimp only [F]
    rw [e.left_inv hz]
  have hLeft : I.comp L = LinearMap.id := LinearMap.ext (fun a =>
    congrArg (fun K : CoordinateSpace →L[ℝ] CoordinateSpace => K a)
      (chartTransition_fderiv_leftInverse c d hx))
  have hx' : e x ∈ (d.transition c).source := by
    rw [← hes]
    exact e.mapsTo hx
  have hBack : d.transition c (e x) = x := by
    rw [← hes, e.left_inv hx]
  have hRight : L.comp I = LinearMap.id := by
    have h := chartTransition_fderiv_leftInverse d c hx'
    rw [hBack] at h
    exact LinearMap.ext (fun a => congrArg (fun K : CoordinateSpace →L[ℝ] CoordinateSpace => K a) h)
  have hd₁ := fixedForm_differentiableConnectionAt B hB hn c hx.1
  have hd₂ := fixedForm_differentiableConnectionAt B hB hn d (e.mapsTo hx).1
  have hOrder : (2 : WithTop ℕ∞) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  have hFAt (a : CoordinateSpace) := (hF a).contDiffAt (e.open_target.mem_nhds (e.mapsTo hx))
  have hComp : L.comp Cc = Cd.comp L := by
    apply LinearMap.ext
    intro a
    have ht := fixedForm_coordinateCurvature_change B hB hs hn c d (fun _ => a) (fun _ => v)
      (fun _ => u) (F a) (F v) (F u) contDiffOn_const contDiffOn_const contDiffOn_const
      (hF a) (hF v) (hF u) (hFxy a) (hFxy v) (hFxy u) x hx
    have hA := (hFAt a).differentiableAt (by simp)
    have hV := (hFAt v).differentiableAt (by simp)
    have hU : ContDiffAt ℝ 2 (F u) (e x) := (hFAt u).of_le hOrder
    rw [coordinateCurvature_eq_curvatureValue _ _ _ _ _ hd₁ (differentiableAt_const a)
      (differentiableAt_const v) contDiffAt_const,
      coordinateCurvature_eq_curvatureValue _ _ _ _ _ hd₂ hA hV hU] at ht
    change fderiv ℝ e x (curvatureValue (Γc x) (directionalConnection Γc x) a v u) =
      curvatureValue (Γd (e x)) (directionalConnection Γd (e x)) (F a (e x)) (F v (e x)) (F u (e x)) at ht
    simpa [Cc, Cd, L, hFxy a x hx, hFxy v x hx, hFxy u x hx] using ht
  have hCd : Cd = (L.comp Cc).comp I := by
    rw [hComp, LinearMap.comp_assoc, hRight, LinearMap.comp_id]
  change LinearMap.trace ℝ CoordinateSpace Cc = LinearMap.trace ℝ CoordinateSpace Cd
  rw [hCd, LinearMap.trace_comp_comm' I (L.comp Cc), ← LinearMap.comp_assoc, hLeft, LinearMap.id_comp]

private theorem coordinateEnd_congr_germ {Γ Δ : CoordinateSpace → Connection}
    {x : CoordinateSpace} (h : Γ =ᶠ[𝓝 x] Δ) (u v : CoordinateSpace) :
    coordinateEnd Γ x u v = coordinateEnd Δ x u v := by
  have hJ : directionalConnection Γ x = directionalConnection Δ x := by
    funext z a b k
    have heq : (fun y => Γ y a b k) =ᶠ[𝓝 x] fun y => Δ y a b k :=
      h.mono fun _ h₁ => congrFun (congrFun (congrFun h₁ a) b) k
    exact congrArg (fun D : CoordinateSpace →L[ℝ] ℝ => D z) heq.fderiv_eq
  apply LinearMap.ext
  intro a
  simp only [coordinateEnd_apply, coordinateTensor_apply, h.self_of_nhds, hJ]

variable [T2Space M]

/-- An intrinsically vacuum metric has zero coordinate Ricci on the target
of any fixed smooth chart, with the actual coordinate pullback of the metric. -/
theorem fixedForm_coordinateVacuum_of_intrinsic
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hs : ManifoldBilinear.IsSymmetric B) (hn : ManifoldBilinear.IsNondegenerate B)
    (hVac : IsVacuum B) (c : AtlasChart M) (x : CoordinateSpace)
    (hx : x ∈ c.chart.target) (b k : Index) :
    CurvatureDifference.coordinateRicci (computedConnection (fixedForm B c)) x b k = 0 := by
  let p := c.chart.symm x
  let d := AtlasChart.atPoint p
  let e := c.transition d
  have he : x ∈ e.source := ⟨hx, mem_chart_source CoordinateSpace p⟩
  let y := e x
  have hy : y ∈ (chartAt CoordinateSpace p).target := (e.mapsTo he).1
  let m := (chartAt CoordinateSpace p).symm y
  have hm : m ∈ (chartAt CoordinateSpace p).source := (chartAt CoordinateSpace p).symm_mapsTo hy
  have hForm : fixedForm B d =ᶠ[𝓝 y] coordinateBilinear B p := by
    filter_upwards [(chartAt CoordinateSpace p).open_target.mem_nhds hy] with z hz
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro w'
    exact fixedCoordinateBilinear_of_preferred B p hz w w'
  have hΓ := Burnett.Bianchi.computedConnection_congr_germ _ _ y hForm
  let u := EuclideanSpace.single b (1 : ℝ)
  let v := EuclideanSpace.single k (1 : ℝ)
  let u' := fderiv ℝ e x u
  let v' := fderiv ℝ e x v
  have hTrace := ricci_eq_coordinate_trace B hB hs hn p m hm (tangentFrame p m u') (tangentFrame p m v')
  rw [forward_tangentFrame p m hm, forward_tangentFrame p m hm, hVac] at hTrace
  change 0 = LinearMap.trace ℝ CoordinateSpace
    (coordinateEnd (computedConnection (coordinateBilinear B p))
      (chartAt CoordinateSpace p ((chartAt CoordinateSpace p).symm y)) u' v') at hTrace
  rw [(chartAt CoordinateSpace p).right_inv hy] at hTrace
  calc
    _ = LinearMap.trace ℝ CoordinateSpace (coordinateEnd (computedConnection (fixedForm B c)) x u v) := by
      rw [trace_coordinateEnd_eq_sum]
      have ht : ∀ᶠ z in 𝓝 x, ∀ a i j,
          computedConnection (fixedForm B c) z a i j = computedConnection (fixedForm B c) z a j i := by
        apply Eventually.of_forall
        intro z a i j
        exact christoffel_torsion_free _ _
          (coordinateJet_symmetric _ z
            (Eventually.of_forall fun z' b' c' => hs (c.chart.symm z') _ _)) a i j
      exact coordinateRicci_eq_coordinateTensor_trace _ _ (fixedForm_differentiableConnectionAt B hB hn c hx)
        ht b k
    _ = LinearMap.trace ℝ CoordinateSpace (coordinateEnd (computedConnection (fixedForm B d)) y u' v') :=
      fixedForm_coordinateTrace_change B hB hs hn c d x he u v
    _ = 0 := by rw [coordinateEnd_congr_germ hΓ, ← hTrace]

end Burnett.Geometry.MaximalChart
