import Burnett.Geometry.Causality.CausalChartRelation
import Burnett.Geometry.IntrinsicCov2

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter Bundle
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- A continuously differentiable path is regularly future causal on its parameter
interval when its intrinsic derivative is nonzero causal and future directed. -/
def RegularFutureOn {g : Field (M := M)} (o : TimeOrientation g) (γ : ℝ → M) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, ∃ v : TangentSpace Model (γ t),
    HasMFDerivAt 𝓘(ℝ) Model γ t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
    v ≠ 0 ∧ g (γ t) v v ≤ 0 ∧ g (γ t) (o.vector (γ t)) v < 0

theorem chart_deriv_of_intrinsic_velocity (γ : ℝ → M) (c : M) (t : ℝ)
    (ht : γ t ∈ (chartAt E c).source) (v : TangentSpace Model (γ t))
    (hd : HasMFDerivAt 𝓘(ℝ) Model γ t ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    let y := (chartAt E c) ∘ γ
    HasDerivAt y (deriv y t) t ∧ tangentFrame c (γ t) (deriv y t) = v := by
  let e := chartAt E c
  let F := (trivializationAt E (TangentSpace Model) c).continuousLinearEquivAt ℝ (γ t) ht
  let w := F v
  have hw : tangentFrame c (γ t) w = v := F.symm_apply_apply v
  have hc : MDifferentiableAt Model Model e (γ t) :=
    (mdifferentiable_chart (I := Model) c).mdifferentiableAt ht
  have hComp := (hc.hasMFDerivAt.comp t hd).hasFDerivAt.hasDerivAt
  have hValue : (mfderiv Model Model e (γ t)) v = w := by
    rw [← hw]
    exact IntrinsicCov2.mfderiv_chart_tangentFrame c (γ t) ht w
  have hDeriv : HasDerivAt (e ∘ γ) w t := by
    convert hComp using 1
    change w = (mfderiv Model Model e (γ t)) ((1 : ℝ) • v)
    rw [one_smul]
    exact hValue.symm
  dsimp only
  rw [hDeriv.deriv]
  exact ⟨hDeriv, hw⟩

/-- Every regular future causal curve is represented by a future causal chart
segment between any two times in a sufficiently small parameter neighborhood. -/
theorem exists_futureCausalChartSegments_near {g : Field (M := M)} (hg : IsSmooth g)
    (hL : HasLorentzSignature g) (o : TimeOrientation g) (γ : ℝ → M)
    {I : Set ℝ} (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ) Model 1 γ I)
    (hFuture : RegularFutureOn o γ I) {s : ℝ} (hs : s ∈ I) :
    ∃ δ > (0 : ℝ), ∀ a ∈ Metric.ball s δ, ∀ b ∈ Metric.ball s δ,
      a < b → HasFutureCausalChartSegment o (γ a) (γ b) := by
  let c := γ s
  let e := chartAt E c
  let y := e ∘ γ
  let x := y s
  let T := ChartVectorField.coordinateVector o.vector c
  let n := T x
  have hc : c ∈ e.source := mem_chart_source E c
  have hx : x ∈ e.target := e.mapsTo hc
  have hTx (z : E) (hz : z ∈ e.target) : coordinateBilinear g c z (T z) (T z) < 0 := by
    change g (e.symm z) (tangentFrame c (e.symm z) (T z)) (tangentFrame c (e.symm z) (T z)) < 0
    rw [ChartVectorField.tangentFrame_coordinateVector o.vector c hz]
    exact o.timelike _
  have hTc : ContinuousAt T x :=
    (ChartVectorField.contDiffOn_coordinateVector o.vector o.smooth c).continuousOn.continuousAt
      (e.open_target.mem_nhds hx)
  have hBnn := continuousAt_actual_chart_pairing g hg c x id (fun _ => n) (fun _ => n)
    continuous_id.continuousAt continuousAt_const continuousAt_const hx
  have hBnT := continuousAt_actual_chart_pairing g hg c x id (fun _ => n) T
    continuous_id.continuousAt continuousAt_const hTc hx
  have hWindow : e.target ∩ {z | coordinateBilinear g c z n n < 0} ∩
      {z | coordinateBilinear g c z n (T z) < 0} ∈ 𝓝 x :=
    inter_mem (inter_mem (e.open_target.mem_nhds hx)
      (hBnn.preimage_mem_nhds (Iio_mem_nhds (hTx x hx)))) (hBnT.preimage_mem_nhds (Iio_mem_nhds (hTx x hx)))
  obtain ⟨R, hR, hBall⟩ := Metric.mem_nhds_iff.mp hWindow
  have hOuter := (Metric.closedBall_subset_ball (half_lt_self hR)).trans hBall
  have hγs : ContinuousAt γ s := hγ.continuousOn.continuousAt (hI.mem_nhds hs)
  have hys : ContinuousAt y s := (e.continuousAt hc).comp hγs
  have hNear : I ∩ γ ⁻¹' e.source ∩ y ⁻¹' Metric.ball x (R / 4) ∈ 𝓝 s :=
    inter_mem (inter_mem (hI.mem_nhds hs) (hγs.preimage_mem_nhds (e.open_source.mem_nhds hc)))
      (hys.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by positivity))))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hNear
  let J := Metric.ball s δ
  have hJI : J ⊆ I := hδsub.trans (inter_subset_left.trans inter_subset_left)
  have hJchart : MapsTo γ J e.source := fun _ ht => (hδsub ht).1.2
  have hyJ : ContDiffOn ℝ 1 y J := by
    have he : ContMDiffOn Model Model 1 e e.source := contMDiffOn_chart
    have hyM : ContMDiffOn 𝓘(ℝ) Model 1 y J := he.comp (hγ.mono hJI) hJchart
    exact hyM.contDiffOn
  have hvJ : ContinuousOn (fun t => ‖deriv y t‖) J :=
    (hyJ.continuousOn_deriv_of_isOpen Metric.isOpen_ball (by norm_num)).norm
  refine ⟨δ, hδ, fun a ha b hb hab => ?_⟩
  have habJ : Icc a b ⊆ J := (convex_ball s δ).ordConnected.out ha hb
  obtain ⟨V, hV⟩ := isCompact_Icc.bddAbove_image (hvJ.mono habJ)
  refine ⟨c, x, n, R / 4, R / 2, a, b, max V 0, y, deriv y,
    (e.left_inv (hJchart ha)).symm, (e.left_inv (hJchart hb)).symm, hab, by linarith,
    le_max_right _ _, fun _ hz => (hOuter hz).1.1, fun _ hz => (hOuter hz).1.2,
    fun _ hz => (hOuter hz).2, hyJ.mono habJ, ?_⟩
  intro t ht
  have htJ := habJ ht
  have htE := hJchart htJ
  have htOut : y t ∈ Metric.closedBall x (R / 2) :=
    Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall (hδsub htJ).2)
  have htTarget := (hOuter htOut).1.1
  obtain ⟨v, hwd, hne, hNull, hTime⟩ := hFuture t (hJI htJ)
  obtain ⟨hd, hFrame⟩ := chart_deriv_of_intrinsic_velocity γ c t htE v hwd
  have hInv : e.symm (y t) = γ t := e.left_inv htE
  have hWne : deriv y t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hFrame
    exact hne hFrame.symm
  have hWW : coordinateBilinear g c (y t) (deriv y t) (deriv y t) ≤ 0 := by
    change g (e.symm (y t)) (tangentFrame c (e.symm (y t)) (deriv y t))
      (tangentFrame c (e.symm (y t)) (deriv y t)) ≤ 0
    rw [hInv, hFrame]
    exact hNull
  have hTW : coordinateBilinear g c (y t) (T (y t)) (deriv y t) < 0 := by
    change g (e.symm (y t)) (tangentFrame c (e.symm (y t)) (T (y t)))
      (tangentFrame c (e.symm (y t)) (deriv y t)) < 0
    rw [ChartVectorField.tangentFrame_coordinateVector o.vector c htTarget, hInv, hFrame]
    exact hTime
  have hTn : coordinateBilinear g c (y t) (T (y t)) n < 0 := by
    rw [(coordinateBilinear_symmetric g hL.isSymmetric c (y t)).eq]
    exact (hOuter htOut).2
  refine ⟨Metric.ball_subset_closedBall (hδsub htJ).2, hd, hWW, ?_, ?_⟩
  · exact (chart_causal_sign_change hL c htTarget (hTx (y t) htTarget) (hOuter htOut).1.2
      hTn hWne hWW hTW).le
  · exact (hV (mem_image_of_mem _ ht)).trans (le_max_left _ _)

/-- Ordered endpoints of an actual regular future causal curve are causally
related. The local chart choice may vary along the curve. -/
theorem chartCausalRelation_of_regular_future_curve {g : Field (M := M)} (hg : IsSmooth g)
    (hL : HasLorentzSignature g) (o : TimeOrientation g) (γ : ℝ → M)
    {I : Set ℝ} (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ) Model 1 γ I)
    (hFuture : RegularFutureOn o γ I) {a b : ℝ} (hab : a < b) (hSeg : Icc a b ⊆ I) :
    (γ a, γ b) ∈ chartCausalRelation o := by
  apply interval_relation_of_local_steps (chartCausalRelation_transitive o) γ hab
  intro s hs
  obtain ⟨δ, hδ, hSeg⟩ := exists_futureCausalChartSegments_near hg hL o γ hI hγ hFuture (hSeg hs)
  have hB : ∀ᶠ t in 𝓝[≠] s, t ∈ Metric.ball s δ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds s hδ)
  filter_upwards [hB] with t ht
  have hsB : s ∈ Metric.ball s δ := Metric.mem_ball_self hδ
  exact ⟨fun hst => Relation.ReflTransGen.single (Or.inr (hSeg s hsB t ht hst)),
    fun hts => Relation.ReflTransGen.single (Or.inr (hSeg t ht s hsB hts))⟩

end Burnett.Geometry.FiniteCausalVolume
