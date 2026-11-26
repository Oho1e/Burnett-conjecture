import Burnett.Geometry.Causality.IntrinsicPiecewiseCausalPaths
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
set_option maxHeartbeats 7500000

noncomputable section
namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter Bundle
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.CotangentHamiltonCauchySlice

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

private theorem exists_coordinate_extension_with_derivatives (y w : ℝ → E) {a b : ℝ}
    (hab : a < b) (hd : ∀ t ∈ Icc a b, HasDerivWithinAt y (w t) (Icc a b) t) :
    ∃ Y : ℝ → E, EqOn Y y (Icc a b) ∧ ∀ t ∈ Icc a b, HasDerivAt Y (w t) t := by
  let u (t : ℝ) : ℝ := (projIcc a b hab.le t).val
  let Y (t : ℝ) := y (u t) + (t - u t) • w (u t)
  have hEq : EqOn Y y (Icc a b) := by
    intro t ht
    simp [Y, u, projIcc_of_mem hab.le ht]
  refine ⟨Y, hEq, fun t ht => ?_⟩
  have hY := (hd t ht).congr hEq (hEq ht)
  rcases eq_or_lt_of_le ht.1 with ha | hAt
  · subst t
    have hLeft : HasDerivAt (fun k : ℝ => y a + (k - a) • w a) (w a) a := by
      simpa only [one_smul] using (((hasDerivAt_id a).sub_const a).smul_const (w a)).const_add (y a)
    have hLeftEq : EqOn Y (fun k : ℝ => y a + (k - a) • w a) (Iic a) := by
      intro k hk
      simp [Y, u, projIcc_of_le_left hab.le hk]
    have ha : a ∈ Iic a := by simp
    apply (hY.union (hLeft.hasDerivWithinAt.congr hLeftEq (hLeftEq ha))).hasDerivAt
    apply mem_of_superset (Iio_mem_nhds hab)
    intro k hk
    by_cases hka : k ≤ a
    · exact Or.inr hka
    · exact Or.inl ⟨le_of_not_ge hka, hk.le⟩
  rcases eq_or_lt_of_le ht.2 with hb | hTb
  · subst t
    have hRight : HasDerivAt (fun k : ℝ => y b + (k - b) • w b) (w b) b := by
      simpa only [one_smul] using (((hasDerivAt_id b).sub_const b).smul_const (w b)).const_add (y b)
    have hRightEq : EqOn Y (fun k : ℝ => y b + (k - b) • w b) (Ici b) := by
      intro k hk
      simp [Y, u, projIcc_of_right_le hab.le hk]
    have hb : b ∈ Ici b := by simp
    apply (hY.union (hRight.hasDerivWithinAt.congr hRightEq (hRightEq hb))).hasDerivAt
    apply mem_of_superset (Ioi_mem_nhds hab)
    intro k hk
    by_cases hkb : b ≤ k
    · exact Or.inr hkb
    · exact Or.inl ⟨hk.le, le_of_not_ge hkb⟩
  exact hY.hasDerivAt (mem_of_superset (Ioo_mem_nhds hAt hTb) Ioo_subset_Icc_self)

private theorem interval_relation_of_closed_local_steps {X : Type*} {R : X → X → Prop}
    (hTrans : Transitive R) (γ : ℝ → X) {a b : ℝ} (hab : a < b)
    (hLocal : ∀ s ∈ Icc a b, ∀ᶠ t in 𝓝[Icc a b] s,
      (s ≤ t → R (γ s) (γ t)) ∧ (t ≤ s → R (γ t) (γ s))) : R (γ a) (γ b) := by
  let u (t : ℝ) : ℝ := (projIcc a b hab.le t).val
  have hEq {s : ℝ} (hs : s ∈ Icc a b) : u s = s := by simp [u, projIcc_of_mem hab.le hs]
  have hu : Continuous u := continuous_subtype_val.comp continuous_projIcc
  have hm : Monotone u := fun _ _ h => (monotone_projIcc hab.le) h
  rw [← hEq (left_mem_Icc.mpr hab.le), ← hEq (right_mem_Icc.mpr hab.le)]
  apply interval_relation_of_local_steps hTrans (γ ∘ u) hab
  intro s hs
  have hCont : Tendsto u (𝓝 s) (𝓝 (u s)) := hu.continuousAt
  rw [hEq hs] at hCont
  have hT : Tendsto u (𝓝 s) (𝓝[Icc a b] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hCont, Eventually.of_forall fun t => (projIcc a b hab.le t).property⟩
  filter_upwards [(hT.eventually (hLocal s hs)).filter_mono nhdsWithin_le_nhds] with t ht
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hh : s ≤ u t := by simpa only [hEq hs] using hm h.le
    simpa only [Function.comp_apply, hEq hs] using ht.1 hh
  · have hh : u t ≤ s := by simpa only [hEq hs] using hm h.le
    simpa only [Function.comp_apply, hEq hs] using ht.2 hh

private theorem hasFutureCausalChartSegment_of_closed_chart_interval {g : Field (M := M)}
    (hL : HasLorentzSignature g) (o : TimeOrientation g) (γ : ℝ → M)
    (c : M) (x n : E) {r R a b : ℝ} (hab : a < b) (hRad : r < R)
    (hTarget : Metric.closedBall x R ⊆ (chartAt E c).target)
    (hn : ∀ z ∈ Metric.closedBall x R, coordinateBilinear g c z n n < 0)
    (hnT : ∀ z ∈ Metric.closedBall x R,
      coordinateBilinear g c z n (ChartVectorField.coordinateVector o.vector c z) < 0)
    (hγ : ContMDiffOn 𝓘(ℝ) Model 1 γ (Icc a b))
    (hMap : MapsTo γ (Icc a b) (chartAt E c).source)
    (hImage : ∀ t ∈ Icc a b, chartAt E c (γ t) ∈ Metric.closedBall x r)
    (hFuture : ∀ t ∈ Icc a b, ∃ v : TangentSpace Model (γ t),
      HasMFDerivWithinAt 𝓘(ℝ) Model γ (Icc a b) t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
      g (γ t) v v ≤ 0 ∧ g (γ t) (o.vector (γ t)) v ≤ 0) : HasFutureCausalChartSegment o (γ a) (γ b) := by
  let e := chartAt E c
  let y := e ∘ γ
  have hY : ContDiffOn ℝ 1 y (Icc a b) :=
    ((contMDiffOn_chart (I := Model)).comp hγ hMap).contDiffOn
  let w (t : ℝ) := derivWithin y (Icc a b) t
  have hBounds (t : ℝ) (ht : t ∈ Icc a b) : HasDerivWithinAt y (w t) (Icc a b) t ∧
      coordinateBilinear g c (y t) (w t) (w t) ≤ 0 ∧
      coordinateBilinear g c (y t) n (w t) ≤ 0 := by
    obtain ⟨v, hDeriv, hvv, hTv⟩ := hFuture t ht
    have htS := hMap ht
    have htT := e.mapsTo htS
    let F := (trivializationAt E (TangentSpace Model) c).continuousLinearEquivAt ℝ (γ t) htS
    let v₀ := F v
    have hFrame : tangentFrame c (γ t) v₀ = v := F.symm_apply_apply v
    have hC := ((mdifferentiable_chart (I := Model) c).mdifferentiableAt htS).hasMFDerivAt
    have hD := (hC.comp_hasMFDerivWithinAt t hDeriv).hasFDerivWithinAt
    have hValue : (mfderiv Model Model e (γ t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight v) =
        (1 : ℝ →L[ℝ] ℝ).smulRight v₀ := by
      apply ContinuousLinearMap.ext
      intro z
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, map_smul]
      rw [← hFrame, IntrinsicCov2.mfderiv_chart_tangentFrame c (γ t) htS]
      rfl
    rw [hValue] at hD
    have hCoord := hD.hasDerivWithinAt
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul] at hCoord
    have hEq : w t = v₀ := hCoord.derivWithin ((uniqueDiffOn_Icc hab) t ht)
    have hInv : e.symm (y t) = γ t := e.left_inv htS
    have hQ : coordinateBilinear g c (y t) (w t) (w t) ≤ 0 := by
      rw [hEq]
      change g (e.symm (y t)) (tangentFrame c (e.symm (y t)) v₀) (tangentFrame c (e.symm (y t)) v₀) ≤ 0
      rw [hInv, hFrame]
      exact hvv
    have hT : coordinateBilinear g c (y t) (ChartVectorField.coordinateVector o.vector c (y t)) (w t) ≤ 0 := by
      rw [hEq]
      change g (e.symm (y t)) (tangentFrame c (e.symm (y t)) (ChartVectorField.coordinateVector o.vector c (y t)))
        (tangentFrame c (e.symm (y t)) v₀) ≤ 0
      have hVector : tangentFrame c (e.symm (y t)) (ChartVectorField.coordinateVector o.vector c (y t)) =
          o.vector (e.symm (y t)) := ChartVectorField.tangentFrame_coordinateVector o.vector c (show y t ∈ e.target from htT)
      rw [hVector, hInv, hFrame]
      exact hTv
    have hyR := Metric.closedBall_subset_closedBall hRad.le (hImage t ht)
    have hSign : coordinateBilinear g c (y t) (ChartVectorField.coordinateVector o.vector c (y t)) n < 0 := by
      rw [(coordinateBilinear_symmetric g hL.isSymmetric c (y t)).eq]
      exact hnT _ hyR
    exact ⟨hEq.symm ▸ hCoord, hQ, chart_causal_weak_sign_change hL c htT
      (coordinate_timeOrientation_timelike o c htT) (hn _ hyR) hSign hQ hT⟩
  obtain ⟨Y, hEq, hD⟩ := exists_coordinate_extension_with_derivatives y w hab (fun t ht => (hBounds t ht).1)
  have hV : ContinuousOn (fun t => ‖w t‖) (Icc a b) := (hY.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl).norm
  obtain ⟨V, hV⟩ := isCompact_Icc.bddAbove_image hV
  refine ⟨c, x, n, r, R, a, b, max V 0, Y, w,
    ?_, ?_, hab, hRad, le_max_right _ _, hTarget, hn, hnT, hY.congr hEq, ?_⟩
  · rw [hEq (left_mem_Icc.mpr hab.le)]
    exact (e.left_inv (hMap (left_mem_Icc.mpr hab.le))).symm
  · rw [hEq (right_mem_Icc.mpr hab.le)]
    exact (e.left_inv (hMap (right_mem_Icc.mpr hab.le))).symm
  intro t ht
  obtain ⟨_, hQ, hN⟩ := hBounds t ht
  rw [hEq ht]
  exact ⟨hImage t ht, hD t ht, hQ, hN, (hV (mem_image_of_mem _ ht)).trans (le_max_left _ _)⟩

private theorem chartCausalRelation_of_intrinsic_segment {g : Field (M := M)} (hg : IsSmooth g)
    (hL : HasLorentzSignature g) (o : TimeOrientation g) {p q : M}
    (h : HasIntrinsicFutureCausalSegment o p q) : (p, q) ∈ chartCausalRelation o := by
  obtain ⟨a, b, γ, hab, rfl, rfl, hγ, hFuture⟩ := h
  refine interval_relation_of_closed_local_steps (chartCausalRelation_transitive o) γ hab ?_
  intro s hs
  let c := γ s
  let e := chartAt E c
  let y := e ∘ γ
  let x := y s
  let T := ChartVectorField.coordinateVector o.vector c
  let n := T x
  have hc : c ∈ e.source := mem_chart_source E c
  have hx : x ∈ e.target := e.mapsTo hc
  have hn := coordinate_timeOrientation_timelike o c hx
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
      (hBnn.preimage_mem_nhds (Iio_mem_nhds hn))) (hBnT.preimage_mem_nhds (Iio_mem_nhds hn))
  obtain ⟨R, hR, hBall⟩ := Metric.mem_nhds_iff.mp hWindow
  have hOuter := (Metric.closedBall_subset_ball (half_lt_self hR)).trans hBall
  have hγs := hγ.continuousOn s hs
  have hys : ContinuousWithinAt y (Icc a b) s := (e.continuousAt hc).comp_continuousWithinAt hγs
  have hNear : γ ⁻¹' e.source ∩ y ⁻¹' Metric.ball x (R / 4) ∈ 𝓝[Icc a b] s :=
    inter_mem (hγs (e.open_source.mem_nhds hc))
      (hys (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by positivity))))
  obtain ⟨δ, hδ, hLoc⟩ := Metric.mem_nhdsWithin_iff.mp hNear
  have hStep {u v : ℝ} (hu : u ∈ Metric.ball s δ ∩ Icc a b) (hv : v ∈ Metric.ball s δ ∩ Icc a b)
      (huv : u ≤ v) : (γ u, γ v) ∈ chartCausalRelation o := by
    rcases eq_or_lt_of_le huv with rfl | huv
    · exact Relation.ReflTransGen.refl
    have hSub := (convex_Icc a b).ordConnected.out hu.2 hv.2
    have hSeg := (convex_ball s δ).ordConnected.out hu.1 hv.1
    refine Relation.ReflTransGen.single (Or.inr (hasFutureCausalChartSegment_of_closed_chart_interval
      hL o γ c x n (r := R / 4) (R := R / 2) huv (by linarith)
      (fun _ h => (hOuter h).1.1) (fun _ h => (hOuter h).1.2)
      (fun _ h => (hOuter h).2) (hγ.mono hSub) (fun _ h => (hLoc ⟨hSeg h, hSub h⟩).1)
      (fun _ h => Metric.ball_subset_closedBall (hLoc ⟨hSeg h, hSub h⟩).2) ?_))
    intro t ht
    obtain ⟨z, hd, hQ, hT⟩ := hFuture t (hSub ht)
    exact ⟨z, hd.mono hSub, hQ, hT⟩
  have hsBall : s ∈ Metric.ball s δ := Metric.mem_ball_self hδ
  have hBallNear : ∀ᶠ t in 𝓝[Icc a b] s, t ∈ Metric.ball s δ :=
    nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hsBall)
  filter_upwards [hBallNear, self_mem_nhdsWithin] with t ht hI
  exact ⟨hStep ⟨hsBall, hs⟩ ⟨ht, hI⟩, hStep ⟨ht, hI⟩ ⟨hsBall, hs⟩⟩

/-- Finite intrinsic future causal paths have causally related chart endpoints. -/
theorem intrinsicPiecewiseCausalRelation_subset_chartCausalRelation {g : Field (M := M)}
    (hg : IsSmooth g) (hL : HasLorentzSignature g) (o : TimeOrientation g) :
    intrinsicPiecewiseCausalRelation o ⊆ chartCausalRelation o := by
  rintro ⟨p, q⟩ hz
  change Relation.ReflTransGen (HasIntrinsicFutureCausalSegment o) p q at hz
  induction hz with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact chartCausalRelation_transitive o ih (chartCausalRelation_of_intrinsic_segment hg hL o h)

/-- The chart-generated relation is exactly the intrinsic piecewise `C¹`
future causal endpoint relation with the closed future cone. -/
theorem chartCausalRelation_eq_intrinsicPiecewiseCausalRelation {g : Field (M := M)}
    (hg : IsSmooth g) (hL : HasLorentzSignature g) (o : TimeOrientation g) :
    chartCausalRelation o = intrinsicPiecewiseCausalRelation o :=
  Subset.antisymm (chartCausalRelation_subset_intrinsicPiecewiseCausalRelation hL o)
    (intrinsicPiecewiseCausalRelation_subset_chartCausalRelation hg hL o)

end Burnett.Geometry.FiniteCausalVolume
