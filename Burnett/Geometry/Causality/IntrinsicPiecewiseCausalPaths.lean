import Burnett.Geometry.Causality.IntrinsicCausalChartSegments
import Mathlib.Analysis.Calculus.Deriv.AffineMap

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section
namespace Burnett.Geometry.FiniteCausalVolume

open Set Bundle
open scoped ContDiff Manifold
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.CotangentHamiltonCauchySlice

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- A genuine future causal `C¹` segment on a finite closed interval.
The intrinsic derivative at an endpoint is taken from within the interval.
The closed future cone permits zero velocity. -/
def HasIntrinsicFutureCausalSegment {g : Field (M := M)} (o : TimeOrientation g) (p q : M) : Prop :=
  ∃ (a b : ℝ) (γ : ℝ → M), a < b ∧ γ a = p ∧ γ b = q ∧
    ContMDiffOn 𝓘(ℝ) Model 1 γ (Icc a b) ∧
    ∀ t ∈ Icc a b, ∃ v : TangentSpace Model (γ t),
      HasMFDerivWithinAt 𝓘(ℝ) Model γ (Icc a b) t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
      g (γ t) v v ≤ 0 ∧ g (γ t) (o.vector (γ t)) v ≤ 0

/-- The endpoint relation of finitely concatenated intrinsic future causal segments. -/
def intrinsicPiecewiseCausalRelation {g : Field (M := M)} (o : TimeOrientation g) : Set (M × M) :=
  {z | Relation.ReflTransGen (HasIntrinsicFutureCausalSegment o) z.1 z.2}

theorem coordinate_timeOrientation_timelike {g : Field (M := M)} (o : TimeOrientation g)
    (c : M) {y : E} (hy : y ∈ (chartAt E c).target) :
    let T := ChartVectorField.coordinateVector o.vector c y
    coordinateBilinear g c y T T < 0 := by
  let x := (chartAt E c).symm y
  let T := ChartVectorField.coordinateVector o.vector c y
  change g x (tangentFrame c x T) (tangentFrame c x T) < 0
  rw [ChartVectorField.tangentFrame_coordinateVector o.vector c hy]
  exact o.timelike x

/-- Two future timelike reference vectors determine the same closed causal half-cone. -/
theorem chart_causal_weak_sign_change {g : Field (M := M)} (hL : HasLorentzSignature g)
    (c : M) {y n w v : E} (hy : y ∈ (chartAt E c).target)
    (hn : coordinateBilinear g c y n n < 0) (hw : coordinateBilinear g c y w w < 0)
    (hnw : coordinateBilinear g c y n w < 0)
    (hvv : coordinateBilinear g c y v v ≤ 0) (hnv : coordinateBilinear g c y n v ≤ 0) :
    coordinateBilinear g c y w v ≤ 0 := by
  by_cases hzero : v = 0
  · simp [hzero]
  let x := (chartAt E c).symm y
  let F := tangentFrame c x
  let B : LinearMap.BilinForm ℝ (TangentSpace Model x) :=
    LinearMap.mk₂ ℝ (fun u z => g x u z) (by intros; simp [map_add]) (by intros; simp [map_smul])
      (by intros; simp [map_add]) (by intros; simp [map_smul])
  have hF : F v ≠ 0 := by
    intro hv
    exact hzero ((tangentFrame_injective c x ((chartAt E c).symm_mapsTo hy)) (hv.trans (map_zero F).symm))
  have hne : coordinateBilinear g c y n v ≠ 0 := by
    intro he
    obtain ⟨b, hb⟩ := hL x
    exact (not_lt_of_ge (show B (F v) (F v) ≤ 0 from hvv))
      (positive_of_timelike_orthogonal B b hb (show B (F n) (F n) < 0 from hn) hF he)
  exact (chart_causal_sign_change hL c hy hn hw hnw hzero hvv (lt_of_le_of_ne hnv hne)).le

private theorem intrinsicFutureCausalSegment_of_coordinate {g : Field (M := M)}
    (o : TimeOrientation g) (c : M) (y v : ℝ → E) {a b : ℝ} (hab : a < b)
    (hY : ContDiffOn ℝ 1 y (Icc a b))
    (hPath : ∀ t ∈ Icc a b, y t ∈ (chartAt E c).target ∧
      HasDerivWithinAt y (v t) (Icc a b) t ∧
      coordinateBilinear g c (y t) (v t) (v t) ≤ 0 ∧
      coordinateBilinear g c (y t) (ChartVectorField.coordinateVector o.vector c (y t)) (v t) ≤ 0) :
    HasIntrinsicFutureCausalSegment o ((chartAt E c).symm (y a)) ((chartAt E c).symm (y b)) := by
  let e := chartAt E c
  let γ := e.symm ∘ y
  refine ⟨a, b, γ, hab, rfl, rfl, ?_, ?_⟩
  · exact (contMDiffOn_chart_symm (I := Model)).comp hY.contMDiffOn (fun t ht => (hPath t ht).1)
  intro t ht
  obtain ⟨hy, hd, hQ, hT⟩ := hPath t ht
  let w := tangentFrame c (γ t) (v t)
  have hInv := ((mdifferentiable_chart (I := Model) c).mdifferentiableAt_symm hy).hasMFDerivAt
  have hDeriv := hInv.comp_hasMFDerivWithinAt t hd.hasFDerivWithinAt.hasMFDerivWithinAt
  have hFrame := ChartDifferential.tangentFrame_eq_mfderiv_symm c (e.symm (y t)) (e.symm_mapsTo hy)
  rw [e.right_inv hy] at hFrame
  have hLinear : (mfderiv Model Model e.symm (y t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (v t)) =
      (1 : ℝ →L[ℝ] ℝ).smulRight w := by
    rw [← hFrame]
    apply ContinuousLinearMap.ext
    intro k
    exact map_smul (tangentFrame c (e.symm (y t))) k (v t)
  rw [hLinear] at hDeriv
  refine ⟨w, hDeriv, hQ, ?_⟩
  change g (γ t) (tangentFrame c (γ t) (ChartVectorField.coordinateVector o.vector c (y t))) w ≤ 0 at hT
  have hVector : tangentFrame c (γ t) (ChartVectorField.coordinateVector o.vector c (y t)) = o.vector (γ t) :=
    ChartVectorField.tangentFrame_coordinateVector o.vector c hy
  rw [hVector] at hT
  exact hT

private theorem intrinsicFutureCausalSegment_of_chart {g : Field (M := M)}
    (hL : HasLorentzSignature g) (o : TimeOrientation g) {p q : M}
    (h : HasFutureCausalChartSegment o p q) : HasIntrinsicFutureCausalSegment o p q := by
  obtain ⟨c, x, n, r, R, a, b, _, y, v, rfl, rfl, hab, hRad, _, hTarget, hn, hnT, hY, hPath⟩ := h
  apply intrinsicFutureCausalSegment_of_coordinate o c y v hab hY
  intro t ht
  obtain ⟨hy, hd, hQ, hN, _⟩ := hPath t ht
  have hyR := Metric.closedBall_subset_closedBall hRad.le hy
  have hyT := hTarget hyR
  exact ⟨hyT, hd.hasDerivWithinAt, hQ,
    chart_causal_weak_sign_change hL c hyT (hn _ hyR) (coordinate_timeOrientation_timelike o c hyT)
      (hnT _ hyR) hQ hN⟩

private theorem intrinsicFutureCausalSegment_of_timelikeChord {g : Field (M := M)}
    (o : TimeOrientation g) {p q : M} (h : FutureTimelikeChartChord o p q) :
    HasIntrinsicFutureCausalSegment o p q := by
  obtain ⟨c, hp, hq, hChord⟩ := h
  let e := chartAt E c
  let y : ℝ → E := AffineMap.lineMap (e p) (e q)
  let v := fun _ : ℝ => e q - e p
  have hY : ContDiff ℝ 1 y := by
    change ContDiff ℝ 1 (fun t : ℝ => AffineMap.lineMap (e p) (e q) t)
    simp only [AffineMap.lineMap_apply_module']
    exact (contDiff_id.smul contDiff_const).add contDiff_const
  have h₀ : e.symm (y 0) = p := by simpa only [y, AffineMap.lineMap_apply_zero] using e.left_inv hp
  have h₁ : e.symm (y 1) = q := by simpa only [y, AffineMap.lineMap_apply_one] using e.left_inv hq
  rw [← h₀, ← h₁]
  apply intrinsicFutureCausalSegment_of_coordinate o c y v zero_lt_one hY.contDiffOn
  intro t ht
  have hv := hChord t ht
  exact ⟨hv.1, AffineMap.hasDerivWithinAt_lineMap, hv.2.1.le, hv.2.2.le⟩

/-- Each generated chart-causal connection is a finite concatenation of genuine
intrinsic future causal segments with one-sided endpoint derivatives. -/
theorem chartCausalRelation_subset_intrinsicPiecewiseCausalRelation {g : Field (M := M)}
    (hL : HasLorentzSignature g) (o : TimeOrientation g) :
    chartCausalRelation o ⊆ intrinsicPiecewiseCausalRelation o := by
  rintro ⟨p, q⟩ hz
  change Relation.ReflTransGen _ p q at hz
  change Relation.ReflTransGen (HasIntrinsicFutureCausalSegment o) p q
  induction hz with
  | refl => exact Relation.ReflTransGen.refl
  | @tail p q _ hStep ih =>
      refine Relation.ReflTransGen.trans ih ?_
      rcases hStep with hTimelike | hCausal
      · change Relation.TransGen (FutureTimelikeChartChord o) p q at hTimelike
        induction hTimelike with
        | single h => exact Relation.ReflTransGen.single (intrinsicFutureCausalSegment_of_timelikeChord o h)
        | tail _ h ih => exact Relation.ReflTransGen.tail ih (intrinsicFutureCausalSegment_of_timelikeChord o h)
      · exact Relation.ReflTransGen.single (intrinsicFutureCausalSegment_of_chart hL o hCausal)

end Burnett.Geometry.FiniteCausalVolume
