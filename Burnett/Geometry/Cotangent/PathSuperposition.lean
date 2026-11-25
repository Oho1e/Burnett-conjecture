import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3400

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Metric Filter
open scoped ContDiff Topology

universe u

variable {T : Type*} {E F : Type u} [TopologicalSpace T] [CompactSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Postcomposition on paths with the uniform norm. -/
def pathSuperposition (f : E → F) (hf : Continuous f) (u : C(T, E)) : C(T, F) :=
  (⟨f, hf⟩ : C(E, F)).comp u

private def pathOperatorLinear (A : C(T, E →L[ℝ] F)) : C(T, E) →ₗ[ℝ] C(T, F) where
  toFun u := ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩
  map_add' u v := by
    ext t
    exact map_add (A t) (u t) (v t)
  map_smul' r u := by
    ext t
    exact map_smul (A t) r (u t)

private theorem pathOperatorLinear_le (A : C(T, E →L[ℝ] F)) (u : C(T, E)) :
    ‖pathOperatorLinear A u‖ ≤ ‖A‖ * ‖u‖ := by
  apply (ContinuousMap.norm_le (pathOperatorLinear A u) (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact ((A t).le_opNorm (u t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
      (norm_nonneg (u t)) (norm_nonneg A))

/-- A continuous path of operators acts pointwise on the path space. -/
def pathOperator (A : C(T, E →L[ℝ] F)) : C(T, E) →L[ℝ] C(T, F) :=
  (pathOperatorLinear A).mkContinuous ‖A‖ (pathOperatorLinear_le A)

theorem pathOperator_apply (A : C(T, E →L[ℝ] F)) (u : C(T, E)) (t : T) :
    pathOperator A u t = A t (u t) := rfl

private theorem norm_pathOperator_le (A : C(T, E →L[ℝ] F)) : ‖pathOperator A‖ ≤ ‖A‖ :=
  (pathOperatorLinear A).mkContinuous_norm_le (norm_nonneg A) (pathOperatorLinear_le A)

private def pathOperatorLift : C(T, E →L[ℝ] F) →L[ℝ] (C(T, E) →L[ℝ] C(T, F)) := by
  let Q : C(T, E →L[ℝ] F) →ₗ[ℝ] (C(T, E) →L[ℝ] C(T, F)) :=
    { toFun := pathOperator
      map_add' := by
        intro A B
        ext u t
        exact rfl
      map_smul' := by
        intro a A
        ext u t
        exact rfl }
  have hQ (A : C(T, E →L[ℝ] F)) : ‖Q A‖ ≤ (1 : ℝ) * ‖A‖ := by
    change ‖pathOperator A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using norm_pathOperator_le A
  refine ⟨Q, ?_⟩
  exact AddMonoidHomClass.continuous_of_bound Q 1 hQ

private theorem uniform_first_order_remainder [ProperSpace E] (f : E → F) (L : E → E →L[ℝ] F)
    (hDiff : ∀ x, HasFDerivAt f (L x) x) (hL : Continuous L)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : E, ‖x‖ ≤ R → ∀ h : E, ‖h‖ < δ →
      ‖f (x + h) - f x - L x h‖ ≤ ε * ‖h‖ := by
  let K := closedBall (0 : E) (R + 1)
  have hUniform : UniformContinuousOn L K :=
    (isCompact_closedBall _ _).uniformContinuousOn_of_continuous hL.continuousOn
  obtain ⟨d, hd, hUC⟩ := Metric.uniformContinuousOn_iff.mp hUniform ε hε
  let δ := min (d / 2) 1
  have hδ : 0 < δ := lt_min (by linarith) zero_lt_one
  have hδd : δ < d := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro x hx h hh
  have hxK : x ∈ K := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hBall : closedBall x δ ⊆ K := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith [hy.trans (min_le_right (d / 2) 1)]
  let ψ (y : E) := f y - L x y
  have dψ (y : E) : HasFDerivAt ψ (L y - L x) y :=
    (hDiff y).sub (L x).hasFDerivAt
  have hBound (y : E) (hy : y ∈ closedBall x δ) : ‖fderiv ℝ ψ y‖ ≤ ε := by
    rw [(dψ y).fderiv]
    have hyδ : dist y x < d := (mem_closedBall.mp hy).trans_lt hδd
    exact (by simpa only [dist_eq_norm] using (hUC y (hBall hy) x hxK hyδ).le)
  have hxδ : x ∈ closedBall x δ := mem_closedBall_self hδ.le
  have hxh : x + h ∈ closedBall x δ := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hh.le
  have hMV := (convex_closedBall x δ).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (dψ y).differentiableAt) hBound hxδ hxh
  have hEq : ψ (x + h) - ψ x = f (x + h) - f x - L x h := by
    simp only [ψ, map_add]
    abel
  rw [hEq, add_sub_cancel_left] at hMV
  exact hMV

theorem hasFDerivAt_pathSuperposition [ProperSpace E] (f : E → F) (hf : Continuous f)
    (L : E → E →L[ℝ] F) (hDiff : ∀ x, HasFDerivAt f (L x) x) (hL : Continuous L)
    (u : C(T, E)) :
    HasFDerivAt (pathSuperposition f hf) (pathOperator (pathSuperposition L hL u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, localBound⟩ := uniform_first_order_remainder f L hDiff hL ‖u‖ hε
  filter_upwards [Metric.ball_mem_nhds (0 : C(T, E)) hδ] with v hv
  have hv' : ‖v‖ < δ := by simpa only [mem_ball, dist_zero_right] using hv
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg v))).mpr
  intro t
  change ‖f (u t + v t) - f (u t) - L (u t) (v t)‖ ≤ ε * ‖v‖
  exact (localBound (u t) (u.norm_coe_le_norm t) (v t) ((v.norm_coe_le_norm t).trans_lt hv')).trans
    (mul_le_mul_of_nonneg_left (v.norm_coe_le_norm t) hε.le)

private theorem contDiff_pathSuperposition_nat [ProperSpace E] (n : ℕ)
    (f : E → F) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ n (pathSuperposition (T := T) f hf.continuous) := by
  induction n generalizing F with
  | zero =>
    have hd := contDiff_infty_iff_fderiv.mp hf
    apply contDiff_zero.mpr
    rw [continuous_iff_continuousAt]
    intro u
    exact (hasFDerivAt_pathSuperposition f hf.continuous _
      (fun x => (hd.1 x).hasFDerivAt) hd.2.continuous u).continuousAt
  | succ n ih =>
    have hd := contDiff_infty_iff_fderiv.mp hf
    have hDerivative (u : C(T, E)) := hasFDerivAt_pathSuperposition f hf.continuous _
      (fun x => (hd.1 x).hasFDerivAt) hd.2.continuous u
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun u => (hDerivative u).differentiableAt, by simp, ?_⟩
    have hEq : fderiv ℝ (pathSuperposition (T := T) f hf.continuous) =
        (pathOperatorLift (T := T) (E := E) (F := F) : _ → _) ∘
          pathSuperposition (fderiv ℝ f) hd.2.continuous := by
      funext u
      change _ = pathOperator (pathSuperposition (fderiv ℝ f) hd.2.continuous u)
      exact (hDerivative u).fderiv
    rw [hEq]
    exact (pathOperatorLift (T := T) (E := E) (F := F)).contDiff.comp (ih _ hd.2)

/-- Smooth changes of the vector field value induce genuinely smooth maps on
short continuous paths. This supplies the nonlinear Picard residual input. -/
theorem contDiff_pathSuperposition [ProperSpace E] (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (pathSuperposition (T := T) f hf.continuous) :=
  contDiff_infty.mpr fun n => contDiff_pathSuperposition_nat n f hf

end Burnett.Geometry.CotangentHamiltonInitialFamily
