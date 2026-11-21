import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function Metric
open scoped ContDiff

/-- A series with summable derivative bounds on each unit ball is smooth,
and every jet is the pointwise sum of the jets of the summands. -/
theorem contDiff_tsum_and_jets_of_locally_summable_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : ℕ → E → F) (hs : ∀ i, ContDiff ℝ ∞ (f i))
    (hBound : ∀ (n : ℕ) (x : E), ∃ v : ℕ → ℝ, Summable v ∧
      ∀ i y, y ∈ ball x 1 → ‖iteratedFDeriv ℝ n (f i) y‖ ≤ v i) :
    ContDiff ℝ ∞ (fun x => ∑' i, f i x) ∧ ∀ (n : ℕ) (x : E),
      iteratedFDeriv ℝ n (fun y => ∑' i, f i y) x = ∑' i, iteratedFDeriv ℝ n (f i) x := by
  let J (n : ℕ) (x : E) := ∑' i, iteratedFDeriv ℝ n (f i) x
  have hSummable (n : ℕ) (x : E) : Summable (fun i => iteratedFDeriv ℝ n (f i) x) := by
    obtain ⟨v, hV, h⟩ := hBound n x
    exact .of_norm_bounded hV (fun i => h i x (mem_ball_self zero_lt_one))
  have hDeriv (n : ℕ) (x : E) :
      HasFDerivAt (J n) (∑' i, fderiv ℝ (iteratedFDeriv ℝ n (f i)) x) x := by
    obtain ⟨v, hV, hb⟩ := hBound (n+1) x
    have hX : x ∈ ball x 1 := mem_ball_self zero_lt_one
    refine hasFDerivAt_tsum_of_isPreconnected hV isOpen_ball (convex_ball x 1).isPreconnected
      (fun i y _ => ((hs i).differentiable_iteratedFDeriv (m := n)
        (by exact_mod_cast ENat.coe_lt_top n) y).hasFDerivAt)
      (fun i y hy => ?_) hX (hSummable n x) hX
    rw [fderiv_iteratedFDeriv, comp_apply, LinearIsometryEquiv.norm_map]
    exact hb i y hy
  have hJet (n : ℕ) : iteratedFDeriv ℝ n (fun y => ∑' i, f i y) = J n := by
    induction n with
    | zero =>
      ext1 x
      simp only [J, iteratedFDeriv_zero_eq_comp, comp_apply]
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
    | succ n ih =>
      ext1 x
      rw [iteratedFDeriv_succ_eq_comp_left, comp_apply, ih, (hDeriv n x).fderiv]
      let equiv := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).symm.toContinuousLinearEquiv
      simpa only [J, iteratedFDeriv_succ_eq_comp_left, comp_apply] using
        (equiv.map_tsum (f := fun i => fderiv ℝ (iteratedFDeriv ℝ n (f i)) x))
  refine ⟨?_, fun n x => congrFun (hJet n) x⟩
  apply contDiff_of_differentiable_iteratedFDeriv
  intro n _
  rw [hJet n]
  exact fun x => (hDeriv n x).differentiableAt

end Burnett.Analysis.CarlesonEmbedding
