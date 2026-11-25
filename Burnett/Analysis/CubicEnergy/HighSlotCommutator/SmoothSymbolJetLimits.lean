import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxHeartbeats 4100000

noncomputable section

namespace Burnett.A06

open Filter Metric Set
open scoped ContDiff Topology

private abbrev FrequencyPair := EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)

/-- The unweighted jets of a convergent symbol sequence still come from
one smooth symbol. The input is uniform convergence on each fixed ball
of the actual two-frequency space. -/
theorem exists_smooth_symbol_of_uniform_jet_limits
    (F : ℕ → FrequencyPair → ℂ) (smooth : ∀ k, ContDiff ℝ ∞ (F k))
    (G : ∀ n : ℕ, FrequencyPair → FrequencyPair[×n]→L[ℝ] ℂ)
    (h : ∀ (n : ℕ) (R : ℝ), TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ n (F k)) (G n) atTop (ball (0 : FrequencyPair) R)) :
    ∃ f : FrequencyPair → ℂ, ContDiff ℝ ∞ f ∧ ∀ n, G n = iteratedFDeriv ℝ n f := by
  let f : FrequencyPair → ℂ := continuousMultilinearCurryFin0 ℝ FrequencyPair ℂ ∘ G 0
  let curry (n : ℕ) := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => FrequencyPair) ℂ
  have derivatives (n : ℕ) (x : FrequencyPair) :
      HasFDerivAt (G n) (curry n (G (n+1) x)) x := by
    let R := ‖x‖ + 1
    have hx : x ∈ ball (0 : FrequencyPair) R := mem_ball_zero_iff.mpr (by dsimp [R]; linarith)
    have hlimit := (curry n).isometry.uniformContinuous.comp_tendstoUniformlyOn (h (n+1) R)
    refine hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hlimit (fun k y _ => ?_)
      (fun y hy => (h n R).tendsto_at hy) hx
    have d : Differentiable ℝ (iteratedFDeriv ℝ n (F k)) :=
      (smooth k).differentiable_iteratedFDeriv (by exact_mod_cast (show (n : ℕ∞) < ⊤ from ENat.coe_lt_top n))
    simpa only [fderiv_iteratedFDeriv,curry] using (d y).hasFDerivAt
  have jets (n : ℕ) : G n = iteratedFDeriv ℝ n f := by
    induction n with
    | zero =>
      funext x
      rw [iteratedFDeriv_zero_eq_comp,Function.comp_apply]
      change G 0 x = (continuousMultilinearCurryFin0 ℝ FrequencyPair ℂ).symm
        ((continuousMultilinearCurryFin0 ℝ FrequencyPair ℂ) (G 0 x))
      exact (LinearIsometryEquiv.symm_apply_apply _ _).symm
    | succ n ih =>
      funext x
      rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,← ih,(derivatives n x).fderiv]
      exact (LinearIsometryEquiv.symm_apply_apply (curry n) _).symm
  refine ⟨f,contDiff_of_differentiable_iteratedFDeriv ?_,jets⟩
  intro n _
  rw [← jets n]
  exact fun x => (derivatives n x).differentiableAt

end Burnett.A06
