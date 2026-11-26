import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

section

variable {X Y V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace Y] (μ : Measure Y)

/-- Ordinary pointwise smoothness and integrable local domination of
every Fréchet jet under one fixed integral. Bounds may vary with the
order and the center. -/
structure DominatedIntegralJets (F : X → Y → V) : Prop where
  smooth : ∀ y, ContDiff ℝ ∞ (fun x => F x y)
  measurable : ∀ n x, AEStronglyMeasurable (fun y =>
    iteratedFDeriv ℝ n (fun z => F z y) x) μ
  locallyDominated : ∀ n (x : X), ∃ ε : ℝ, 0 < ε ∧ ∃ b : Y → ℝ,
    Integrable b μ ∧ ∀ x' ∈ ball x ε, ∀ y,
      ‖iteratedFDeriv ℝ n (fun z => F z y) x'‖ ≤ b y

omit [CompleteSpace V] in
private theorem dominated_integral_jet_integrable (F : X → Y → V)
    (h : DominatedIntegralJets μ F) (n : ℕ) (x : X) :
    Integrable (fun y => iteratedFDeriv ℝ n (fun z => F z y) x) μ := by
  obtain ⟨ε,εp,b,bi,bd⟩ := h.locallyDominated n x
  exact bi.mono' (h.measurable n x) (Eventually.of_forall (bd x (mem_ball_self εp)))

omit [CompleteSpace V] in
private theorem dominated_integral_jet_hasFDerivAt (F : X → Y → V)
    (h : DominatedIntegralJets μ F) (n : ℕ) (x : X) :
    HasFDerivAt (fun x' => ∫ y, iteratedFDeriv ℝ n (fun z => F z y) x' ∂μ)
      (∫ y, fderiv ℝ (iteratedFDeriv ℝ n (fun z => F z y)) x ∂μ) x := by
  let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => X) V
  have eq (y : Y) : fderiv ℝ (iteratedFDeriv ℝ n (fun z => F z y)) x =
      C (iteratedFDeriv ℝ (n+1) (fun z => F z y) x) := rfl
  have ds : AEStronglyMeasurable (fun y =>
      fderiv ℝ (iteratedFDeriv ℝ n (fun z => F z y)) x) μ := by
    simp only [eq]
    exact C.continuous.comp_aestronglyMeasurable (h.measurable (n+1) x)
  obtain ⟨ε,εp,b,bi,bd⟩ := h.locallyDominated (n+1) x
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun x' y => iteratedFDeriv ℝ n (fun z => F z y) x')
    (F' := fun x' y => fderiv ℝ (iteratedFDeriv ℝ n (fun z => F z y)) x') εp
    (Eventually.of_forall (h.measurable n)) (dominated_integral_jet_integrable μ F h n x) ds ?_ bi ?_
  · exact Eventually.of_forall fun y x' hx' => by
      rw [norm_fderiv_iteratedFDeriv]
      exact bd x' hx' y
  · refine Eventually.of_forall fun y x' _ => ?_
    have dp : (n : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (ENat.coe_lt_top n)
    exact ((h.smooth y).differentiable_iteratedFDeriv dp x').hasFDerivAt

/-- Every actual iterated Fréchet derivative commutes with the Bochner
integral under ordinary domination of the integrand's jets. -/
theorem iteratedFDeriv_integral_eq_of_dominated_jets (F : X → Y → V)
    (h : DominatedIntegralJets μ F) (n : ℕ) (x : X) :
    iteratedFDeriv ℝ n (fun x' => ∫ y, F x' y ∂μ) x =
      ∫ y, iteratedFDeriv ℝ n (fun z => F z y) x ∂μ := by
  induction n generalizing x with
  | zero =>
    let C := (continuousMultilinearCurryFin0 ℝ X V).symm
    exact (C.toLinearIsometry.integral_comp_comm (fun y => F x y)).symm
  | succ n ih =>
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => X) V
    have all : iteratedFDeriv ℝ n (fun x' => ∫ y, F x' y ∂μ) =
        (fun x' => ∫ y, iteratedFDeriv ℝ n (fun z => F z y) x' ∂μ) := funext ih
    have z := dominated_integral_jet_hasFDerivAt μ F h n x
    rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,all,z.fderiv]
    have D : (fun y => fderiv ℝ (iteratedFDeriv ℝ n (fun z => F z y)) x) =
        (fun y => C (iteratedFDeriv ℝ (n+1) (fun z => F z y) x)) := rfl
    have commute : (∫ y, C (iteratedFDeriv ℝ (n+1) (fun z => F z y) x) ∂μ) =
        C (∫ y, iteratedFDeriv ℝ (n+1) (fun z => F z y) x ∂μ) := by
      exact LinearIsometry.integral_comp_comm (𝕜 := ℝ) (μ := μ)
        (E := ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) => X) V)
        (F := X →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => X) V)
        C.toLinearIsometry (fun y => iteratedFDeriv ℝ (n+1) (fun z => F z y) x)
    rw [D,commute]
    exact C.symm_apply_apply _

/-- Smoothness of a genuine parameter integral follows from the same
local domination, with no smoothness assertion about the integral
taken as an input. -/
theorem contDiff_integral_of_dominated_jets (F : X → Y → V)
    (h : DominatedIntegralJets μ F) : ContDiff ℝ ∞ (fun x => ∫ y, F x y ∂μ) := by
  apply contDiff_of_differentiable_iteratedFDeriv
  intro n _
  have eq : iteratedFDeriv ℝ n (fun x' => ∫ y, F x' y ∂μ) =
      (fun x' => ∫ y, iteratedFDeriv ℝ n (fun z => F z y) x' ∂μ) :=
    funext (iteratedFDeriv_integral_eq_of_dominated_jets μ F h n)
  rw [eq]
  exact fun x => (dominated_integral_jet_hasFDerivAt μ F h n x).differentiableAt

end

end Burnett.A03
