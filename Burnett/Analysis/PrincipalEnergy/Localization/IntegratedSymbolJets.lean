import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Metric
open scoped ContDiff Topology

/-- Smooth parameter integrals with an integrable majorant for each jet on
each parameter ball. The derivatives are the integrals of the actual jets. -/
theorem contDiff_integral_of_locally_dominated_jets {A X F : Type*} [MeasurableSpace A]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (μ : Measure A) (u : A → X → F)
    (smooth : ∀ a, ContDiff ℝ ∞ (u a))
    (measurable : ∀ (n : ℕ) x, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (u a) x) μ)
    (dominated : ∀ (n : ℕ) (x : X), ∃ B : A → ℝ, Integrable B μ ∧
      ∀ a y, y ∈ ball x 1 → ‖iteratedFDeriv ℝ n (u a) y‖ ≤ B a) :
    ContDiff ℝ ∞ (fun x => ∫ a, u a x ∂μ) ∧ ∀ (n : ℕ) x,
      iteratedFDeriv ℝ n (fun y => ∫ a, u a y ∂μ) x = ∫ a, iteratedFDeriv ℝ n (u a) x ∂μ := by
  let p (x : X) (n : ℕ) := ∫ a, iteratedFDeriv ℝ n (u a) x ∂μ
  have hInt (n : ℕ) (x : X) : Integrable (fun a => iteratedFDeriv ℝ n (u a) x) μ := by
    obtain ⟨B, hB, bound⟩ := dominated n x
    exact hB.mono' (measurable n x) (Eventually.of_forall fun a => bound a x (mem_ball_self zero_lt_one))
  have derivative (n : ℕ) (x : X) : HasFDerivAt (fun y => p y n) (p x (n + 1)).curryLeft x := by
    letI : NormedAddCommGroup (X →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => X) F) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ (X →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => X) F) :=
      ContinuousLinearMap.toNormedSpace
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => X) F
    let L : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => X) F →L[ℝ]
        (X →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => X) F) :=
      C.toContinuousLinearEquiv.toContinuousLinearMap
    let D (y : X) (a : A) := C (iteratedFDeriv ℝ (n + 1) (u a) y)
    have hD (y : X) (a : A) : D y a = fderiv ℝ (iteratedFDeriv ℝ n (u a)) y := by
      dsimp only [D]
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      exact C.apply_symm_apply _
    have hMeas : AEStronglyMeasurable (D x) μ :=
      C.continuous.comp_aestronglyMeasurable (measurable (n + 1) x)
    obtain ⟨B, hB, hBound⟩ := dominated (n + 1) x
    have hNorm : ∀ᵐ a ∂μ, ∀ y ∈ ball x 1, ‖D y a‖ ≤ B a :=
      Eventually.of_forall fun a y hy => by simpa only [D, LinearIsometryEquiv.norm_map] using hBound a y hy
    have hDiff : ∀ᵐ a ∂μ, ∀ y ∈ ball x 1,
        HasFDerivAt (iteratedFDeriv ℝ n (u a)) (D y a) y := Eventually.of_forall fun a y _ => by
      rw [hD]
      have hOrder : (n : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.coe_lt_top n
      exact ((smooth a).contDiffAt.differentiableAt_iteratedFDeriv hOrder).hasFDerivAt
    have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (show (0 : ℝ) < 1 from zero_lt_one) (Eventually.of_forall (measurable n))
      (hInt n x) hMeas hNorm hB hDiff
    have commutes : (∫ a, D x a ∂μ) = (p x (n + 1)).curryLeft := by
      change (∫ a, L (iteratedFDeriv ℝ (n + 1) (u a) x) ∂μ) =
        L (∫ a, iteratedFDeriv ℝ (n + 1) (u a) x ∂μ)
      exact ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (μ := μ)
        (Fₗ := X →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => X) F) L (hInt (n + 1) x)
    rwa [commutes] at h
  have zeroJet (x : X) : (p x 0).curry0 = ∫ a, u a x ∂μ := by
    let C := continuousMultilinearCurryFin0 ℝ X F
    let L := C.toContinuousLinearEquiv.toContinuousLinearMap
    change L (∫ a, iteratedFDeriv ℝ 0 (u a) x ∂μ) = _
    rw [← L.integral_comp_comm (hInt 0 x)]
    apply integral_congr_ae
    filter_upwards with a
    change C (iteratedFDeriv ℝ 0 (u a) x) = _
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact C.apply_symm_apply _
  have series : HasFTaylorSeriesUpTo ∞ (fun x => ∫ a, u a x ∂μ) p :=
    ⟨zeroJet, fun n _ => derivative n, fun n _ =>
      continuous_iff_continuousAt.mpr fun x => (derivative n x).continuousAt⟩
  exact ⟨series.contDiff, fun n x =>
    (series.eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x).symm⟩

end Burnett.Analysis.CarlesonEmbedding
