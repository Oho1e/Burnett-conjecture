import Burnett.Analysis.AllScaleTransfer.RadianTrilinearChange
import Mathlib.LinearAlgebra.Multilinear.Basic

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.A05

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (Space radianTrilinearWeight radianTrilinearForm
  integrable_radianTrilinearWeight_of_bounded)
open scoped FourierTransform BigOperators

private def radianSchwartzEval (p : Space) : SchwartzMap Space ℂ →ₗ[ℂ] ℂ where
  toFun f := SchwartzMap.fourierTransformCLM ℂ f (tau⁻¹ • p)
  map_add' f g := by rw [map_add, SchwartzMap.add_apply]
  map_smul' c f := by
    rw [map_smul (SchwartzMap.fourierTransformCLM ℂ) c f, SchwartzMap.smul_apply]
    rfl

private theorem radianSchwartzEval_eq (f : SchwartzMap Space ℂ) (p : Space) :
    radianSchwartzEval p f = radianFourier f p := by
  have hτ : tau ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
  change SchwartzMap.fourierTransformCLM ℂ f (tau⁻¹ • p) = _
  rw [SchwartzMap.fourierTransformCLM_apply, ← radianFourier_scaled, smul_smul,
    mul_inv_cancel₀ hτ, one_smul]

private def radianSchwartzWeight (m : Joint → ℂ) (p : Joint) :
    MultilinearMap ℂ (fun _ : Fin 3 => SchwartzMap Space ℂ) ℂ :=
  m p • (MultilinearMap.mkPiAlgebra ℂ (Fin 3) ℂ).compLinearMap
    (fun i => radianSchwartzEval (![p.1, p.2, -(p.1+p.2)] i))

private theorem radianSchwartzWeight_eq (m : Joint → ℂ) (p : Joint)
    (f : Fin 3 → SchwartzMap Space ℂ) :
    radianSchwartzWeight m p f = radianTrilinearWeight m (f 0) (f 1) (f 2) p := by
  simp [radianSchwartzWeight, MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_succ,
    radianSchwartzEval_eq, radianTrilinearWeight, radianWeight, mul_assoc]

/-- The original radian Fourier form on Schwartz factors is complex-linear in
each of the three signed-frequency slots. -/
def radianSchwartzTrilinear (m : Joint → ℂ) (hm : AEStronglyMeasurable m volume)
    (H : ℝ) (hBound : ∀ p, ‖m p‖ ≤ H) :
    MultilinearMap ℂ (fun _ : Fin 3 => SchwartzMap Space ℂ) ℂ where
  toFun f := radianTrilinearForm m (f 0) (f 1) (f 2)
  map_update_add' f i a b := by
    classical
    let weight (g : Fin 3 → SchwartzMap Space ℂ) := radianTrilinearWeight m (g 0) (g 1) (g 2)
    have int (g : Fin 3 → SchwartzMap Space ℂ) : Integrable (weight g) :=
      integrable_radianTrilinearWeight_of_bounded m hm H hBound (g 0) (g 1) (g 2)
    have eq : weight (Function.update f i (a+b)) =
        fun p => weight (Function.update f i a) p + weight (Function.update f i b) p := by
      funext p
      simpa only [radianSchwartzWeight_eq, weight] using (radianSchwartzWeight m p).map_update_add f i a b
    change (tau^8)⁻¹ • (∫ p, weight (Function.update f i (a+b)) p) =
      (tau^8)⁻¹ • (∫ p, weight (Function.update f i a) p) +
        (tau^8)⁻¹ • (∫ p, weight (Function.update f i b) p)
    rw [eq, integral_add (int _) (int _), smul_add]
  map_update_smul' f i c a := by
    classical
    let weight (g : Fin 3 → SchwartzMap Space ℂ) := radianTrilinearWeight m (g 0) (g 1) (g 2)
    have eq : weight (Function.update f i (c • a)) =
        fun p => c • weight (Function.update f i a) p := by
      funext p
      simpa only [radianSchwartzWeight_eq, weight] using (radianSchwartzWeight m p).map_update_smul f i c a
    change (tau^8)⁻¹ • (∫ p, weight (Function.update f i (c • a)) p) =
      c • ((tau^8)⁻¹ • (∫ p, weight (Function.update f i a) p))
    rw [eq, integral_smul, smul_comm]

@[simp] theorem radianSchwartzTrilinear_apply (m : Joint → ℂ)
    (hm : AEStronglyMeasurable m volume) (H : ℝ) (hBound : ∀ p, ‖m p‖ ≤ H)
    (f : Fin 3 → SchwartzMap Space ℂ) :
    radianSchwartzTrilinear m hm H hBound f = radianTrilinearForm m (f 0) (f 1) (f 2) := rfl

end Burnett.A05
