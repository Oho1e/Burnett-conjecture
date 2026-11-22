import Burnett.Analysis.GaugeProjection.GaugeProjectionLp
import Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter
open Burnett.A02.FrequencySplit (E)
open scoped ENNReal BigOperators Topology

/-- The full matrix norm uses the fixed maximum norm on the coordinate entries. -/
def projectionMatrixLpNorm (p : ℝ) (w : ProjectionSchwartzMatrix) : ℝ≥0∞ :=
  eLpNorm (fun x : E => fun i j => w i j x) (ENNReal.ofReal p) volume

private theorem entry_norm_le_matrix (H : Fin 4 → Fin 4 → ℂ) (i j : Fin 4) :
    ‖H i j‖ ≤ ‖H‖ :=
  (norm_le_pi_norm (H i) j).trans (norm_le_pi_norm H i)

private theorem norm_matrix_le_sum (H : Fin 4 → Fin 4 → ℂ) :
    ‖H‖ ≤ ∑ i, ∑ j, ‖H i j‖ := by
  have hnonneg : 0 ≤ ∑ i, ∑ j, ‖H i j‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg hnonneg).2 (fun i =>
    (pi_norm_le_iff_of_nonneg hnonneg).2 fun j => ?_)
  exact (Finset.single_le_sum (f := fun j => ‖H i j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖H i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))

private theorem eLpNorm_double_sum_le {F : Type*} [NormedAddCommGroup F]
    (q : ℝ≥0∞) (hq : 1 ≤ q) (f : Fin 4 → Fin 4 → E → F)
    (hf : ∀ i j, AEStronglyMeasurable (f i j) volume) :
    eLpNorm (fun x => ∑ i, ∑ j, f i j x) q volume ≤
      ∑ i, ∑ j, eLpNorm (f i j) q volume := by
  have heq : (fun x => ∑ i, ∑ j, f i j x) = ∑ i, ∑ j, f i j := by
    funext x
    simp only [Finset.sum_apply]
  rw [heq]
  refine (eLpNorm_sum_le (fun i _ => Finset.aestronglyMeasurable_sum _ fun j _ => hf i j) hq).trans ?_
  exact Finset.sum_le_sum (fun i _ => eLpNorm_sum_le (fun j _ => hf i j) hq)

private theorem projectionMatrixLpNorm_le_sum (p : ℝ) (hp : 1 ≤ ENNReal.ofReal p)
    (w : ProjectionSchwartzMatrix) :
    projectionMatrixLpNorm p w ≤
      ∑ i, ∑ j, eLpNorm (w i j : E → ℂ) (ENNReal.ofReal p) volume := by
  calc
    _ ≤ eLpNorm (fun x => ∑ i, ∑ j, ‖w i j x‖) (ENNReal.ofReal p) volume :=
      eLpNorm_mono_real (fun x => norm_matrix_le_sum (fun i j => w i j x))
    _ ≤ ∑ i, ∑ j, eLpNorm (fun x => ‖w i j x‖) (ENNReal.ofReal p) volume :=
      eLpNorm_double_sum_le _ hp _ (fun i j => (w i j).continuous.norm.aestronglyMeasurable)
    _ = _ := by simp only [eLpNorm_norm]

private theorem entry_eLpNorm_le_projectionMatrixLpNorm
    (p : ℝ) (w : ProjectionSchwartzMatrix) (i j : Fin 4) :
    eLpNorm (w i j : E → ℂ) (ENNReal.ofReal p) volume ≤ projectionMatrixLpNorm p w :=
  eLpNorm_mono (fun x => entry_norm_le_matrix (fun i j => w i j x) i j)

private theorem projectionFullSchwartz_apply (w : ProjectionSchwartzMatrix)
    (a b : Fin 4) (x : E) :
    projectionFullSchwartz w a b x = ∑ c, ∑ d, gaugeProjectionSchwartzComponent a b c d (w c d) x := by
  let eval : SchwartzMap E ℂ →+ ℂ :=
    { toFun := fun g => g x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change eval (∑ c, ∑ d, gaugeProjectionSchwartzComponent a b c d (w c d)) =
    ∑ c, ∑ d, eval (gaugeProjectionSchwartzComponent a b c d (w c d))
  simp_rw [map_sum]

/-- At every fixed finite p>1, the exact matrix multiplier controls both
the field and each of its actual coordinate derivatives. -/
theorem exists_projectionFullSchwartz_finiteLp_bounds (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ w : ProjectionSchwartzMatrix,
      projectionMatrixLpNorm p (projectionFullSchwartz w) ≤ C * projectionMatrixLpNorm p w ∧
      ∀ b : Fin 4,
        projectionMatrixLpNorm p (projectionMatrixDerivative b (projectionFullSchwartz w)) ≤
          C * projectionMatrixLpNorm p (projectionMatrixDerivative b w) := by
  have hp₁ : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  choose C hC bound using fun (a b c d : Fin 4) =>
    exists_regularizedGaugeProjectionSymbol_Schwartz_Lp_bound a b c d p hp
  let CM : ℝ≥0∞ := ∑ a, ∑ b, ∑ c, ∑ d, C a b c d
  have hCM : CM < ⊤ := ENNReal.sum_lt_top.mpr fun a _ =>
    ENNReal.sum_lt_top.mpr fun b _ => ENNReal.sum_lt_top.mpr fun c _ =>
      ENNReal.sum_lt_top.mpr fun d _ => hC a b c d
  have hMain (w : ProjectionSchwartzMatrix) :
      projectionMatrixLpNorm p (projectionFullSchwartz w) ≤ CM * projectionMatrixLpNorm p w := by
    apply (projectionMatrixLpNorm_le_sum p hp₁ (projectionFullSchwartz w)).trans
    rw [show CM * projectionMatrixLpNorm p w =
      ∑ a, ∑ b, ∑ c, ∑ d, C a b c d * projectionMatrixLpNorm p w by
        simp only [CM, Finset.sum_mul]]
    apply Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    have hsum := eLpNorm_double_sum_le (ENNReal.ofReal p) hp₁
      (fun c d => (gaugeProjectionSchwartzComponent a b c d (w c d) : E → ℂ))
      (fun c d => (gaugeProjectionSchwartzComponent a b c d (w c d)).continuous.aestronglyMeasurable)
    rw [show (projectionFullSchwartz w a b : E → ℂ) =
      (fun x => ∑ c, ∑ d, gaugeProjectionSchwartzComponent a b c d (w c d) x) from
      funext (projectionFullSchwartz_apply w a b)]
    apply hsum.trans (Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => ?_)
    calc
      _ ≤ C a b c d * eLpNorm (w c d : E → ℂ) (ENNReal.ofReal p) volume := by
        change eLpNorm (gaugeProjectionSchwartzComponent a b c d (w c d) : E → ℂ)
          (ENNReal.ofReal p) volume ≤ _
        rw [gaugeProjectionSchwartzComponent_eq_radianAction]
        exact bound a b c d (w c d)
      _ ≤ _ := mul_le_mul_left' (entry_eLpNorm_le_projectionMatrixLpNorm p w c d) _
  refine ⟨CM, hCM, fun w => ⟨hMain w, fun b => ?_⟩⟩
  rw [← projectionFullSchwartz_coordinateDerivative]
  exact hMain (projectionMatrixDerivative b w)

end Burnett.P01
