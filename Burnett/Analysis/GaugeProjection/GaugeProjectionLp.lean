import Burnett.Analysis.GaugeProjection.GaugeProjectionSymbol
import Burnett.Analysis.Fourier.FixedInfraredSchwartz

set_option autoImplicit false
set_option maxHeartbeats 2900000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter
open Burnett.A02.FrequencySplit (E radianFourier radianAction homogeneous_multiplier_Schwartz_bound)
open Burnett.A07 (fixedInfraredSchwartz fixedInfraredSchwartz_radianFourier exists_fixedInfraredSchwartz_Lp_bound)
open scoped ENNReal

/-- Fixed high-pass action with the same cutoff used in the matrix symbol. -/
def projectionInfraredAction (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  fixedInfraredSchwartz gaugeProjectionInfrared gaugeProjectionInfrared_contDiff 1 2 zero_lt_one
    (fun _ hs => gaugeProjectionInfrared_zero hs) (fun _ hs => gaugeProjectionInfrared_one hs) f

theorem radianFourier_projectionInfraredAction (f : SchwartzMap E ℂ) (ξ : E) :
    radianFourier (projectionInfraredAction f) ξ =
      (gaugeProjectionInfrared ‖ξ‖ : ℂ) * radianFourier f ξ :=
  fixedInfraredSchwartz_radianFourier gaugeProjectionInfrared gaugeProjectionInfrared_contDiff
    1 2 zero_lt_one (fun _ hs => gaugeProjectionInfrared_zero hs) (fun _ hs => gaugeProjectionInfrared_one hs) f ξ

/-- Composition of the homogeneous projection with the fixed high pass
has exactly the original regularized Fourier symbol. -/
theorem radianAction_regularizedGaugeProjectionSymbol (a b c d : Fin 4) (f : SchwartzMap E ℂ) :
    radianAction (regularizedGaugeProjectionSymbol a b c d) f =
      radianAction (gaugeProjectionSymbol a b c d) (projectionInfraredAction f) := by
  funext x
  unfold radianAction
  apply congrArg _
  apply integral_congr_ae
  refine Eventually.of_forall fun ξ => ?_
  simp only [regularizedGaugeProjectionSymbol, Complex.ofReal_mul, radianFourier_projectionInfraredAction]
  ring

/-- The original regularized matrix multiplier has finite-exponent bounds
on its actual scalar entries, with no variation of the infrared cutoff. -/
theorem exists_regularizedGaugeProjectionSymbol_Schwartz_Lp_bound
    (a b c d : Fin 4) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : SchwartzMap E ℂ,
      eLpNorm (radianAction (regularizedGaugeProjectionSymbol a b c d) f) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,bound⟩ := homogeneous_multiplier_Schwartz_bound _
    (gaugeProjectionSymbol_contDiffOn a b c d) (gaugeProjectionSymbol_scale a b c d) p hp
  obtain ⟨D,hD,cutbound⟩ := exists_fixedInfraredSchwartz_Lp_bound
    gaugeProjectionInfrared gaugeProjectionInfrared_contDiff 1 2 zero_lt_one
    (fun _ hs => gaugeProjectionInfrared_zero hs) (fun _ hs => gaugeProjectionInfrared_one hs) p hp
  refine ⟨C * D, ENNReal.mul_lt_top hC hD, fun f => ?_⟩
  rw [radianAction_regularizedGaugeProjectionSymbol]
  exact (bound (projectionInfraredAction f)).trans <| by
    rw [mul_assoc]
    exact mul_le_mul_left' (cutbound f) C

end Burnett.P01
