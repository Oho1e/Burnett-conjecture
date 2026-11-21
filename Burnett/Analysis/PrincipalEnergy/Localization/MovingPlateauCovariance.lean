import Burnett.Analysis.PrincipalEnergy.Localization.SymbolTranslation
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichSymbol

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped FourierTransform

/-- Recenter the actual sandwich by the moving plateau χ(· - c).
The symbol on the right samples the original coefficient at x + c. -/
theorem cutoffSandwichSymbol_recenter (a : Space → Space → ℂ)
    (χ : SchwartzMap Space ℂ) (c x ξ : Space) :
    cutoffSandwichSymbol a (translateSchwartz (-c) χ) (x+c) ξ =
      cutoffSandwichSymbol (fun y => a (y+c)) χ x ξ := by
  simp only [cutoffSandwichSymbol, translateSchwartz_apply, add_neg_cancel_right]
  apply congrArg (fun z : ℂ => χ x * z)
  apply integral_congr_ae
  filter_upwards with η
  have hFourier :
      𝓕 (translateSchwartz (-c) χ : Space → ℂ) η =
        Real.fourierChar (inner ℝ (-c) η) • 𝓕 (χ : Space → ℂ) η :=
    congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume (innerₗ Space)
      (χ : Space → ℂ) (-c)) η
  have hPhase :
      Real.fourierChar (inner ℝ η (x+c)) * Real.fourierChar (inner ℝ (-c) η) =
        Real.fourierChar (inner ℝ η x) := by
    rw [← Real.fourierChar.map_add_eq_mul]
    congr 1
    rw [inner_add_right, inner_neg_left, real_inner_comm c η, add_neg_cancel_right]
  have hComplex : (Real.fourierChar (inner ℝ η (x+c)) : ℂ) *
      (Real.fourierChar (inner ℝ (-c) η) : ℂ) =
        (Real.fourierChar (inner ℝ η x) : ℂ) := by
    simpa only [Circle.coe_mul] using congrArg (fun z : Circle => (z : ℂ)) hPhase
  rw [hFourier]
  simp only [Circle.smul_def, smul_eq_mul]
  rw [← hComplex]
  ring

/-- The recentered symbol represents the original operator truncated on both
sides by the plateau centered at c. -/
theorem firstOrderAction_movingPlateau (a : Space → Space → ℂ)
    (ha : FrequencyOrderOne a) (χ f : SchwartzMap Space ℂ) (c x : Space) :
    firstOrderAction (cutoffSandwichSymbol (fun y => a (y+c)) χ)
        (translateSchwartz c f) x =
      translateSchwartz (-c) χ (x+c) *
        firstOrderAction a (scalarSchwartzProduct (translateSchwartz (-c) χ) f) (x+c) := by
  have hSymbol :
      cutoffSandwichSymbol (fun y => a (y+c)) χ =
        fun y => cutoffSandwichSymbol a (translateSchwartz (-c) χ) (y+c) := by
    funext y ξ
    exact (cutoffSandwichSymbol_recenter a χ c y ξ).symm
  rw [hSymbol, firstOrderAction_translate, firstOrderAction_cutoffSandwichSymbol ha]

end Burnett.Analysis.CarlesonEmbedding
