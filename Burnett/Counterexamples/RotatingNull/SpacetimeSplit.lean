import Burnett.Analysis.Cubic.Explicit
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
namespace Burnett.RotatingNullSpacetime
open MeasureTheory

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev Spatial := EuclideanSpace ℝ (Fin 3)

def split : Space ≃ᵐ ℝ × Spatial :=
  (EuclideanSpace.measurableEquiv (Fin 4)).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (EuclideanSpace.measurableEquiv (Fin 3)).symm))

theorem split_apply (x : Space) :
    split x = (x 0, WithLp.toLp 2 (fun j : Fin 3 => x j.succ)) := by
  rfl

theorem split_measurePreserving : MeasurePreserving split := by
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (EuclideanSpace.volume_preserving_measurableEquiv (Fin 3)).symm).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).comp
        (EuclideanSpace.volume_preserving_measurableEquiv (Fin 4)))

theorem integrable_separated (χ : ℝ → ℝ) (η : Spatial → ℝ)
    (hχ : Integrable χ) (hη : Integrable η) :
    Integrable (fun x : Space => χ (x 0) * η (WithLp.toLp 2 (fun j : Fin 3 => x j.succ))) := by
  have h := (split_measurePreserving.integrable_comp_emb split.measurableEmbedding).mpr (hχ.mul_prod hη)
  simpa only [Function.comp_apply, split_apply] using h

theorem integral_separated (χ : ℝ → ℝ) (η : Spatial → ℝ) :
    (∫ x : Space, χ (x 0) * η (WithLp.toLp 2 (fun j : Fin 3 => x j.succ))) =
      (∫ t, χ t) * (∫ y, η y) := by
  have h := split_measurePreserving.integral_comp split.measurableEmbedding
    (fun p : ℝ × Spatial => χ p.1 * η p.2)
  calc
    _ = ∫ p : ℝ × Spatial, χ p.1 * η p.2 := by simpa only [Function.comp_apply, split_apply] using h
    _ = _ := integral_prod_mul _ _

end Burnett.RotatingNullSpacetime
