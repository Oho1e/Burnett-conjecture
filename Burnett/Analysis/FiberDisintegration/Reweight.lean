import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MapComap

set_option autoImplicit false
noncomputable section

namespace Burnett.F08.KernelRenormalization

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

def reweightedKernel (K : Kernel X Y) [IsSFiniteKernel K] (w : Y → ℝ≥0∞) (F : Y → Z) : Kernel X Z :=
  (K.withDensity fun _ y => w y).map F

theorem reweightedKernel_apply (K : Kernel X Y) [IsSFiniteKernel K] {w : Y → ℝ≥0∞}
    (hw : Measurable w) {F : Y → Z} (hF : Measurable F) (x : X) :
    reweightedKernel K w F x = ((K x).withDensity w).map F := by
  rw [reweightedKernel,Kernel.map_apply _ hF,Kernel.withDensity_apply]
  exact hw.comp measurable_snd

/-- Reweight and push forward inside each fiber of a positive measure reconstructed
by a kernel. The resulting measure identity tests every measurable target set. -/
theorem reweightedKernel_reconstruct (v : Measure X) (μ : Measure Y) (K : Kernel X Y) [IsSFiniteKernel K]
    (hrec : ∀ A : Set Y, MeasurableSet A → μ A = ∫⁻ x, K x A ∂v)
    {w : Y → ℝ≥0∞} (hw : Measurable w) {F : Y → Z} (hF : Measurable F)
    (A : Set Z) (hA : MeasurableSet A) :
    ((μ.withDensity w).map F) A = ∫⁻ x, reweightedKernel K w F x A ∂v := by
  have he : μ = v.bind (fun x => K x) := by
    ext T hT
    rw [Measure.bind_apply hT K.measurable.aemeasurable]
    exact hrec T hT
  have hT := hF hA
  rw [Measure.map_apply hF hA,withDensity_apply _ hT,← lintegral_indicator hT, he,
    Measure.lintegral_bind K.measurable.aemeasurable (hw.indicator hT).aemeasurable]
  apply lintegral_congr
  intro x
  rw [reweightedKernel_apply _ hw hF,Measure.map_apply hF hA,withDensity_apply _ hT,lintegral_indicator hT]

end Burnett.F08.KernelRenormalization
