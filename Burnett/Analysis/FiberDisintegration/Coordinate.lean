import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section

namespace Burnett.F08.FiberTransport

open Set MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

variable {X Y A C : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSpace C]

/-- Read the original global kernel at the inverse chart point and express its
covectors in the selected chart. -/
def coordKernel (k : Kernel X Y) (bInv : A → X) (hbInv : Measurable bInv) (φ : Y → C) : Kernel A C :=
  (k.map φ).comap bInv hbInv

/-- Every joint section is transported with both its original base point and
its original conditional measure. Only the chart-inverse identity on the
support of the base volume is needed. -/
theorem coordKernel_integral_sections (v : Measure X) [SFinite v] (k : Kernel X Y) [IsSFiniteKernel k]
    (b : X → A) (hb : Measurable b) (bInv : A → X) (hbInv : Measurable bInv)
    (hleft : ∀ᵐ x ∂v, bInv (b x) = x) (φ : Y → C) (hφ : Measurable φ) (S : Set (A × C))
    (hS : MeasurableSet S) :
    ((v ⊗ₘ k).map (Prod.map b φ)) S =
      ∫⁻ a, coordKernel k bInv hbInv φ a (Prod.mk a ⁻¹' S) ∂v.map b := by
  letI : IsSFiniteKernel (coordKernel k bInv hbInv φ) := by
    unfold coordKernel
    infer_instance
  have hm := hb.prodMap hφ
  rw [Measure.map_apply hm hS, Measure.compProd_apply (hm hS),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hS) hb]
  apply lintegral_congr_ae
  filter_upwards [hleft] with x hx
  rw [coordKernel, Kernel.comap_apply', Kernel.map_apply' _ hφ _ (measurable_prodMk_left hS), hx]
  rfl

/-- Once the chart kernel is identified, its coordinate second moment is
the corresponding integral of the chart covector components of the original
global kernel. -/
theorem coordKernel_real_moment (k : Kernel X Y) (bInv : A → X) (hbInv : Measurable bInv)
    (φ : Y → C) (hφ : Measurable φ) (a : A) (f : C → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂coordKernel k bInv hbInv φ a) = ∫ p, f (φ p) ∂k (bInv a) := by
  rw [coordKernel, Kernel.comap_apply, Kernel.map_apply _ hφ, integral_map hφ.aemeasurable hf.aestronglyMeasurable]

end Burnett.F08.FiberTransport
