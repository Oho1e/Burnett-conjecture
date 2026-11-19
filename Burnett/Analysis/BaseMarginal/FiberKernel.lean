import Burnett.Geometry.ConnectionDifference
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Weighted disintegration of a finite coordinate measure

The marginal density, kernel, and measurable fiber relation use the same joint and base measures.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.F08.ActualBaseMarginal

open MeasureTheory Filter Set ProbabilityTheory Burnett.Geometry.ConnectionDifference
open scoped ENNReal ProbabilityTheory

/-- Extend the real base density by zero outside the open coordinate region. -/
def localizedFiberWeight (U : Set CoordinateSpace) (e : CoordinateSpace → ℝ)
    (y : CoordinateSpace) : ℝ≥0∞ := by
  classical
  exact U.piecewise (fun x => ENNReal.ofReal (e x)) 0 y

theorem measurable_localizedFiberWeight
    {U : Set CoordinateSpace} (hU : MeasurableSet U) {e : CoordinateSpace → ℝ}
    (he : ContinuousOn e U) : Measurable (localizedFiberWeight U e) := by
  classical
  exact (ENNReal.continuous_ofReal.comp_continuousOn he).measurable_piecewise continuousOn_const hU

theorem localizedFiberWeight_eq {U : Set CoordinateSpace} (e : CoordinateSpace → ℝ)
    {y : CoordinateSpace} (hy : y ∈ U) : localizedFiberWeight U e y = ENNReal.ofReal (e y) := by
  classical
  exact piecewise_eq_of_mem U _ _ hy

theorem localizedFiberWeight_zero_of_notMem {U : Set CoordinateSpace} (e : CoordinateSpace → ℝ)
    {y : CoordinateSpace} (hy : y ∉ U) : localizedFiberWeight U e y = 0 := by
  classical
  exact piecewise_eq_of_notMem U _ _ hy

/-- The original mass-density factor multiplies the standard Borel
conditional probability kernel. -/
def weightedFiberKernel (ρ : Measure (CoordinateSpace × CoordinateSpace)) [IsFiniteMeasure ρ]
    (w : CoordinateSpace → ℝ≥0∞) : Kernel CoordinateSpace CoordinateSpace :=
  ρ.condKernel.withDensity (fun y _ => w y)

theorem weightedFiberKernel_apply
    (ρ : Measure (CoordinateSpace × CoordinateSpace)) [IsFiniteMeasure ρ]
    {w : CoordinateSpace → ℝ≥0∞} (hw : Measurable w) (y : CoordinateSpace) :
    weightedFiberKernel ρ w y = w y • ρ.condKernel y := by
  have hu : Measurable (Function.uncurry (fun (a : CoordinateSpace) (_ : CoordinateSpace) => w a)) :=
    hw.comp measurable_fst
  rw [weightedFiberKernel, Kernel.withDensity_apply _ hu, withDensity_const]

theorem weightedFiberKernel_isFinite
    (ρ : Measure (CoordinateSpace × CoordinateSpace)) [IsFiniteMeasure ρ]
    {w : CoordinateSpace → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞) (hw : ∀ y, w y ≤ C) :
    IsFiniteKernel (weightedFiberKernel ρ w) :=
  Kernel.isFiniteKernel_withDensity_of_bounded _ hC (fun y _ => hw y)

theorem weightedFiberKernel_total
    (ρ : Measure (CoordinateSpace × CoordinateSpace)) [IsFiniteMeasure ρ]
    {w : CoordinateSpace → ℝ≥0∞} (hw : Measurable w) (y : CoordinateSpace) :
    weightedFiberKernel ρ w y univ = w y := by
  rw [weightedFiberKernel_apply ρ hw y, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]

/-- Disintegration against the original base measure, with the density
absorbed into each fiber measure. This uses the measure itself, rather
than choosing or prescribing an angular distribution from moments. -/
theorem weightedFiberKernel_compProd
    (ρ : Measure (CoordinateSpace × CoordinateSpace)) [IsFiniteMeasure ρ]
    (dV : Measure CoordinateSpace) [IsFiniteMeasure dV]
    {w : CoordinateSpace → ℝ≥0∞} (hw : Measurable w)
    [IsFiniteKernel (weightedFiberKernel ρ w)]
    (hMarginal : ρ.fst = dV.withDensity w) :
    dV ⊗ₘ weightedFiberKernel ρ w = ρ := by
  calc
    _ = (dV.withDensity w) ⊗ₘ ρ.condKernel := by
      apply Measure.ext
      intro s hs
      rw [Measure.compProd_apply hs, Measure.compProd_apply hs,
        lintegral_withDensity_eq_lintegral_mul dV hw (Kernel.measurable_kernel_prodMk_left hs)]
      apply lintegral_congr
      intro y
      rw [weightedFiberKernel_apply ρ hw y, Measure.smul_apply, smul_eq_mul]
      rfl
    _ = ρ := hMarginal ▸ ρ.disintegrate ρ.condKernel

/-- A joint measure concentrated on a measurable relation yields fiberwise
concentration almost everywhere with respect to the base measure used
in its actual disintegration. -/
theorem ae_fiber_concentrated_of_compProd
    (dV : Measure CoordinateSpace) [IsFiniteMeasure dV]
    (κ : Kernel CoordinateSpace CoordinateSpace) [IsFiniteKernel κ]
    (ρ : Measure (CoordinateSpace × CoordinateSpace)) (hρ : dV ⊗ₘ κ = ρ)
    {Z : Set (CoordinateSpace × CoordinateSpace)} (hZ : MeasurableSet Z)
    (hMass : ρ Zᶜ = 0) :
    ∀ᵐ y ∂dV, κ y (((fun η => (y, η)) ⁻¹' Z)ᶜ) = 0 := by
  rw [← hρ, Measure.compProd_apply hZ.compl,
    lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hZ.compl)] at hMass
  exact hMass

theorem localFiberKernel_unique
    (dV : Measure CoordinateSpace) [IsFiniteMeasure dV] (κ κ' : Kernel CoordinateSpace CoordinateSpace)
    [IsFiniteKernel κ] [IsFiniteKernel κ'] (μ : Measure (CoordinateSpace × CoordinateSpace))
    (hκ : dV ⊗ₘ κ = μ) (hκ' : dV ⊗ₘ κ' = μ) :
    κ =ᵐ[dV] κ' :=
  Kernel.ae_eq_of_compProd_eq (hκ.trans hκ'.symm)

/-- A finite coordinate joint measure with a known bounded marginal weight
gives one finite, integrable fiber kernel over the original base measure.
The joint law, the mass of every fiber, and the almost-everywhere fiber
relation refer to this same kernel. Its uniqueness is for the fixed joint
law and base measure. -/
theorem exists_localFiberDisintegration
    (ρ : Measure (CoordinateSpace × CoordinateSpace)) [IsFiniteMeasure ρ]
    (dV : Measure CoordinateSpace) [IsFiniteMeasure dV]
    {w : CoordinateSpace → ℝ≥0∞} (hw : Measurable w)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hBound : ∀ y, w y ≤ C)
    (hMarginal : ρ.fst = dV.withDensity w)
    {Z : Set (CoordinateSpace × CoordinateSpace)} (hZ : MeasurableSet Z)
    (hMass : ρ Zᶜ = 0) :
    ∃ κ : Kernel CoordinateSpace CoordinateSpace, ∃ _ : IsFiniteKernel κ,
      dV ⊗ₘ κ = ρ ∧
      (∀ y, κ y univ = w y) ∧
      Integrable (fun y => (κ y).real univ) dV ∧
      (∫⁻ y, κ y univ ∂dV) = ρ univ ∧
      (∀ᵐ y ∂dV, κ y (((fun η => (y, η)) ⁻¹' Z)ᶜ) = 0) ∧
      ∀ (κ' : Kernel CoordinateSpace CoordinateSpace) [IsFiniteKernel κ'],
        dV ⊗ₘ κ' = ρ → κ =ᵐ[dV] κ' := by
  let κ := weightedFiberKernel ρ w
  letI : IsFiniteKernel κ := weightedFiberKernel_isFinite ρ hC hBound
  have hκ : dV ⊗ₘ κ = ρ := weightedFiberKernel_compProd ρ dV hw hMarginal
  have hTotal (y : CoordinateSpace) : κ y univ = w y := weightedFiberKernel_total ρ hw y
  have hRealMass : Integrable (fun y => (κ y).real univ) dV := by
    have hm : Measurable (fun y => (κ y).real univ) :=
      ENNReal.measurable_toReal.comp (κ.measurable_coe MeasurableSet.univ)
    apply Integrable.of_bound hm.aestronglyMeasurable C.toReal
    exact Eventually.of_forall fun y => by
      change |(κ y univ).toReal| ≤ C.toReal
      rw [abs_of_nonneg ENNReal.toReal_nonneg, hTotal y]
      exact ENNReal.toReal_mono hC (hBound y)
  have hIntegral : (∫⁻ y, κ y univ ∂dV) = ρ univ := by
    rw [← hκ, Measure.compProd_apply MeasurableSet.univ]
    simp only [preimage_univ]
  refine ⟨κ, inferInstance, hκ, hTotal, hRealMass, hIntegral,
    ae_fiber_concentrated_of_compProd dV κ ρ hκ hZ hMass, ?_⟩
  intro κ' _ hκ'
  exact localFiberKernel_unique dV κ κ' ρ hκ hκ'

end Burnett.F08.ActualBaseMarginal
