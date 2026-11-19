import Burnett.Analysis.FiberDisintegration.Uniqueness
import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.Probability.Kernel.WithDensity

set_option autoImplicit false
noncomputable section

namespace Burnett.F08.FiberGluing

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]

private theorem finite_weighted_conditional (v : Measure X) [IsFiniteMeasure v]
    (ρ : Measure (X × Y)) [IsFiniteMeasure ρ] (w : X → ℝ≥0∞) (hw : Measurable w)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (bound : ∀ x, w x ≤ C) (hm : ρ.fst = v.withDensity w) :
    ∃ k : Kernel X Y, IsFiniteKernel k ∧ v ⊗ₘ k = ρ ∧ ∀ x, k x univ = w x := by
  let k := ρ.condKernel.withDensity (fun x _ => w x)
  haveI : IsFiniteKernel k := Kernel.isFiniteKernel_withDensity_of_bounded _ hC (fun x _ => bound x)
  have happly (x : X) : k x = w x • ρ.condKernel x := by
    have hweight : Measurable (Function.uncurry (fun (a : X) (_ : Y) => w a)) :=
      hw.comp measurable_fst
    show ρ.condKernel.withDensity _ x = _
    rw [Kernel.withDensity_apply _ hweight, withDensity_const]
  refine ⟨k, inferInstance, ?_, fun x => ?_⟩
  · calc
      v ⊗ₘ k = (v.withDensity w) ⊗ₘ ρ.condKernel := by
        ext s hs
        rw [Measure.compProd_apply hs, Measure.compProd_apply hs,
          lintegral_withDensity_eq_lintegral_mul v hw (Kernel.measurable_kernel_prodMk_left hs)]
        apply lintegral_congr
        intro x
        rw [happly, Measure.smul_apply, smul_eq_mul]
        rfl
      _ = ρ := hm ▸ ρ.disintegrate ρ.condKernel
  · rw [happly, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]

/-- A locally bounded base marginal produces a disintegration over the original
base volume on a countable cover. The fixed joint measure determines the kernel
up to a single null set. Neither measure needs to have finite total mass. -/
theorem exists_weighted_disintegration_on_cover
    (v : Measure X) [SFinite v] (ρ : Measure (X × Y))
    (w : X → ℝ≥0∞) (hw : Measurable w) (hm : ρ.fst = v.withDensity w)
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (cover : ⋃ n, U n = univ)
    [∀ n, IsFiniteMeasure (v.restrict (U n))]
    [∀ n, IsFiniteMeasure (ρ.restrict (Prod.fst ⁻¹' U n))]
    (hb : ∀ n, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x ∈ U n, w x ≤ C)
    {Z : Set (X × Y)} (hZ : MeasurableSet Z) (support : ρ Zᶜ = 0) :
    ∃ k : Kernel X Y, IsSFiniteKernel k ∧ v ⊗ₘ k = ρ ∧ (∀ x, IsFiniteMeasure (k x)) ∧
      (∀ x, k x univ = w x) ∧ (∀ᵐ x ∂v, k x (Prod.mk x ⁻¹' Zᶜ) = 0) ∧
      ∀ k' : Kernel X Y, (∀ s : Set (X × Y), MeasurableSet s →
        ρ s = ∫⁻ x, k' x (Prod.mk x ⁻¹' s) ∂v) → k' =ᵐ[v] k := by
  classical
  have localK (n : ℕ) : ∃ k : Kernel X Y, IsFiniteKernel k ∧
      v.restrict (U n) ⊗ₘ k = ρ.restrict (Prod.fst ⁻¹' U n) ∧ ∀ x, k x univ = (U n).indicator w x := by
    obtain ⟨C, hC, bound⟩ := hb n
    apply finite_weighted_conditional _ _ _ (hw.indicator (hU n)) C hC
    · intro x
      by_cases hx : x ∈ U n
      · simpa [hx] using bound x hx
      · simp [hx]
    · calc
        (ρ.restrict (Prod.fst ⁻¹' U n)).fst = ρ.fst.restrict (U n) :=
          (Measure.restrict_map measurable_fst (hU n)).symm
        _ = (v.restrict (U n)).withDensity w := by rw [hm, restrict_withDensity (hU n)]
        _ = _ := withDensity_congr_ae (by
          filter_upwards [ae_restrict_mem (μ := v) (hU n)] with x hx
          simp [hx])
  choose k hfin hprod hmass using localK
  letI : ∀ n, IsFiniteKernel (k n) := hfin
  obtain ⟨hjoint, hfinite⟩ := patchKernel_disintegrates v ρ U hU cover k hprod
  refine ⟨patchKernel U hU k, inferInstance, hjoint, hfinite, ?_, ?_, ?_⟩
  · intro x
    have hx : x ∈ ⋃ n, disjointed U n := by rw [iUnion_disjointed, cover]; exact mem_univ x
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    rw [patchKernel_apply U hU k n hn, hmass n x, indicator_of_mem (disjointed_subset U n hn)]
  · rw [← hjoint, Measure.compProd_apply hZ.compl,
      lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hZ.compl)] at support
    exact support
  · exact patchKernel_unique_of_integral_sections v ρ U hU cover k hprod

end Burnett.F08.FiberGluing
