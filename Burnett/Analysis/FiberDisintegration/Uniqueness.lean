import Burnett.Analysis.FiberDisintegration.CountableCover
import Mathlib.Probability.Kernel.CompProdEqIff

set_option autoImplicit false
noncomputable section

namespace Burnett.F08.FiberGluing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]

/-- The same joint measure has a unique measurable disintegration almost everywhere.
The competing kernel is specified by its ordinary integral formula for every measurable joint set. -/
theorem localFiberKernel_unique_of_integral_sections
    (dV : Measure α) [IsFiniteMeasure dV] (κ κ' : Kernel α β) [IsFiniteKernel κ]
    (ρ : Measure (α × β)) (hκ : dV ⊗ₘ κ = ρ)
    (hκ' : ∀ s : Set (α × β), MeasurableSet s →
      ρ s = ∫⁻ y, κ' y (Prod.mk y ⁻¹' s) ∂dV) :
    κ' =ᵐ[dV] κ := by
  classical
  have hMass : (fun y => κ' y univ) =ᵐ[dV] fun y => κ y univ := by
    apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (κ'.measurable_coe MeasurableSet.univ) (κ.measurable_coe MeasurableSet.univ)
    intro s hs _
    have hSection (y : α) : Prod.mk y ⁻¹' (s ×ˢ (univ : Set β)) =
        if y ∈ s then univ else ∅ := by
      ext η
      by_cases hy : y ∈ s <;> simp [hy]
    calc
      (∫⁻ y in s, κ' y univ ∂dV) = ∫⁻ y, κ' y (Prod.mk y ⁻¹' (s ×ˢ univ)) ∂dV := by
        rw [← lintegral_indicator hs]
        apply lintegral_congr
        intro y
        rw [hSection]
        by_cases hy : y ∈ s <;> simp [hy]
      _ = ρ (s ×ˢ univ) := (hκ' _ (hs.prod MeasurableSet.univ)).symm
      _ = ∫⁻ y in s, κ y univ ∂dV := by rw [← hκ, Measure.compProd_apply_prod hs MeasurableSet.univ]
  let good : Set α := {y | κ' y univ ≤ κ.bound}
  have hGood : MeasurableSet good :=
    measurableSet_le (κ'.measurable_coe MeasurableSet.univ) measurable_const
  have hGoodAE : ∀ᵐ y ∂dV, y ∈ good := by
    filter_upwards [hMass] with y hy
    exact hy.le.trans (κ.measure_le_bound y univ)
  let trimmed := Kernel.piecewise hGood κ' 0
  haveI : IsFiniteKernel trimmed := by
    refine ⟨⟨κ.bound, κ.bound_lt_top, fun y => ?_⟩⟩
    change Kernel.piecewise hGood κ' 0 y univ ≤ κ.bound
    rw [Kernel.piecewise_apply']
    by_cases hy : y ∈ good
    · simpa only [if_pos hy] using hy
    · simp [hy]
  have hTrim : trimmed =ᵐ[dV] κ' := by
    filter_upwards [hGoodAE] with y hy
    simp only [trimmed, Kernel.piecewise_apply, if_pos hy]
  have hComp : dV ⊗ₘ trimmed = ρ := by
    apply Measure.ext
    intro s hs
    rw [Measure.compProd_apply hs, hκ' s hs]
    apply lintegral_congr_ae
    filter_upwards [hTrim] with y hy
    rw [hy]
  exact hTrim.symm.trans (Kernel.ae_eq_of_compProd_eq (hComp.trans hκ.symm))

/-- Same-joint uniqueness in the `compProd` interface for any s-finite competing kernel. -/
theorem localFiberKernel_unique_of_sFinite
    (dV : Measure α) [IsFiniteMeasure dV] (κ κ' : Kernel α β)
    [IsFiniteKernel κ] [IsSFiniteKernel κ'] (ρ : Measure (α × β))
    (hκ : dV ⊗ₘ κ = ρ) (hκ' : dV ⊗ₘ κ' = ρ) :
    κ' =ᵐ[dV] κ :=
  localFiberKernel_unique_of_integral_sections dV κ κ' ρ hκ (fun s hs => by
    rw [← hκ', Measure.compProd_apply hs])

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountableOrCountablyGenerated X Y]

/-- A competing measurable kernel which represents every measurable joint set
agrees almost everywhere with the pasted disintegration. The base measure and
the bounds on the local kernels need only be finite patch by patch. -/
theorem patchKernel_unique_of_integral_sections
    (v : Measure X) (ρ : Measure (X × Y))
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (cover : ⋃ n, U n = univ)
    [∀ n, IsFiniteMeasure (v.restrict (U n))]
    (k : ℕ → Kernel X Y) [∀ n, IsFiniteKernel (k n)]
    (hLocal : ∀ n, v.restrict (U n) ⊗ₘ k n = ρ.restrict (Prod.fst ⁻¹' U n))
    (k' : Kernel X Y)
    (hRep : ∀ s : Set (X × Y), MeasurableSet s → ρ s = ∫⁻ x, k' x (Prod.mk x ⁻¹' s) ∂v) :
    k' =ᵐ[v] patchKernel U hU k := by
  apply patchKernel_ae_of_local v U hU cover k (fun x m => k' x = m)
  intro n
  apply localFiberKernel_unique_of_integral_sections _ _ _ _ (hLocal n)
  intro s hs
  rw [Measure.restrict_apply hs, hRep _ (hs.inter (measurable_fst (hU n))),
    ← lintegral_indicator (hU n)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ U n
  · rw [indicator_of_mem hx]
    congr 1
    ext y
    simp [hx]
  · rw [indicator_of_notMem hx]
    have hempty : Prod.mk x ⁻¹' (s ∩ Prod.fst ⁻¹' U n) = ∅ := by
      ext y
      simp [hx]
    rw [hempty, measure_empty]

end Burnett.F08.FiberGluing
