import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Assemble finitely many supported weights against one density. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section
namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open scoped BigOperators

/-- Each weight restricts the integral to its own measurable window.
The sum is integrable on the original measure, with one common density. -/
theorem integrable_finiteRestrictedDensitySum
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (K : ι → Set X) (hK : ∀ i, MeasurableSet (K i))
    (w : ι → X → ℂ) (a : X → ℂ)
    (hSupport : ∀ i x, x ∉ K i → w i x = 0)
    (hI : ∀ i, Integrable (fun x => w i x * a x) (μ.restrict (K i))) :
    Integrable (fun x => (∑ i, w i x) * a x) μ ∧
      (∫ x, (∑ i, w i x) * a x ∂μ) = ∑ i, ∫ x in K i, w i x * a x ∂μ := by
  have hIndicator (i : ι) : (K i).indicator (fun x => w i x * a x) = fun x => w i x * a x := by
    funext x
    by_cases hx : x ∈ K i
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, hSupport i x hx, zero_mul]
  have hEach (i : ι) : Integrable (fun x => w i x * a x) μ := by
    rw [← hIndicator i, integrable_indicator_iff (hK i)]
    exact hI i
  simp_rw [Finset.sum_mul]
  refine ⟨integrable_finset_sum _ (fun i _ => hEach i), ?_⟩
  rw [integral_finset_sum _ (fun i _ => hEach i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_indicator (hK i), hIndicator i]

end Burnett.Microlocal.Overlap
