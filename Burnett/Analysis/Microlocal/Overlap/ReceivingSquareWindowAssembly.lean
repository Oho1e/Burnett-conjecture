import Burnett.Analysis.Microlocal.Overlap.ReceivingSquareLocalization

/-! Finite assembly of local classical limits on one phase measure. -/

set_option autoImplicit false
set_option maxHeartbeats 550000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators Topology

/-- Integrating the squared cutoff parts on their own windows gives the
integral against the same measure, including for a complex ordered entry. -/
theorem integral_eq_sum_squareCutoff_windows {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (π : X → E) (χ : ι → D) (W : ι → Set X) (F : X → ℂ)
    (hSum : ∀ x, F x ≠ 0 → ∑ i, (χ i : E → ℝ) (π x) ^ 2 = 1)
    (hZero : ∀ i x, x ∉ W i → ((χ i : E → ℝ) (π x) ^ 2 : ℝ) * F x = 0)
    (hI : ∀ i, IntegrableOn (fun x => ((χ i : E → ℝ) (π x) ^ 2 : ℝ) * F x) (W i) μ) :
    Integrable F μ ∧
      (∫ x, F x ∂μ) = ∑ i, ∫ x in W i, ((χ i : E → ℝ) (π x) ^ 2 : ℝ) * F x ∂μ := by
  let f (i : ι) (x : X) : ℂ := ((χ i : E → ℝ) (π x) ^ 2 : ℝ) * F x
  have hf (i : ι) : Integrable (f i) μ :=
    (hI i).integrable_of_forall_notMem_eq_zero (hZero i)
  have heq (x : X) : (∑ i, f i x) = F x := by
    by_cases hx : F x = 0
    · simp only [f, hx, mul_zero, Finset.sum_const_zero]
    · have hw : ∑ i, (((χ i : E → ℝ) (π x) ^ 2 : ℝ) : ℂ) = 1 := by exact_mod_cast hSum x hx
      simp only [f, ← Finset.sum_mul, hw, one_mul]
  have hInt := integrable_finset_sum Finset.univ (fun i _ => hf i)
  refine ⟨hInt.congr (Eventually.of_forall heq), ?_⟩
  calc
    _ = ∫ x, ∑ i, f i x ∂μ := (integral_congr_ae (Eventually.of_forall heq)).symm
    _ = ∑ i, ∫ x, f i x ∂μ := integral_finset_sum _ (fun i _ => hf i)
    _ = _ := Finset.sum_congr rfl (fun i _ => (setIntegral_eq_integral_of_forall_compl_eq_zero (hZero i)).symm)

/-- A same-sequence operator localization error and the local ordered limits
give the actual full pairing with the original complex phase measure. -/
theorem tendsto_classicalPairing_of_squareCutoff_windows {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (π : X → E) (χ : ι → D) (W : ι → Set X) (F : X → ℂ)
    (hSum : ∀ x, F x ≠ 0 → ∑ i, (χ i : E → ℝ) (π x) ^ 2 = 1)
    (hZero : ∀ i x, x ∉ W i → ((χ i : E → ℝ) (π x) ^ 2 : ℝ) * F x = 0)
    (hI : ∀ i, IntegrableOn (fun x => ((χ i : E → ℝ) (π x) ^ 2 : ℝ) * F x) (W i) μ)
    (Q : ℕ → ℂ) (Qloc : ι → ℕ → ℂ)
    (hErr : Tendsto (fun n => Q n - ∑ i, Qloc i n) atTop (𝓝 0))
    (hLim : ∀ i, Tendsto (Qloc i) atTop
      (𝓝 (∫ x in W i, ((χ i : E → ℝ) (π x) ^ 2 : ℝ) * F x ∂μ))) :
    Integrable F μ ∧ Tendsto Q atTop (𝓝 (∫ x, F x ∂μ)) := by
  obtain ⟨hF, heq⟩ := integral_eq_sum_squareCutoff_windows μ π χ W F hSum hZero hI
  have hLoc := tendsto_finset_sum Finset.univ (fun i _ => hLim i)
  rw [← heq] at hLoc
  refine ⟨hF, ?_⟩
  simpa only [sub_add_cancel, zero_add] using hErr.add hLoc

end Burnett.Microlocal.Overlap
