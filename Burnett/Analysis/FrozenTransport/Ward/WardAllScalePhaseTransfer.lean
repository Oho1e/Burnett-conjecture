import Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives

set_option autoImplicit false
set_option maxRecDepth 6200
set_option maxHeartbeats 12000000
noncomputable section

namespace Burnett.C02

open MeasureTheory Burnett.A05 Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.RicciSymbol (Tensor2)
open scoped ContDiff

/-- Covectors of the original signed triad in the order seen by the Fourier integral. -/
def wardPhaseCovector (x : Joint) (j : Fin 3) : E := ![x.1, x.2, -(x.1 + x.2)] j

/-- Multiplying the symbol by a one-slot scalar phase transfers the same
phase to the Schwartz input at that slot, before taking the Fourier integral. -/
theorem wardRadianWeight_phase_transfer (A : Joint → ℂ) (phase : E → ℂ)
    (f : Fin 3 → SchwartzMap E ℂ) (g : SchwartzMap E ℂ) (j : Fin 3)
    (hg : ∀ ξ, radianFourier g ξ = phase ξ * radianFourier (f j) ξ) :
    radianTrilinearWeight (fun x => A x * phase (wardPhaseCovector x j)) (f 0) (f 1) (f 2) =
      radianTrilinearWeight A (Function.update f j g 0) (Function.update f j g 1) (Function.update f j g 2) := by
  funext x
  fin_cases j <;> simp [radianTrilinearWeight, radianWeight, wardPhaseCovector, hg] <;> ring

/-- Combine finite exact phase extractions through the existing low-slot
all-scale estimate. This accepts the actual ordered Fourier fields and one
phase field for each separated coefficient. -/
theorem exists_wardLowPhaseForm_bound {ι : Type*} [Fintype ι]
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hCut : ∀ t, 1 ≤ t → ϑ t = 0)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (m : Tensor2) (F : ι → WardLowPoint → ℂ) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) wardLowProfileDomain)
    (j : ι → Fin 3) :
    ∃ C : ι → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (A : Joint → ℂ) (f : Fin 3 → SchwartzMap E ℂ) (g : ι → SchwartzMap E ℂ),
        (∀ i ξ, radianFourier (g i) ξ = (normalizedFrozenPhase m ξ : ℂ) * radianFourier (f (j i)) ξ) →
        (∀ x, A x = ∑ i, wardLowRadialSymbol ϑ κ (F i) x * (normalizedFrozenPhase m (wardPhaseCovector x (j i)) : ℂ)) →
        Integrable (radianTrilinearWeight A (f 0) (f 1) (f 2)) ∧
        ‖radianTrilinearForm A (f 0) (f 1) (f 2)‖ ≤ ∑ i,
          C i * (wardCoordinateGradientL3 (Function.update f (j i) (g i) 0) *
            wardCoordinateGradientL3 (Function.update f (j i) (g i) 1) *
            wardCoordinateGradientL3 (Function.update f (j i) (g i) 2)) := by
  classical
  choose C hC hEst using fun i => exists_wardLowRadialForm_bound ϑ hϑ hCut κ hκ hSmall (F i) (hF i)
  refine ⟨C,hC,?_⟩
  intro A f g hg hA
  let B i := wardLowRadialSymbol ϑ κ (F i)
  let f' i := Function.update f (j i) (g i)
  let W i := radianTrilinearWeight (B i) (f' i 0) (f' i 1) (f' i 2)
  let T i := radianTrilinearForm (B i) (f' i 0) (f' i 1) (f' i 2)
  have hInt (i : ι) : Integrable (W i) := (hEst i _ _ _).1
  have hW : radianTrilinearWeight A (f 0) (f 1) (f 2) = fun x => ∑ i, W i x := by
    funext x
    have h (i : ι) : W i x =
        radianTrilinearWeight (fun y => B i y * (normalizedFrozenPhase m (wardPhaseCovector y (j i)) : ℂ))
          (f 0) (f 1) (f 2) x :=
      congrFun (wardRadianWeight_phase_transfer (B i) (fun ξ => (normalizedFrozenPhase m ξ : ℂ)) f (g i) (j i)
        (hg i)).symm x
    change A x * _ = _
    rw [hA, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (h i).symm
  refine ⟨hW.symm ▸ integrable_finset_sum Finset.univ (fun i _ => hInt i),?_⟩
  have hSum : radianTrilinearForm A (f 0) (f 1) (f 2) = ∑ i, T i := by
    change (tau^8)⁻¹ • (∫ x, radianTrilinearWeight A (f 0) (f 1) (f 2) x) =
      ∑ i : ι, (tau^8)⁻¹ • (∫ x, W i x)
    rw [hW, ← Finset.smul_sum, ← integral_finset_sum Finset.univ (fun i _ => hInt i)]
  rw [hSum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => (hEst i _ _ _).2))

end Burnett.C02
