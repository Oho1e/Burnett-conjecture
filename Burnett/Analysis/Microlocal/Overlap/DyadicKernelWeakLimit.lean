import Burnett.Analysis.Microlocal.Overlap.BoundedKernelWeakLimit
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Filter Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel (E dyadicScale)
open scoped InnerProduct Topology ENNReal

/-- A dyadic family of localized kernel differences with an inverse-scale
Schur gain has an absolutely convergent action that takes weakly null inputs to zero. -/
theorem exists_overlapShell_actions_tendsto_zero
    (K : ℕ → E → E → ℂ) (hK : ∀ j, Measurable (uncurry (K j)))
    (S : Set E) (hS : MeasurableSet S) (hSfin : (volume : Measure E) S ≠ ∞)
    (hSupport : ∀ j x y, x ∉ S ∨ y ∉ S → K j x y = 0)
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 < q)
    (hbound : ∀ j x y, ‖K j x y‖ ≤
      C * dyadicScale j ^ 3 / (1 + dyadicScale j * q * ‖x - y‖) ^ 5)
    (f : ℕ → E → ℂ) (hfm : ∀ n, Measurable (f n)) (hf₁ : ∀ n, Integrable (f n))
    (hf : ∀ n, MemLp (f n) 2 volume)
    (B : ℝ) (hu : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((hf n).toLp (f n))) atTop (𝓝 0)) :
    ∃ U : ℕ → ℕ → ComplexL2 E,
      (∀ j n, U j n =ᵐ[volume] fun x => ∫ y, K j x y * f n y) ∧
      (∀ n, Summable (fun j => ‖U j n‖)) ∧
      Tendsto (fun n => ∑' j, U j n) atTop (𝓝 0) := by
  let s := dyadicScale
  have hs (j : ℕ) : 0 < s j := by
    unfold s dyadicScale
    positivity
  choose hA hNorm using fun j n => overlapKernel_action_norm_le (K j) (hK j)
    C q (s j) hC hq (hs j) (hbound j) (f n) (hfm n) (hf₁ n) (hf n)
  let U (j n : ℕ) := (hA j n).toLp (fun x => ∫ y, K j x y * f n y)
  let g (j : ℕ) := (C / q ^ 4 * ∫ z, fifthProfile z) / s j
  have hMajor : Summable (fun j => g j * B) := (summable_overlapShell_bound C q).mul_right B
  have hg₀ (j : ℕ) : 0 ≤ g j := by
    dsimp [g]
    exact div_nonneg (mul_nonneg (div_nonneg hC (pow_nonneg hq.le _))
      (integral_nonneg fifthProfile_nonneg)) (hs j).le
  have hMaj j n : ‖U j n‖ ≤ g j * B :=
    (hNorm j n).trans (mul_le_mul_of_nonneg_left (hu n) (hg₀ j))
  have hFixed (j : ℕ) : Tendsto (U j) atTop (𝓝 0) := by
    have hGlobal (x y : E) : ‖K j x y‖ ≤ C * s j ^ 3 := by
      apply (hbound j x y).trans
      have hbase : 1 ≤ 1 + s j * q * ‖x - y‖ :=
        le_add_of_nonneg_right (mul_nonneg (mul_nonneg (hs j).le hq.le) (norm_nonneg _))
      rw [div_le_iff₀ (pow_pos (zero_lt_one.trans_le hbase) _)]
      have hDen : 1 ≤ (1 + s j * q * ‖x - y‖) ^ 5 := one_le_pow₀ hbase
      exact le_mul_of_one_le_right (mul_nonneg hC (pow_nonneg (hs j).le _)) hDen
    exact boundedKernel_action_tendsto_zero (K j) (hK j) S hS hSfin (hSupport j)
      (C * s j ^ 3) (mul_nonneg hC (pow_nonneg (hs j).le _)) hGlobal f hf B hu hw (hA j)
  refine ⟨U, fun j n => (hA j n).coeFn_toLp, fun n => ?_, ?_⟩
  · exact hMajor.of_norm_bounded (by simpa only [norm_norm] using fun j => hMaj j n)
  · simpa only [tsum_zero] using (tendsto_tsum_of_dominated_convergence (g := fun _ => 0)
      hMajor hFixed (Eventually.of_forall fun n j => hMaj j n))

end Burnett.Microlocal.Overlap
