import Burnett.Analysis.Microlocal.Overlap.BaseFourierAction
import Burnett.Analysis.Microlocal.Overlap.BoundedKernelWeakLimit

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularDyadicKernel (E)
open scoped FourierTransform InnerProduct Topology ENNReal

/-- The left action of a bounded symbol supported in a compact rectangle
of base and frequency variables is strongly null on weakly null inputs. -/
theorem exists_compactFrequency_leftAction_strongZero
    (a : E → E → ℂ) (ha : Measurable (uncurry a))
    (S Q : Set E) (hS : IsCompact S) (hQ : IsCompact Q)
    (hSupport : ∀ x ξ, x ∉ S ∨ ξ ∉ Q → a x ξ = 0)
    (C : ℝ) (hC : 0 ≤ C) (hBound : ∀ x ξ, ‖a x ξ‖ ≤ C)
    (f : ℕ → SchwartzMap E ℂ) (B : ℝ) (hB : ∀ n, ‖(f n).toLp 2 volume‖ ≤ B)
    (hw : ∀ w : ComplexL2 E,
      Tendsto (fun n => inner ℂ w ((f n).toLp 2 volume)) atTop (𝓝 0)) :
    ∃ A : ℕ → ComplexL2 E, (∀ n, A n =ᵐ[volume] firstOrderAction a (f n)) ∧
      Tendsto A atTop (𝓝 0) := by
  let H (x ξ : E) := baseFourierPhase ξ x * a x ξ
  let F (n : ℕ) := SchwartzMap.fourierTransformCLE ℂ (f n)
  have hH : Measurable (uncurry H) :=
    (baseFourierPhase_continuous.measurable.comp measurable_swap).mul ha
  have hHBound (x ξ : E) : ‖H x ξ‖ ≤ C := by
    simpa only [H, norm_mul, baseFourierPhase_norm, one_mul] using hBound x ξ
  have hHZ (x ξ : E) (h : x ∉ S ∨ ξ ∉ Q) : H x ξ = 0 := by
    simp only [H, hSupport x ξ h, mul_zero]
  have hA (n : ℕ) : MemLp (fun x => ∫ ξ, H x ξ * F n ξ) 2 volume := by
    let D := C * ∫ ξ, ‖F n ξ‖
    have hD : 0 ≤ D := mul_nonneg hC (integral_nonneg fun _ => norm_nonneg _)
    have hJoint : StronglyMeasurable (fun q : E × E => H q.1 q.2 * F n q.2) :=
      (hH.mul ((F n).continuous.measurable.comp measurable_snd)).stronglyMeasurable
    have hMeas : Measurable (fun x => ∫ ξ, H x ξ * F n ξ) :=
      (hJoint.integral_prod_right' (ν := (volume : Measure E))).measurable
    refine (memLp_indicator_const 2 hS.measurableSet D (Or.inr hS.measure_lt_top.ne)).mono
      hMeas.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, Real.norm_of_nonneg hD]
      have hInt : Integrable (fun ξ => C * ‖F n ξ‖) := (F n).integrable.norm.const_mul C
      have hN := norm_integral_le_of_norm_le hInt
        (Eventually.of_forall fun ξ => show ‖H x ξ * F n ξ‖ ≤ C * ‖F n ξ‖ by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hHBound x ξ) (norm_nonneg _))
      simpa only [D, integral_const_mul] using hN
    · simp only [hHZ x _ (Or.inl hx), zero_mul, integral_zero, indicator_of_notMem hx, norm_zero, le_refl]
  have hFw (w : ComplexL2 E) :
      Tendsto (fun n => inner ℂ w ((F n).toLp 2 volume)) atTop (𝓝 0) := by
    have hP (n : ℕ) : inner ℂ w ((F n).toLp 2 volume) =
        inner ℂ ((fourierL2Equiv (V := E)).symm w) ((f n).toLp 2 volume) := by
      rw [show (F n).toLp 2 volume = fourierL2Equiv ((f n).toLp 2 volume)
        from (fourierL2Equiv_schwartz (f n)).symm]
      conv_lhs => rw [← (fourierL2Equiv (V := E)).apply_symm_apply w]
      exact (fourierL2Equiv (V := E)).inner_map_map _ _
    simpa only [hP] using hw ((fourierL2Equiv (V := E)).symm w)
  have hZero := boundedKernel_action_tendsto_zero H hH (S ∪ Q)
    (hS.measurableSet.union hQ.measurableSet) (hS.union hQ).measure_lt_top.ne
    (fun x ξ h => hHZ x ξ (h.imp
      (fun hx hs => hx (Or.inl hs)) (fun hξ hq => hξ (Or.inr hq)))) C hC hHBound
    (fun n => (F n : E → ℂ)) (fun n => (F n).memLp 2 volume) B
    (fun n => (schwartz_fourier_toLp_norm (f n)).trans_le (hB n)) hFw hA
  refine ⟨_, fun n => ((hA n).coeFn_toLp).trans (Eventually.of_forall fun x => ?_), hZero⟩
  rw [firstOrderAction, Real.fourierIntegralInv_eq']
  simp only [H, baseFourierPhase, smul_eq_mul, mul_assoc]
  rfl

end Burnett.Microlocal.Overlap
