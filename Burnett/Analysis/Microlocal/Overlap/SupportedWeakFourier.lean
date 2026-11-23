import Burnett.Analysis.Microlocal.Overlap.BoundedKernelWeakLimit
import Burnett.Analysis.Microlocal.AngularCommutator.Infrared

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.AngularCommutator
open scoped ContDiff FourierTransform InnerProduct Topology

/-- Bounded compactly supported, weakly null complex Schwartz inputs
have vanishing energy on every fixed Fourier ball. -/
theorem low_frequency_energy_tendsto_zero_of_supported_weakL2
    (K : Set E) (hK : IsCompact K) (f : ℕ → SchwartzMap E ℂ)
    (hfS : ∀ n, tsupport (f n : E → ℂ) ⊆ K)
    (B : ℝ) (hB : ∀ n, ‖(f n).toLp 2 volume‖ ≤ B)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((f n).toLp 2 volume)) atTop (𝓝 0))
    (R : ℝ) :
    Tendsto (fun n => ∫ ξ in Metric.closedBall (0 : E) R, ‖(𝓕 (f n : E → ℂ)) ξ‖ ^ 2)
      atTop (𝓝 0) := by
  let S := Metric.closedBall (0 : E) R
  let P (p : E × E) := Complex.exp ((↑(-2 * Real.pi * inner ℝ p.2 p.1) : ℂ) * Complex.I)
  let A (ξ x : E) := (S ×ˢ K).indicator P (ξ, x)
  let G (n : ℕ) := SchwartzMap.fourierTransformCLE ℂ (f n)
  let Q (n : ℕ) := S.indicator (G n : E → ℂ)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hP : Continuous P := by unfold P; fun_prop
  have hA : Measurable (uncurry A) := hP.measurable.indicator (hS.measurableSet.prod hK.measurableSet)
  have hCut (ξ x : E) (h : ξ ∉ S ∨ x ∉ K) : A ξ x = 0 :=
    indicator_of_notMem (fun hp : (ξ,x) ∈ S ×ˢ K => h.elim (fun hξ => hξ hp.1) (fun hx => hx hp.2)) _
  have hNorm (ξ x : E) : ‖A ξ x‖ ≤ 1 := by
    by_cases h : (ξ,x) ∈ S ×ˢ K
    · simp only [A, indicator_of_mem h, P, Complex.norm_exp_ofReal_mul_I, le_refl]
    · simp only [A, indicator_of_notMem h, norm_zero, zero_le_one]
  have hEq (n : ℕ) (ξ : E) : (∫ x, A ξ x * f n x) = Q n ξ := by
    by_cases hξ : ξ ∈ S
    · simp only [Q, indicator_of_mem hξ]
      change (∫ x, A ξ x * f n x) = (𝓕 (f n : E → ℂ)) ξ
      rw [Real.fourierIntegral_eq']
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ K
      · rw [show A ξ x = P (ξ,x) from
          indicator_of_mem (show (ξ,x) ∈ S ×ˢ K from ⟨hξ,hx⟩) _, smul_eq_mul]
      · have hz : f n x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hs => hx (hfS n hs))
        rw [hCut ξ x (.inr hx), hz, zero_mul, smul_zero]
    · simp only [Q, indicator_of_notMem hξ, hCut ξ _ (.inl hξ), zero_mul, integral_zero]
  let hQ (n : ℕ) : MemLp (Q n) 2 volume := ((G n).memLp 2 volume).indicator hS.measurableSet
  have hMem (n : ℕ) : MemLp (fun ξ => ∫ x, A ξ x * f n x) 2 volume :=
    (hQ n).ae_eq (Eventually.of_forall (fun ξ => (hEq n ξ).symm))
  have hStrong := boundedKernel_action_tendsto_zero A hA (S ∪ K)
    (hS.union hK).measurableSet (hS.union hK).measure_lt_top.ne
    (fun ξ x h => hCut ξ x (h.imp
      (fun hξ hξ' => hξ (.inl hξ')) (fun hx hx' => hx (.inr hx'))))
    1 zero_le_one hNorm (fun n => (f n : E → ℂ))
    (fun n => (f n).memLp 2 volume) B hB hw hMem
  have hLpEq (n : ℕ) : (hMem n).toLp (fun ξ => ∫ x, A ξ x * f n x) = (hQ n).toLp (Q n) := by
    apply Lp.ext
    filter_upwards [(hMem n).coeFn_toLp, (hQ n).coeFn_toLp] with ξ h₁ h₂
    rw [h₁, h₂, hEq n ξ]
  have hSq (n : ℕ) : ‖(hQ n).toLp (Q n)‖ ^ 2 =
      ∫ ξ in S, ‖(𝓕 (f n : E → ℂ)) ξ‖ ^ 2 := by
    rw [l2_norm_sq_integral, ← integral_indicator hS.measurableSet]
    apply integral_congr_ae
    filter_upwards [(hQ n).coeFn_toLp] with ξ hξ
    rw [hξ]
    by_cases hx : ξ ∈ S
    · rw [show Q n ξ = G n ξ from indicator_of_mem hx _, indicator_of_mem hx]
      rfl
    · simp only [Q, indicator_of_notMem hx, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simpa only [hLpEq, hSq, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hStrong.norm.pow 2

/-- The actual angular commutator vanishes on a compactly supported
Schwartz family under complex weak L² convergence. -/
theorem cutoffCommutator_tendsto_zero_of_supported_weakL2
    (m χ : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ))
    (hχ : ContDiff ℝ ∞ (χ : E → ℂ)) (hcχ : HasCompactSupport (χ : E → ℂ))
    (K : Set E) (hK : IsCompact K) (f : ℕ → SchwartzMap E ℂ)
    (hfS : ∀ n, tsupport (f n : E → ℂ) ⊆ K)
    (B : ℝ) (hB : ∀ n, ‖(f n).toLp 2 volume‖ ≤ B)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((f n).toLp 2 volume)) atTop (𝓝 0)) :
    Tendsto (fun n => cutoffCommutator m χ ((f n).toLp 2 volume)) atTop (𝓝 0) := by
  let G (n : ℕ) := SchwartzMap.fourierTransformCLE ℂ (f n)
  let hG (n : ℕ) : MemLp (G n : E → ℂ) 2 volume := (G n).memLp 2 volume
  have hInv (n : ℕ) : fourierL2Equiv.symm ((hG n).toLp (G n)) = (f n).toLp 2 volume := by
    change fourierL2Equiv.symm ((G n).toLp 2 volume) = _
    rw [← fourierL2Equiv_schwartz, fourierL2Equiv.symm_apply_apply]
  have hGN (n : ℕ) : ‖(hG n).toLp (G n)‖ ≤ B := by
    change ‖(G n).toLp 2 volume‖ ≤ B
    rw [← fourierL2Equiv_schwartz, LinearIsometryEquiv.norm_map]
    exact hB n
  have hLow (R : ℝ) (_ : 0 < R) :
      Tendsto (fun n => ∫ ξ in Metric.closedBall (0 : E) R, ‖G n ξ‖^2) atTop (𝓝 0) :=
    low_frequency_energy_tendsto_zero_of_supported_weakL2 K hK f hfS B hB hw R
  have h := cutoffCommutator_tendsto_zero_of_low_energy m χ hm hd hχ hcχ
    (fun n => (G n : E → ℂ)) (fun n => (G n).continuous.measurable)
    (fun n => (G n).integrable) hG B ((norm_nonneg _).trans (hB 0)) hGN hLow
  simpa only [hInv] using h

end Burnett.Microlocal.Overlap
