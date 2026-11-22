import Burnett.Analysis.GaugeProjection.ProjectedDefectHalfDensity

set_option autoImplicit false
set_option maxHeartbeats 4900000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter Burnett.Fourier
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped BigOperators ContDiff Topology

/-- The fixed compactly supported half-density can move through the actual
matrix projection on all ordered components of the same weakly null field. -/
theorem projectionFullSchwartz_halfDensity_sub_tendsto_zero
    (ρ : BoundedSymbol E) (d : D) (hρ : ∀ x, ρ x = ((d : E → ℝ) x : ℂ))
    (f : ℕ → Fin 4 → Fin 4 → E → ℝ) (hf : ∀ n i j, ContDiff ℝ ∞ (f n i j))
    (fLp : ∀ n i j, MemLp (f n i j) 2 (volume : Measure E))
    (χ₀ : D) (hCut : ∀ n i j x, f n i j x ≠ 0 → (χ₀ : E → ℝ) x = 1)
    (B : ℝ) (hB : ∀ n i j, ‖(fLp n i j).toLp (f n i j)‖ ≤ B)
    (hWeak : ∀ i j (φ : D), Tendsto (fun n => ∫ x, f n i j x * (φ : E → ℝ) x) atTop (𝓝 0)) :
    let w := fun n i j => sourceSchwartz (hf n i j) χ₀ (hCut n i j)
    let v := fun n i j => sourceSchwartz ((test_smooth d).mul (hf n i j)) χ₀
      (fun x h => hCut n i j x (fun h₀ => h (mul_eq_zero.mpr (Or.inr h₀))))
    Tendsto (fun n => projectionMatrixToL2 (projectionFullSchwartz (v n)) -
      (fun i j => symbolCLM ρ ((projectionFullSchwartz (w n) i j).toLp 2 volume)))
      atTop (𝓝 0) := by
  intro w v
  let L := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  let D (n : ℕ) (a b : Fin 4) :=
    L (gaugeProjectionSchwartzComponent i j a b (v n a b)) -
      symbolCLM ρ (L (gaugeProjectionSchwartzComponent i j a b (w n a b)))
  have hD (a b : Fin 4) : Tendsto (fun n => D n a b) atTop (𝓝 0) :=
    projectedDefectComponent_halfDensity_commutator_tendsto_zero i j a b ρ d hρ
      (fun n => f n a b) (fun n => hf n a b) (fun n => fLp n a b)
      χ₀ (fun n => hCut n a b) B (fun n => hB n a b) (hWeak a b)
  have hSum (n : ℕ) :
      (projectionMatrixToL2 (projectionFullSchwartz (v n)) -
        (fun p q => symbolCLM ρ ((projectionFullSchwartz (w n) p q).toLp 2 volume))) i j =
        ∑ a, ∑ b, D n a b := by
    change L (∑ a, ∑ b, gaugeProjectionSchwartzComponent i j a b (v n a b)) -
      symbolCLM ρ (L (∑ a, ∑ b, gaugeProjectionSchwartzComponent i j a b (w n a b))) = _
    simp only [map_sum, Finset.sum_sub_distrib, D]
  have ht := tendsto_finset_sum (Finset.univ : Finset (Fin 4)) (fun a _ =>
    tendsto_finset_sum (Finset.univ : Finset (Fin 4)) (fun b _ => hD a b))
  simpa only [hSum, Pi.zero_apply, Finset.sum_const_zero] using ht

/-- Testing two L² fields against a fixed bounded operator is unchanged in
the limit by two strongly vanishing L² errors. -/
theorem defectPairing_sub_tendsto_zero_of_strong_errors
    (T : ComplexL2 E →L[ℂ] ComplexL2 E)
    (u v u' v' : ℕ → ComplexL2 E) (B C : ℝ)
    (hU : ∀ n, ‖u n‖ ≤ B) (hV' : ∀ n, ‖v' n‖ ≤ C)
    (hU' : Tendsto (fun n => u' n - u n) atTop (𝓝 0))
    (hV : Tendsto (fun n => v' n - v n) atTop (𝓝 0)) :
    Tendsto (fun n => inner ℂ (u' n) (T (v' n)) - inner ℂ (u n) (T (v n))) atTop (𝓝 0) := by
  have hL : Tendsto (fun n => inner ℂ (u' n - u n) (T (v' n))) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).2
    refine squeeze_zero (g := fun n => ‖u' n - u n‖ * (‖T‖ * C))
      (fun n => norm_nonneg _) (fun n => ?_) ?_
    · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul_of_nonneg_left
        ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hV' n) (norm_nonneg _))) (norm_nonneg _))
    · simpa only [norm_zero, zero_mul] using hU'.norm.mul (tendsto_const_nhds (x := ‖T‖ * C))
  have hv := T.continuous.continuousAt (x := 0).tendsto.comp hV
  have hR : Tendsto (fun n => inner ℂ (u n) (T (v' n - v n))) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).2
    refine squeeze_zero (g := fun n => B * ‖T (v' n - v n)‖)
      (fun n => norm_nonneg _) (fun n => ?_) ?_
    · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul_of_nonneg_right (hU n) (norm_nonneg _))
    · simpa only [Function.comp_apply, map_zero, norm_zero, mul_zero] using (tendsto_const_nhds (x := B)).mul hv.norm
  have h := hL.add hR
  rw [zero_add] at h
  refine h.congr (fun n => ?_)
  rw [inner_sub_left, map_sub, inner_sub_right]
  abel

end Burnett.P01
