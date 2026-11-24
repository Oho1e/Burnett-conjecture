import Burnett.Analysis.Microlocal.BesselLocalization

/-! A smooth first-order row maps a strongly vanishing L² error to a strongly vanishing negative-energy error. -/
set_option autoImplicit false
set_option maxRecDepth 2700
set_option maxHeartbeats 1000000

noncomputable section
namespace Burnett.Microlocal.BesselLocalization

open Filter MeasureTheory Burnett.Fourier
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.X02.SobolevTestJet (D Space)
open scoped BigOperators Topology

private theorem coeffMul_sub (a : D) (f g : SchwartzMap Space ℂ) :
    coeffMul a (f - g) = coeffMul a f - coeffMul a g := by
  ext x
  change ((a : Space → ℝ) x : ℂ) * (f x - g x) =
    ((a : Space → ℝ) x : ℂ) * f x - ((a : Space → ℝ) x : ℂ) * g x
  rw [mul_sub]

variable {J L I : Type*} [Fintype J] [Fintype L]

theorem firstOrderRow_sub (a : J → D) (v : J → Space) (i : J → I) (b : L → D) (j : L → I)
    (f g : I → SchwartzMap Space ℂ) :
    firstOrderRow a v i b j (fun k => f k - g k) = firstOrderRow a v i b j f - firstOrderRow a v i b j g := by
  simp only [firstOrderRow, map_sub, coeffMul_sub, Finset.sum_sub_distrib]
  abel

theorem tendsto_besselLp_iff_negativeEnergy_tendsto_zero (f : ℕ → SchwartzMap Space ℂ) :
    Tendsto (fun n => fourierMultiplier besselSymbol ((f n).toLp 2 volume)) atTop (𝓝 0) ↔
      Tendsto (fun n => negativeEnergy (f n)) atTop (𝓝 0) := by
  constructor
  · intro h
    simpa only [besselLp_norm_sq_eq_negativeEnergy, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using h.norm.pow 2
  · intro h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hNorm (n : ℕ) : ‖fourierMultiplier besselSymbol ((f n).toLp 2 volume)‖ =
        Real.sqrt (negativeEnergy (f n)) := by
      rw [← besselLp_norm_sq_eq_negativeEnergy, Real.sqrt_sq (norm_nonneg _)]
    simp_rw [hNorm]
    simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp h

private theorem operator_map_tendsto_zero (T : ComplexL2 Space →L[ℂ] ComplexL2 Space)
    (u : ℕ → ComplexL2 Space) (h : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => T (u n)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, map_zero] using (T.continuous.tendsto 0).comp h

/-- Inverse Bessel regularization controls the genuine row of derivatives
and its lower-order terms on a strongly vanishing componentwise L² family. -/
theorem bessel_firstOrderRow_tendsto_zero_of_strongL2
    (a : J → D) (v : J → Space) (i : J → I) (b : L → D) (j : L → I)
    (f : ℕ → I → SchwartzMap Space ℂ)
    (hF : ∀ k : I, Tendsto (fun n => (f n k).toLp 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => fourierMultiplier besselSymbol ((firstOrderRow a v i b j (f n)).toLp 2 volume))
      atTop (𝓝 0) := by
  let T := (fourierMultiplier besselSymbol).comp (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space))
  have hMain (s : J) : Tendsto (fun n => T (coeffMul (a s) (SchwartzMap.pderivCLM ℂ (v s) (f n (i s)))))
      atTop (𝓝 0) := by
    let E₁ := (fourierMultiplier (regularizedDirectionSymbol (v s))).comp (symbolCLM (physicalCoefficient (a s)))
    let E₂ := (fourierMultiplier besselSymbol).comp (symbolCLM (physicalCoefficient (coefficientPDeriv (a s) (v s))))
    have h := (operator_map_tendsto_zero E₁ _ (hF (i s))).sub (operator_map_tendsto_zero E₂ _ (hF (i s)))
    simp only [T, ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply]
    simp_rw [besselLp_coeffMul_pderiv, coeffMul_toLp]
    simpa only [E₁, E₂, ContinuousLinearMap.comp_apply, sub_zero] using h
  have hLower (s : L) : Tendsto (fun n => T (coeffMul (b s) (f n (j s)))) atTop (𝓝 0) := by
    simpa only [T, ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply, coeffMul_toLp] using
      operator_map_tendsto_zero ((fourierMultiplier besselSymbol).comp (symbolCLM (physicalCoefficient (b s))))
        _ (hF (j s))
  change Tendsto (fun n => T (firstOrderRow a v i b j (f n))) atTop (𝓝 0)
  simp only [firstOrderRow, map_add, map_sum]
  simpa only [Finset.sum_const_zero, add_zero] using
    (tendsto_finset_sum Finset.univ (fun s _ => hMain s)).add (tendsto_finset_sum Finset.univ (fun s _ => hLower s))

/-- The same first-order row has equivalent strong negative-energy behavior
on two local source sequences whose actual L² difference tends to zero. -/
theorem negativeEnergy_firstOrderRow_tendsto_zero_of_strongL2_replacement
    (a : J → D) (v : J → Space) (i : J → I) (b : L → D) (j : L → I)
    (f g : ℕ → I → SchwartzMap Space ℂ)
    (hDiff : ∀ k : I, Tendsto (fun n => (f n k).toLp 2 volume - (g n k).toLp 2 volume) atTop (𝓝 0))
    (hG : Tendsto (fun n => negativeEnergy (firstOrderRow a v i b j (g n))) atTop (𝓝 0)) :
    Tendsto (fun n => negativeEnergy (firstOrderRow a v i b j (f n))) atTop (𝓝 0) := by
  let F (n : ℕ) := firstOrderRow a v i b j (f n)
  let G (n : ℕ) := firstOrderRow a v i b j (g n)
  let T := (fourierMultiplier besselSymbol).comp (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space))
  have hDiff' (k : I) : Tendsto (fun n => (f n k - g n k).toLp 2 volume) atTop (𝓝 0) := by
    have hSub (n : ℕ) : (f n k - g n k).toLp 2 volume = (f n k).toLp 2 volume - (g n k).toLp 2 volume :=
      (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)).map_sub (f n k) (g n k)
    simpa only [hSub] using hDiff k
  have hBessel := bessel_firstOrderRow_tendsto_zero_of_strongL2 a v i b j (fun n k => f n k - g n k) hDiff'
  change Tendsto (fun n => T (firstOrderRow a v i b j (fun k => f n k - g n k))) atTop (𝓝 0) at hBessel
  simp only [firstOrderRow_sub, map_sub] at hBessel
  change Tendsto (fun n => T (F n) - T (G n)) atTop (𝓝 0) at hBessel
  have hG' : Tendsto (fun n => T (G n)) atTop (𝓝 0) :=
    (tendsto_besselLp_iff_negativeEnergy_tendsto_zero G).mpr hG
  apply (tendsto_besselLp_iff_negativeEnergy_tendsto_zero F).mp
  change Tendsto (fun n => T (F n)) atTop (𝓝 0)
  simpa only [sub_add_cancel, zero_add] using hBessel.add hG'

end Burnett.Microlocal.BesselLocalization
