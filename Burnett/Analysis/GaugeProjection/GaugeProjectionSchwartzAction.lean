import Burnett.Analysis.GaugeProjection.GaugeProjectionTemperate
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualSymbolInputs

set_option autoImplicit false
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.P01

open Burnett.A02.FrequencySplit
  (E tau radianFourier radianFourier_scaled radianAction radianActionSpectrum radianActionSpectrum_inverse)
open scoped BigOperators ContDiff FourierTransform

private def frequencyDilation : E →L[ℝ] E := tau • ContinuousLinearMap.id ℝ E

private theorem order_le_smooth (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

private theorem scaledComplexProjectionSymbol_hasTemperateGrowth (a b c d : Fin 4) :
    Function.HasTemperateGrowth
      (fun ν : E => (regularizedGaugeProjectionSymbol a b c d (tau • ν) : ℂ)) := by
  let m := regularizedGaugeProjectionSymbol a b c d
  let L := frequencyDilation
  have hm : Function.HasTemperateGrowth m := regularizedGaugeProjectionSymbol_hasTemperateGrowth a b c d
  have hComp : ContDiff ℝ ∞ (m ∘ L) := hm.1.comp L.contDiff
  refine ⟨Complex.ofRealCLM.contDiff.comp hComp, fun n => ?_⟩
  obtain ⟨k,C,hC⟩ := hm.2 n
  let S := max 1 ‖L‖
  let M := max 0 C
  have hM : 0 ≤ M := le_max_left _ _
  have hS : 0 ≤ S := le_trans zero_le_one (le_max_left _ _)
  have hScale (x : E) : 1 + ‖L x‖ ≤ S * (1 + ‖x‖) := by
    calc
      _ ≤ S + S * ‖x‖ :=
        add_le_add (le_max_left _ _) ((L.le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
      _ = _ := by rw [mul_add, mul_one]
  refine ⟨k, (M * S^k) * ‖L‖^n, fun x => ?_⟩
  change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ (m ∘ L)) x‖ ≤ _
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hComp.contDiffAt (order_le_smooth n),
    L.iteratedFDeriv_comp_right hm.1 x (order_le_smooth n)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n m (L x)‖ * ∏ _ : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ n m (L x)‖ * ‖L‖^n := by simp
    _ ≤ (M * (S * (1 + ‖x‖))^k) * ‖L‖^n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
      refine (hC (L x)).trans ?_
      exact (mul_le_mul_of_nonneg_right (le_max_right 0 C) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hScale x) k) hM)
    _ = _ := by rw [mul_pow]; ring

/-- The projection's scalar Fourier multiplier as an actual Schwartz map. -/
def gaugeProjectionSchwartzComponent (a b c d : Fin 4) :
    SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm.toContinuousLinearMap.comp
    ((SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
      (scaledComplexProjectionSymbol_hasTemperateGrowth a b c d)).comp
      (SchwartzMap.fourierTransformCLE ℂ).toContinuousLinearMap)

private theorem gaugeProjectionSchwartzComponent_fourier (a b c d : Fin 4)
    (f : SchwartzMap E ℂ) (ν : E) :
    𝓕 (gaugeProjectionSchwartzComponent a b c d f : E → ℂ) ν =
      (regularizedGaugeProjectionSymbol a b c d (tau • ν) : ℂ) * 𝓕 (f : E → ℂ) ν := by
  unfold gaugeProjectionSchwartzComponent
  change SchwartzMap.fourierTransformCLE ℂ
      ((SchwartzMap.fourierTransformCLE ℂ).symm
        (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
          (scaledComplexProjectionSymbol_hasTemperateGrowth a b c d)
          (SchwartzMap.fourierTransformCLE ℂ f))) ν = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change 𝓕 (f : E → ℂ) ν * (regularizedGaugeProjectionSymbol a b c d (tau • ν) : ℂ) = _
  exact mul_comm _ _

theorem gaugeProjectionSchwartzComponent_radianFourier (a b c d : Fin 4)
    (f : SchwartzMap E ℂ) (ξ : E) :
    radianFourier (gaugeProjectionSchwartzComponent a b c d f) ξ =
      (regularizedGaugeProjectionSymbol a b c d ξ : ℂ) * radianFourier f ξ := by
  have ht : tau ≠ 0 := (mul_pos (show (0 : ℝ) < 2 by norm_num) Real.pi_pos).ne'
  let ν := tau⁻¹ • ξ
  have hν : tau • ν = ξ := by
    dsimp only [ν]
    rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
  rw [← hν, radianFourier_scaled, radianFourier_scaled]
  exact gaugeProjectionSchwartzComponent_fourier a b c d f ν

theorem gaugeProjectionSchwartzComponent_eq_radianAction (a b c d : Fin 4)
    (f : SchwartzMap E ℂ) :
    (gaugeProjectionSchwartzComponent a b c d f : E → ℂ) =
      radianAction (regularizedGaugeProjectionSymbol a b c d) f := by
  let u := gaugeProjectionSchwartzComponent a b c d f
  have hSpectrum : 𝓕 (u : E → ℂ) =
      radianActionSpectrum (regularizedGaugeProjectionSymbol a b c d) f :=
    funext (gaugeProjectionSchwartzComponent_fourier a b c d f)
  calc
    (u : E → ℂ) = 𝓕⁻ (𝓕 (u : E → ℂ)) :=
      (u.continuous.fourier_inversion u.integrable (SchwartzMap.fourierTransformCLM ℂ u).integrable).symm
    _ = _ := by rw [hSpectrum, radianActionSpectrum_inverse]

end Burnett.P01
