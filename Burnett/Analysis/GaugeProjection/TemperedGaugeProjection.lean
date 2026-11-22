import Burnett.Analysis.GaugeProjection.GaugeProjectionSchwartzAction
import Burnett.Analysis.Fourier.RadianCoordinateDerivative

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.P01

open Matrix
open Burnett.A02.FrequencySplit (E tau radianFourier radianFourier_scaled)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open scoped BigOperators Matrix FourierTransform

private theorem directionProjectionEntry_symmetric (a b : Fin 4) (ξ : E) :
    directionProjectionEntry a b ξ = directionProjectionEntry b a ξ := by
  exact congrArg (fun M : Components => M b a)
    (directionProjection_transpose (fun i => ξ i))

private theorem directionProjectionEntry_frequency_sum (a : Fin 4) (ξ : E) :
    ∑ b, directionProjectionEntry a b ξ * ξ b = 0 := by
  let v : Covector := fun i => ξ i
  have hv : directionProjection v *ᵥ v = 0 := by
    by_cases h : v = 0
    · simp [h]
    · exact directionProjection_kills_covector h
  exact congrFun hv a

private theorem regularizedGaugeProjectionSymbol_left_contract (a b j : Fin 4) (ξ : E) :
    ∑ i, regularizedGaugeProjectionSymbol a b i j ξ * ξ i = 0 := by
  calc
    _ = (gaugeProjectionInfrared ‖ξ‖ * directionProjectionEntry j b ξ) *
          ∑ i, directionProjectionEntry a i ξ * ξ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [regularizedGaugeProjectionSymbol, gaugeProjectionSymbol]
      ring
    _ = _ := by rw [directionProjectionEntry_frequency_sum, mul_zero]

private theorem regularizedGaugeProjectionSymbol_right_contract (a b j : Fin 4) (ξ : E) :
    ∑ i, regularizedGaugeProjectionSymbol a b j i ξ * ξ i = 0 := by
  calc
    _ = (gaugeProjectionInfrared ‖ξ‖ * directionProjectionEntry a j ξ) *
          ∑ i, directionProjectionEntry b i ξ * ξ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [regularizedGaugeProjectionSymbol, gaugeProjectionSymbol]
      rw [directionProjectionEntry_symmetric i b ξ]
      ring
    _ = _ := by rw [directionProjectionEntry_frequency_sum, mul_zero]

private def radianEval (ξ : E) : SchwartzMap E ℂ →ₗ[ℂ] ℂ where
  toFun f := (SchwartzMap.fourierTransformCLE ℂ f) (tau⁻¹ • ξ)
  map_add' f g := by simp
  map_smul' c f := by simp

private theorem radianEval_apply (ξ : E) (f : SchwartzMap E ℂ) :
    radianEval ξ f = radianFourier f ξ := by
  change 𝓕 (f : E → ℂ) (tau⁻¹ • ξ) = radianFourier f ξ
  have ht : tau ≠ 0 := (mul_pos (show (0 : ℝ) < 2 by norm_num) Real.pi_pos).ne'
  rw [← radianFourier_scaled, smul_smul, mul_inv_cancel₀ ht, one_smul]

private theorem sameSchwartz_of_radian {f g : SchwartzMap E ℂ}
    (h : ∀ ξ, radianFourier f ξ = radianFourier g ξ) : f = g := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext ν
  simpa only [radianFourier_scaled] using h (tau • ν)

private theorem directionalSum_eq_zero_of_frequency_contract
    (f : SchwartzMap E ℂ) (F : Fin 4 → SchwartzMap E ℂ) (profile : Fin 4 → E → ℝ)
    (hF : ∀ i ξ, radianFourier (F i) ξ = (profile i ξ : ℂ) * radianFourier f ξ)
    (hzero : ∀ ξ, ∑ i, profile i ξ * ξ i = 0) :
    (∑ i, coordinateDerivative i (F i)) = 0 := by
  apply sameSchwartz_of_radian
  intro ξ
  simp only [← radianEval_apply, map_sum, map_zero]
  simp only [radianEval_apply, radianFourier_coordinateDerivative, hF]
  have hComplex : (∑ i, (profile i ξ : ℂ) * (ξ i : ℂ)) = 0 := by
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero]
      using congrArg Complex.ofReal (hzero ξ)
  calc
    _ = (Complex.I * radianFourier f ξ) * ∑ i, (profile i ξ : ℂ) * (ξ i : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hComplex, mul_zero]

/-- A tempered distribution is a continuous complex linear functional
on the Schwartz test space. -/
abbrev ChartTemperedDistribution := SchwartzMap E ℂ →L[ℂ] ℂ

def temperedSymmetrizedGradient (V : Fin 4 → ChartTemperedDistribution) :
    Fin 4 → Fin 4 → ChartTemperedDistribution :=
  fun a b => -(V b).comp (coordinateDerivative a) - (V a).comp (coordinateDerivative b)

/-- The regularized projection acts on distributions by duality with its
real even scalar multipliers on Schwartz tests. -/
def temperedGaugeProjection (T : Fin 4 → Fin 4 → ChartTemperedDistribution) :
    Fin 4 → Fin 4 → ChartTemperedDistribution :=
  fun a b => ∑ c, ∑ d, (T c d).comp (gaugeProjectionSchwartzComponent a b c d)

/-- The same fixed projection annihilates a symmetrized gradient on the
tempered dual. The proof uses exact row contractions of its actual symbol. -/
theorem temperedGaugeProjection_symmetrizedGradient (V : Fin 4 → ChartTemperedDistribution) :
    temperedGaugeProjection (temperedSymmetrizedGradient V) = 0 := by
  funext a b
  apply ContinuousLinearMap.ext
  intro f
  have first (j : Fin 4) :
      (∑ i, coordinateDerivative i (gaugeProjectionSchwartzComponent a b i j f)) = 0 :=
    directionalSum_eq_zero_of_frequency_contract f (fun i => gaugeProjectionSchwartzComponent a b i j f)
      (fun i => regularizedGaugeProjectionSymbol a b i j)
      (fun i => gaugeProjectionSchwartzComponent_radianFourier a b i j f)
      (regularizedGaugeProjectionSymbol_left_contract a b j)
  have second (j : Fin 4) :
      (∑ i, coordinateDerivative i (gaugeProjectionSchwartzComponent a b j i f)) = 0 :=
    directionalSum_eq_zero_of_frequency_contract f (fun i => gaugeProjectionSchwartzComponent a b j i f)
      (fun i => regularizedGaugeProjectionSymbol a b j i)
      (fun i => gaugeProjectionSchwartzComponent_radianFourier a b j i f)
      (regularizedGaugeProjectionSymbol_right_contract a b j)
  have hA : (∑ c, ∑ d, V d (coordinateDerivative c (gaugeProjectionSchwartzComponent a b c d f))) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← map_sum, first j, map_zero]
  have hB : (∑ c, ∑ d, V c (coordinateDerivative d (gaugeProjectionSchwartzComponent a b c d f))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [← map_sum, second j, map_zero]
  simp only [temperedGaugeProjection, temperedSymmetrizedGradient, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    Pi.zero_apply, ContinuousLinearMap.zero_apply, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    hA, hB, neg_zero, sub_zero]

end Burnett.P01
