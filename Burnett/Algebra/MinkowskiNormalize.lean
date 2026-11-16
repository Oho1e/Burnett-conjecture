import Burnett.Algebra.FrameComposition
import Burnett.Algebra.MinkowskiNull

/-!
# Normalizing every nonzero Minkowski-null covector

One or two actual Lorentz reflections send the given covector to (-1,1,0,0).
Their coordinate maps are involutions and their inverse metric is computed
directly as E η Eᵀ, in the orientation required by LorentzFrame.
-/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Burnett.RicciSymbol.MinkowskiNormalize

open scoped BigOperators
open TensorFrame NullScreen

private theorem standard_eq_minkowski : standardInverse = minkowskiInverse := rfl

def pairing (u v : Covector) : ℝ := ∑ a, signature a * u a * v a

theorem pairing_comm (u v : Covector) : pairing u v = pairing v u := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem pairing_sub_left (u v w : Covector) :
    pairing (u - v) w = pairing u w - pairing v w := by
  simp only [pairing, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem pairing_sub_right (u v w : Covector) :
    pairing u (v - w) = pairing u v - pairing u w := by
  simp only [pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pairing_smul_right (u v : Covector) (r : ℝ) :
    pairing u (r • v) = r * pairing u v := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem pairing_self (u : Covector) : pairing u u = symbolNorm minkowskiInverse u := by
  rw [symbolNorm_eq_metricTrace, ← standard_eq_minkowski, metricTrace_standard]
  simp only [pairing, mul_assoc]

def reflectionComponents (d : Covector) : Tensor2 := fun i a =>
  (if i = a then 1 else 0) - 2 * signature i * d i * d a / pairing d d

def reflection (d ξ : Covector) : Covector :=
  ξ - (2 * pairing d ξ / pairing d d) • d

theorem covector_reflection (d ξ : Covector) :
    covector (reflectionComponents d) ξ = reflection d ξ := by
  funext a
  simp only [covector, reflectionComponents, reflection, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
  have hdiag : (∑ i : Index, (if i = a then (1 : ℝ) else 0) * ξ i) = ξ a := by
    simp [ite_mul]
  rw [hdiag]
  congr 1
  simp only [pairing, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairing_reflection (d ξ : Covector) (hd : pairing d d ≠ 0) :
    pairing d (reflection d ξ) = -pairing d ξ := by
  rw [reflection, pairing_sub_right, pairing_smul_right]
  field_simp [hd]
  ring

theorem reflection_involutive (d : Covector) (hd : pairing d d ≠ 0) :
    Function.Involutive (reflection d) := by
  intro ξ
  have hpair := pairing_reflection d ξ hd
  funext a
  simp only [reflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hpair ⊢
  rw [hpair]
  field_simp [hd]
  ring

/-- The metric identity is calculated in the required E η Eᵀ direction. -/
theorem reflection_inverseMetric (d : Covector) (hd : pairing d d ≠ 0) :
    inverseMetric (reflectionComponents d) = standardInverse := by
  funext i j
  have hlead : (∑ a : Index, signature a * (if i = a then (1 : ℝ) else 0) *
      (if j = a then (1 : ℝ) else 0)) = standardInverse i j := by
    by_cases hij : i = j
    · subst j
      simp [standardInverse, mul_ite]
    · simp [standardInverse, mul_ite, hij]
  have hi : (∑ a : Index, signature a * (if i = a then (1 : ℝ) else 0) * d a) =
      signature i * d i := by simp [ite_mul, mul_ite]
  have hj : (∑ a : Index, signature a * (if j = a then (1 : ℝ) else 0) * d a) =
      signature j * d j := by simp [ite_mul, mul_ite]
  calc
    _ = (∑ a : Index, signature a * (if i = a then (1 : ℝ) else 0) *
          (if j = a then (1 : ℝ) else 0)) -
        (2 * signature j * d j / pairing d d) *
          (∑ a : Index, signature a * (if i = a then (1 : ℝ) else 0) * d a) -
        (2 * signature i * d i / pairing d d) *
          (∑ a : Index, signature a * (if j = a then (1 : ℝ) else 0) * d a) +
        ((2 * signature i * d i / pairing d d) *
          (2 * signature j * d j / pairing d d)) *
          (∑ a : Index, signature a * d a * d a) := by
      simp only [inverseMetric, reflectionComponents, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = _ := by
      rw [hlead, hi, hj]
      change standardInverse i j -
        (2 * signature j * d j / pairing d d) * (signature i * d i) -
        (2 * signature i * d i / pairing d d) * (signature j * d j) +
        ((2 * signature i * d i / pairing d d) *
          (2 * signature j * d j / pairing d d)) * pairing d d = standardInverse i j
      field_simp [hd]
      ring

def reflectionFrame (d : Covector) (hd : pairing d d ≠ 0) : LorentzFrame minkowskiInverse where
  components := reflectionComponents d
  isBasis := by
    have hinv : Function.Involutive (covector (reflectionComponents d)) := by
      intro ξ
      simpa only [covector_reflection] using reflection_involutive d hd ξ
    constructor
    · intro ξ ζ h
      calc
        ξ = covector (reflectionComponents d) (covector (reflectionComponents d) ξ) := (hinv ξ).symm
        _ = covector (reflectionComponents d) (covector (reflectionComponents d) ζ) := congrArg _ h
        _ = ζ := hinv ζ
    · intro ξ
      exact ⟨covector (reflectionComponents d) ξ, hinv ξ⟩
  inverseMetric_eq := by rw [reflection_inverseMetric d hd, standard_eq_minkowski]

theorem null_difference_norm (ξ ζ : Covector)
    (hξ : symbolNorm minkowskiInverse ξ = 0) (hζ : symbolNorm minkowskiInverse ζ = 0) :
    pairing (ξ - ζ) (ξ - ζ) = -2 * pairing ξ ζ := by
  rw [pairing_sub_left, pairing_sub_right, pairing_sub_right,
    pairing_self ξ, pairing_self ζ, hξ, hζ, pairing_comm ζ ξ]
  ring

theorem null_difference_ne_zero (ξ ζ : Covector)
    (hξ : symbolNorm minkowskiInverse ξ = 0) (hζ : symbolNorm minkowskiInverse ζ = 0)
    (hp : pairing ξ ζ ≠ 0) : pairing (ξ - ζ) (ξ - ζ) ≠ 0 := by
  rw [null_difference_norm ξ ζ hξ hζ]
  exact mul_ne_zero (by norm_num) hp

def nullReflectionFrame (ξ ζ : Covector)
    (hξ : symbolNorm minkowskiInverse ξ = 0) (hζ : symbolNorm minkowskiInverse ζ = 0)
    (hp : pairing ξ ζ ≠ 0) : LorentzFrame minkowskiInverse :=
  reflectionFrame (ξ - ζ) (null_difference_ne_zero ξ ζ hξ hζ hp)

theorem nullReflectionFrame_sends (ξ ζ : Covector)
    (hξ : symbolNorm minkowskiInverse ξ = 0) (hζ : symbolNorm minkowskiInverse ζ = 0)
    (hp : pairing ξ ζ ≠ 0) :
    covector (nullReflectionFrame ξ ζ hξ hζ hp).components ξ = ζ := by
  change covector (reflectionComponents (ξ - ζ)) ξ = ζ
  rw [covector_reflection]
  have hcross : pairing (ξ - ζ) ξ = -pairing ξ ζ := by
    rw [pairing_sub_left, pairing_self ξ, hξ, pairing_comm ζ ξ]
    ring
  funext a
  simp only [reflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [null_difference_norm ξ ζ hξ hζ, hcross]
  field_simp [hp]
  ring

def oppositeNullCovector : Covector := fun a =>
  if a = 0 then -1 else if a = 1 then -1 else 0

theorem oppositeNullCovector_symbolNorm : symbolNorm minkowskiInverse oppositeNullCovector = 0 := by
  simp [symbolNorm, minkowskiInverse, oppositeNullCovector, Fin.sum_univ_succ, Fin.isValue]

theorem pairing_nullCovector (ξ : Covector) : pairing ξ nullCovector = ξ 0 + ξ 1 := by
  simp [pairing, signature, nullCovector, Fin.sum_univ_succ, Fin.isValue]

theorem pairing_oppositeNullCovector (ξ : Covector) :
    pairing ξ oppositeNullCovector = ξ 0 - ξ 1 := by
  simp [pairing, signature, oppositeNullCovector, Fin.sum_univ_succ, Fin.isValue, sub_eq_add_neg]

theorem opposite_pairing_ne_zero : pairing oppositeNullCovector nullCovector ≠ 0 := by
  rw [pairing_nullCovector]
  norm_num [oppositeNullCovector]

/-- Every nonzero null covector is normalized by a constructed actual frame,
using one reflection or a composition of two reflections. -/
theorem exists_normalizing_frame (ξ : Covector) (hξ : ξ ≠ 0)
    (hs : symbolNorm minkowskiInverse ξ = 0) :
    ∃ frame : LorentzFrame minkowskiInverse, covector frame.components ξ = nullCovector := by
  by_cases hp : pairing ξ nullCovector ≠ 0
  · exact ⟨nullReflectionFrame ξ nullCovector hs nullCovector_symbolNorm hp,
      nullReflectionFrame_sends ξ nullCovector hs nullCovector_symbolNorm hp⟩
  · have hpair : ξ 0 + ξ 1 = 0 := by
      simpa only [pairing_nullCovector] using not_ne_iff.mp hp
    have h0 := MinkowskiNull.temporal_component_ne_zero ξ hξ hs
    have hpm : pairing ξ oppositeNullCovector ≠ 0 := by
      rw [pairing_oppositeNullCovector]
      intro h
      apply h0
      linarith
    let first := nullReflectionFrame ξ oppositeNullCovector hs oppositeNullCovector_symbolNorm hpm
    let second := nullReflectionFrame oppositeNullCovector nullCovector
      oppositeNullCovector_symbolNorm nullCovector_symbolNorm opposite_pairing_ne_zero
    refine ⟨FrameComposition.composeFrames minkowskiInverse first second, ?_⟩
    rw [FrameComposition.covector_composeFrames]
    change covector second.components
      (covector (nullReflectionFrame ξ oppositeNullCovector hs oppositeNullCovector_symbolNorm hpm).components ξ) = nullCovector
    rw [nullReflectionFrame_sends ξ oppositeNullCovector hs oppositeNullCovector_symbolNorm hpm]
    exact nullReflectionFrame_sends oppositeNullCovector nullCovector
      oppositeNullCovector_symbolNorm nullCovector_symbolNorm opposite_pairing_ne_zero

end Burnett.RicciSymbol.MinkowskiNormalize
