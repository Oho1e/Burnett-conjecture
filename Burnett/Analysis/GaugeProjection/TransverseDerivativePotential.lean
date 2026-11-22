import Burnett.Analysis.GaugeProjection.GaugeProjectionFourier
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2800000

noncomputable section

namespace Burnett.P01

open Burnett.A02.FrequencySplit (E)
open scoped BigOperators

/-- The antisymmetric potential whose divergence differentiates a transverse
Fourier field. The coordinate choice is the same as for the projection. -/
def transverseDerivativePotential (b : Fin 4) (ξ : E) (w : ComplexCovector) : ComplexComponents :=
  fun j i => (ξ b : ℂ) / ((‖ξ‖^2 : ℝ) : ℂ) *
    ((ξ j : ℂ) * w i - (ξ i : ℂ) * w j)

theorem transverseDerivativePotential_skew (b : Fin 4) (ξ : E) (w : ComplexCovector)
    (j i : Fin 4) :
    transverseDerivativePotential b ξ w j i = -transverseDerivativePotential b ξ w i j := by
  simp only [transverseDerivativePotential]
  ring

private theorem sum_squared_complex_frequency (ξ : E) :
    ∑ j : Fin 4, (ξ j : ℂ) * (ξ j : ℂ) = ((‖ξ‖^2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.norm_eq_abs, sq_abs, pow_two, Complex.ofReal_mul]

theorem transverseDerivativePotential_divergence (b : Fin 4) (ξ : E) (hξ : ξ ≠ 0)
    (w : ComplexCovector) (hw : ∑ j : Fin 4, (ξ j : ℂ) * w j = 0) (i : Fin 4) :
    ∑ j : Fin 4, (Complex.I * (ξ j : ℂ)) * transverseDerivativePotential b ξ w j i =
      Complex.I * (ξ b : ℂ) * w i := by
  let s : ℂ := ((‖ξ‖^2 : ℝ) : ℂ)
  have hS : s ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ))
  have hSq : ∑ j : Fin 4, (ξ j : ℂ) * (ξ j : ℂ) = s := sum_squared_complex_frequency ξ
  calc
    _ = ∑ j : Fin 4, (Complex.I * ((ξ b : ℂ) / s)) *
        (((ξ j : ℂ) * (ξ j : ℂ)) * w i - (ξ i : ℂ) * ((ξ j : ℂ) * w j)) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [transverseDerivativePotential, s]
      ring
    _ = (Complex.I * ((ξ b : ℂ) / s)) *
        ((∑ j : Fin 4, (ξ j : ℂ) * (ξ j : ℂ)) * w i - (ξ i : ℂ) * ∑ j : Fin 4, (ξ j : ℂ) * w j) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    _ = _ := by
      rw [hSq, hw, mul_zero, sub_zero]
      field_simp

/-- Antisymmetric potentials contract to zero against a symmetric Hessian. -/
theorem skew_symmetric_contraction_zero (A S : ComplexComponents)
    (hA : ∀ j i, A j i = -A i j) (hS : ∀ j i, S j i = S i j) :
    ∑ j, ∑ i, A j i * S j i = 0 := by
  let z : ℂ := ∑ j, ∑ i, A j i * S j i
  have h : z = -z := calc
    z = ∑ i, ∑ j, A j i * S j i := Finset.sum_comm
    _ = -z := by
      unfold z
      simp only [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hA i j, hS i j, neg_mul]
  have hzero : (2 : ℂ) * z = 0 := by
    rw [two_mul]
    calc
      z + z = -z + z := congrArg (fun v : ℂ => v + z) h
      _ = 0 := neg_add_cancel z
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

end Burnett.P01
