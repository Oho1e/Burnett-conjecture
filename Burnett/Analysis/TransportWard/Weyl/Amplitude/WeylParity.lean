import Burnett.Analysis.TransportWard.Weyl.Amplitude.A01WeylProperSupport
import Burnett.Analysis.TransportWard.Weyl.Amplitude.DyadicWeylFinite
import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactKernelOrderZero
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
set_option maxHeartbeats 3700000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.Analysis.FirstOrderDyadic
open Burnett.A02.FrequencySplit (E tau)
open Burnett.Microlocal.AngularDyadicKernel (radialCore)
open scoped ContDiff FourierTransform ComplexConjugate Topology

private theorem patch_fourier_phase_conj_neg_base (ξ z : E) :
    conj (patchFourierPhase ξ z) = patchFourierPhase (-ξ) z := by
  unfold patchFourierPhase Burnett.Microlocal.Overlap.baseFourierPhase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, inner_neg_left]
  congr 1
  push_cast
  ring

private theorem patch_fourier_phase_conj_neg_relative (ξ z : E) :
    conj (patchFourierPhase ξ z) = patchFourierPhase ξ (-z) := by
  unfold patchFourierPhase Burnett.Microlocal.Overlap.baseFourierPhase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, inner_neg_right]
  congr 1
  push_cast
  ring

/-- The exact outer cutoff used by the actual dyadic midpoint integral is even. -/
theorem dyadic_weyl_cutoff_even (N : ℕ) (ξ : E) : dyadicWeylCutoff N (-ξ) = dyadicWeylCutoff N ξ := by
  simp [dyadicWeylCutoff, radialCore, smul_neg]

private theorem a01_complete_finite_kernel_frequency_integral
    (β : E → E → ℂ) (cont : ∀ x, Continuous (normalizedWeylSymbol β x)) (N : ℕ) (x z : E) :
    a01CompleteFiniteKernel (normalizedWeylSymbol β) N (x,z) =
      ∫ ξ : E, (patchFourierPhase ξ z * (dyadicWeylCutoff N ξ : ℂ)) * β x (tau • ξ) := by
  change firstOrderLowKernel (normalizedWeylSymbol β) x z +
    ∑ j ∈ Finset.range N, firstOrderAnnularKernel (normalizedWeylSymbol β) x j z = _
  rw [← dyadic_weyl_finite_inverse_eq_actual_bands β N x z (cont x)]
  simp only [Real.fourierIntegralInv_eq', dyadic_weyl_finite_symbol_eq_cutoff, smul_eq_mul,
    Burnett.Microlocal.Overlap.baseFourierPhase, mul_assoc]

/-- A real full symbol gives Hermitian kernel symmetry in the relative variable. -/
theorem a01_weyl_band_kernel_conj_reverse_relative
    (β : E → E → ℂ) (cont : ∀ x, Continuous (normalizedWeylSymbol β x))
    (real : ∀ x ξ, conj (β x ξ) = β x ξ) (N : ℕ) (x z : E) :
    conj (a01CompleteFiniteKernel (normalizedWeylSymbol β) N (x,z)) =
      a01CompleteFiniteKernel (normalizedWeylSymbol β) N (x,-z) := by
  rw [a01_complete_finite_kernel_frequency_integral β cont N x z,
    a01_complete_finite_kernel_frequency_integral β cont N x (-z), ← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by
    simp only [map_mul, Complex.conj_ofReal, real x (tau • ξ), patch_fourier_phase_conj_neg_relative]

/-- A real odd full symbol makes the literal finite Weyl kernel pure imaginary. -/
theorem a01_weyl_band_kernel_conj_neg
    (β : E → E → ℂ) (cont : ∀ x, Continuous (normalizedWeylSymbol β x))
    (real : ∀ x ξ, conj (β x ξ) = β x ξ) (odd : ∀ x ξ, β x (-ξ) = -β x ξ)
    (N : ℕ) (x z : E) :
    conj (a01CompleteFiniteKernel (normalizedWeylSymbol β) N (x,z)) =
      -a01CompleteFiniteKernel (normalizedWeylSymbol β) N (x,z) := by
  rw [a01_complete_finite_kernel_frequency_integral β cont N x z, ← integral_conj]
  let F (ξ : E) := (patchFourierPhase ξ z * (dyadicWeylCutoff N ξ : ℂ)) * β x (tau • ξ)
  calc
    _ = ∫ ξ : E, -(F (-ξ)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by
        simp only [F, map_mul, Complex.conj_ofReal, real x (tau • ξ),
          patch_fourier_phase_conj_neg_base, dyadic_weyl_cutoff_even, smul_neg,
          odd x (tau • ξ), mul_neg, neg_neg]
    _ = -(∫ ξ : E, F (-ξ)) := integral_neg _
    _ = _ := by rw [integral_neg_eq_self F volume]

/-- The actual finite, localized Weyl two-point kernel. -/
def a01LocalizedWeylFiniteKernel (β : E → E → ℂ) (w : E → E → ℝ) (N : ℕ) (x y : E) : ℂ :=
  (w x y : ℂ) * a01CompleteFiniteKernel (normalizedWeylSymbol β) N ((1/2 : ℝ) • (x+y), x-y)

/-- For a real full symbol and a symmetric real two-point localization,
the actual finite Weyl kernel is Hermitian in the two physical arguments. -/
theorem a01_weyl_localized_finite_kernel_hermitian
    (β : E → E → ℂ) (cont : ∀ x, Continuous (normalizedWeylSymbol β x))
    (real : ∀ x ξ, conj (β x ξ) = β x ξ)
    (w : E → E → ℝ) (sym : ∀ x y, w x y = w y x) (N : ℕ) (x y : E) :
    conj (a01LocalizedWeylFiniteKernel β w N x y) = a01LocalizedWeylFiniteKernel β w N y x := by
  simp only [a01LocalizedWeylFiniteKernel, map_mul, Complex.conj_ofReal,
    a01_weyl_band_kernel_conj_reverse_relative β cont real N ((1/2 : ℝ) • (x+y)) (x-y)]
  rw [neg_sub, add_comm x y, sym x y]

/-- The real odd finite action anticommutes with conjugation on test functions. -/
theorem a01_weyl_localized_finite_action_anticommutes
    (β : E → E → ℂ) (cont : ∀ x, Continuous (normalizedWeylSymbol β x))
    (real : ∀ x ξ, conj (β x ξ) = β x ξ) (odd : ∀ x ξ, β x (-ξ) = -β x ξ)
    (w : E → E → ℝ) (N : ℕ) (u v : SchwartzMap E ℂ)
    (rel : ∀ y, v y = conj (u y)) (x : E) :
    conj (compactKernelAction (a01LocalizedWeylFiniteKernel β w N) u x) =
      -compactKernelAction (a01LocalizedWeylFiniteKernel β w N) v x := by
  rw [compactKernelAction, compactKernelAction, ← integral_conj, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [a01LocalizedWeylFiniteKernel, rel y, map_mul, Complex.conj_ofReal,
      a01_weyl_band_kernel_conj_neg β cont real odd N ((1/2 : ℝ) • (x+y)) (x-y),
      mul_neg, neg_mul]

end Burnett.A03
