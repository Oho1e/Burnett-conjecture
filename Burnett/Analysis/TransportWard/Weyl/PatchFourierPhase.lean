import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency
import Burnett.Analysis.Microlocal.Overlap.BaseFourierAction

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Burnett.A02.FrequencySplit (E tau)
open scoped RealInnerProductSpace

/-- The phase with the same normalization as the radian multiplier. -/
abbrev patchFourierPhase := Burnett.Microlocal.Overlap.baseFourierPhase

theorem patch_fourier_phase_norm (q x : E) : ‖patchFourierPhase q x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem patch_fourier_phase_continuous :
    Continuous (fun y : E × E => patchFourierPhase y.1 y.2) :=
  Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_inner)).mul continuous_const)

theorem patch_fourier_phase_add (p q x : E) :
    patchFourierPhase (p + q) x = patchFourierPhase p x * patchFourierPhase q x := by
  simp only [Burnett.Microlocal.Overlap.baseFourierPhase, inner_add_left, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem patch_fourier_phase_neg_mul (q x : E) :
    patchFourierPhase (-q) x * patchFourierPhase q x = 1 := by
  rw [← patch_fourier_phase_add, neg_add_cancel]
  simp [Burnett.Microlocal.Overlap.baseFourierPhase]

end Burnett.A03
