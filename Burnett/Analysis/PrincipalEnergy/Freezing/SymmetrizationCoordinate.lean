import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianCommutator
import Burnett.Analysis.PrincipalEnergy.Freezing.LeftFourierSeriesAction
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSkewDifferentiation

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal

/-- The actual symmetric Fourier mode minus that mode's left action. -/
def separatedSkewLeftRemainder (f : SchwartzMap E ℂ) (b : E → ℝ) (u : SchwartzMap E ℂ) : E → ℂ :=
  fun x => separatedSkewAction f b u x - f x * radianSkewAction b u x

theorem separated_skew_left_remainder_eq_commutator
    (f : SchwartzMap E ℂ) (b : E → ℝ) (u : SchwartzMap E ℂ) :
    separatedSkewLeftRemainder f b u = ((-Complex.I) / 2) • radianCommutator b f u := by
  funext x
  rw [separatedSkewLeftRemainder, separated_skew_left_difference]
  change (radianSkewAction b (energyProduct f u) x - f x * radianSkewAction b u x) / 2 =
    ((-Complex.I) / 2) * (radianAction b (energyProduct f u) x - f x * radianAction b u x)
  unfold radianSkewAction
  ring

/-- The coordinate derivative of the difference has one term for each
differentiated input. Both terms retain the commutator's cancellation. -/
theorem separated_skew_left_remainder_coordinate (f : SchwartzMap E ℂ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (u : SchwartzMap E ℂ) (j : Index) (x : E) :
    DifferentiableAt ℝ (separatedSkewLeftRemainder f b u) x ∧
      fderiv ℝ (separatedSkewLeftRemainder f b u) x (EuclideanSpace.single j 1) =
        separatedSkewLeftRemainder f b (energyPartial j u) x +
          separatedSkewLeftRemainder (energyPartial j f) b u x := by
  obtain ⟨hQ, dQ⟩ := radian_skew_coordinate_derivative b hb hom u x
  obtain ⟨hS, dS⟩ := separated_skew_coordinate_commutator f b hb hom u x j
  let L : E → ℂ := (f : E → ℂ) * radianSkewAction b u
  have hL : DifferentiableAt ℝ L x := (f.differentiable x).mul hQ
  change DifferentiableAt ℝ (separatedSkewAction f b u - L) x ∧ _
  refine ⟨hS.sub hL, ?_⟩
  change fderiv ℝ (separatedSkewAction f b u - L) x (EuclideanSpace.single j 1) = _
  have leftDeriv : fderiv ℝ L x (EuclideanSpace.single j 1) =
      f x * radianSkewAction b (energyPartial j u) x + energyPartial j f x * radianSkewAction b u x := by
    dsimp only [L]
    rw [fderiv_mul (f.differentiable x) hQ]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      dQ, energyPartial, SchwartzMap.pderivCLM_apply]
    rw [mul_comm (radianSkewAction b u x)]
  rw [fderiv_sub hS hL, ContinuousLinearMap.sub_apply, sub_eq_iff_eq_add.mp dS, leftDeriv]
  unfold separatedSkewLeftRemainder
  ring

end Burnett.A03
