import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinGradient

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.DyadicSquare (rescaleSymbol)
open Burnett.Analysis.ShiftedFourierWindow (shifted_window_physical)
open Burnett.Analysis.SignedFourierWindow
open Finset MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open scoped ENNReal ContDiff

/-- The full norm of the actual Fréchet derivative controls the paper's |D|f
on Schwartz tests for each finite exponent above one. -/
theorem mikhlin_radial_gradient_bound (p : ℝ) (hp : 1<p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : SchwartzMap E ℂ,
      eLpNorm (radianAction (fun ξ => ‖ξ‖) f) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (fderiv ℝ (f : E → ℂ)) (ENNReal.ofReal p) volume := by
  let P := ENNReal.ofReal p
  choose C fin bound using fun j => homogeneous_multiplier_Schwartz_bound _ (mikhlinRiesz_regular j).1
    (mikhlinRiesz_regular j).2 p hp
  refine ⟨∑ j, C j,ENNReal.sum_lt_top.mpr (fun j _ => fin j),?_⟩
  intro f
  let g := fun j => mikhlinDerivative j f
  have meas (j : Index) : AEStronglyMeasurable (radianAction (mikhlinRiesz j) (g j)) volume := by
    obtain ⟨M,hm⟩ := mikhlin_bounded_symbol _ (mikhlinRiesz_regular j).1 (mikhlinRiesz_regular j).2
    exact (Lp.aestronglyMeasurable _).congr (mikhlin_action_test _ M hm (mikhlinRiesz_regular j).2 (g j))
  have grad (j : Index) : eLpNorm (g j : E → ℂ) P volume ≤ eLpNorm (fderiv ℝ (f : E → ℂ)) P volume := by
    apply eLpNorm_mono
    intro x
    change ‖(-Complex.I) • (fderiv ℝ (f : E → ℂ) x (EuclideanSpace.single j 1))‖ ≤ _
    simpa using (fderiv ℝ (f : E → ℂ) x).le_opNorm (EuclideanSpace.single j 1)
  rw [mikhlin_radial_derivative_identity,Finset.sum_mul]
  have h1 : 1≤P := by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  apply (eLpNorm_sum_le (fun j _ => meas j) h1).trans
  exact sum_le_sum (fun j _ => (bound j (g j)).trans (mul_le_mul_left' (grad j) _))

end Burnett.A02.FrequencySplit
