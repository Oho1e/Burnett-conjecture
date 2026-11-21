import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinApplications
import Burnett.Analysis.H1FourierEnergy

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.DyadicSquare (rescaleSymbol)
open Burnett.Analysis.ShiftedFourierWindow (shifted_window_physical)
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset Burnett.RicciSymbol
open scoped ENNReal ContDiff FourierTransform RealInnerProductSpace

def mikhlinDerivative (j : Index) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  (-Complex.I) • SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1) f

theorem mikhlinDerivative_fourier (j : Index) (f : SchwartzMap E ℂ) (ξ : E) :
    𝓕 (mikhlinDerivative j f : E → ℂ) ξ = (tau * ξ j : ℝ) * 𝓕 (f : E → ℂ) ξ := by
  let g := SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1) f
  have h : 𝓕 (mikhlinDerivative j f : E → ℂ) ξ = -Complex.I * 𝓕 (g : E → ℂ) ξ :=
    congrArg (fun u : SchwartzMap E ℂ => u ξ) ((SchwartzMap.fourierTransformCLM ℂ).map_smul (-Complex.I) g)
  rw [h,show 𝓕 (g : E → ℂ) ξ = _ from Burnett.Analysis.HminusWeightedDual.fourier_pderiv f _ ξ]
  simp only [EuclideanSpace.inner_single_right,Complex.ofReal_mul,tau]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem riesz_sum (ξ : E) : ∑ j, mikhlinRiesz j ξ * ξ j = ‖ξ‖ := by
  have sq : ∑ j, (ξ j)^2 = ‖ξ‖^2 := by simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs,sq_abs]
  have id (j : Index) : mikhlinRiesz j ξ * ξ j = (ξ j)^2 / ‖ξ‖ := by unfold mikhlinRiesz; ring
  simp_rw [id]
  rw [← Finset.sum_div,sq]
  by_cases z : ξ=0
  · simp [z]
  · field_simp [norm_ne_zero_iff.mpr z]

/-- The paper's |D|f is exactly the finite sum of Rⱼ Dⱼ f, with both actual
radian Fourier conventions and the multiplier values at zero included. -/
theorem mikhlin_radial_derivative_identity (f : SchwartzMap E ℂ) :
    radianAction (fun ξ => ‖ξ‖) f = ∑ j, radianAction (mikhlinRiesz j) (mikhlinDerivative j f) := by
  funext x
  let w := fun ξ : E => Complex.exp ((↑(2*Real.pi*inner ℝ ξ x):ℂ)*Complex.I)
  let G := fun (j : Index) (ξ : E) => (mikhlinRiesz j ξ : ℂ)*𝓕 (mikhlinDerivative j f : E → ℂ) ξ
  have wt (ξ : E) : ‖w ξ‖ = 1 := by simp [w,Complex.norm_exp]
  have wm : Continuous w := by dsimp only [w]; fun_prop
  have intg (j : Index) : Integrable (fun ξ => w ξ * G j ξ) := by
    obtain ⟨M,hM⟩ := mikhlin_bounded_symbol _ (mikhlinRiesz_regular j).1 (mikhlinRiesz_regular j).2
    let g := SchwartzMap.fourierTransformCLM ℂ (mikhlinDerivative j f)
    have i : Integrable (fun ξ => M ξ * g ξ) := g.integrable.bdd_mul M.measurable ⟨M.bound,M.norm_le⟩
    have e : G j = fun ξ => M ξ * g ξ := funext fun ξ => by rw [hM]; rfl
    rw [e]
    exact i.bdd_mul wm.aestronglyMeasurable ⟨1,fun ξ => (wt ξ).le⟩
  have rp (j : Index) : radianAction (mikhlinRiesz j) (mikhlinDerivative j f) x =
      ∫ ξ, w ξ * G j ξ := by
    rw [radianAction_eq_orderOne,show (fun ξ => mikhlinRiesz j (tau • ξ)) = mikhlinRiesz j from
      funext ((mikhlinRiesz_regular j).2 _ (mul_pos (by norm_num) Real.pi_pos)),orderOneAction,Real.fourierIntegralInv_eq']
    rfl
  rw [Finset.sum_apply]
  simp_rw [rp]
  rw [← integral_finset_sum _ (fun j _ => intg j),radianAction_eq_orderOne,orderOneAction,Real.fourierIntegralInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  change w ξ * ((‖tau • ξ‖ : ℂ) * 𝓕 (f : E → ℂ) ξ) = _
  rw [norm_smul,Real.norm_of_nonneg (mul_pos (by norm_num) Real.pi_pos).le,← Finset.mul_sum]
  congr 1
  have step (j : Index) : G j ξ = (↑(mikhlinRiesz j ξ * ξ j) : ℂ)*((tau : ℂ)*𝓕 (f : E → ℂ) ξ) := by
    simp only [G,mikhlinDerivative_fourier,Complex.ofReal_mul]
    ring
  simp only [step,← Finset.sum_mul]
  rw [← Complex.ofReal_sum,riesz_sum,Complex.ofReal_mul]
  ring

end Burnett.A02.FrequencySplit
