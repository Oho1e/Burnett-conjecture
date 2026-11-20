import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinGradientBound

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.DyadicSquare (rescaleSymbol)
open Burnett.Analysis.ShiftedFourierWindow (shifted_window_physical)
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open scoped ContDiff ENNReal FourierTransform

/-- The actual spectrum of a radian multiplier on a Schwartz input, written
in the project Fourier coordinates. -/
def radianActionSpectrum (a : E → ℝ) (f : SchwartzMap E ℂ) (ξ : E) : ℂ :=
  (a (tau • ξ) : ℂ) * 𝓕 (f : E → ℂ) ξ

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

theorem radianActionSpectrum_inverse (a : E → ℝ) (f : SchwartzMap E ℂ) :
    𝓕⁻ (radianActionSpectrum a f) = radianAction a f :=
  funext fun x => (radianAction_eq_orderOne a f x).symm

theorem radianActionSpectrum_smooth (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ | ξ ≠ 0})
    (f : SchwartzMap E ℂ) : ContDiffOn ℝ ∞ (radianActionSpectrum a f) {ξ | ξ ≠ 0} := by
  have hc : ContDiffOn ℝ ∞ (fun ξ : E => a (tau • ξ)) {ξ | ξ ≠ 0} :=
    ha.comp (contDiff_const.smul contDiff_id).contDiffOn (fun ξ hξ => smul_ne_zero tau_pos.ne' hξ)
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hc).mul
    ((SchwartzMap.fourierTransformCLM ℂ f).smooth _).contDiffOn

theorem radianActionSpectrum_degreeZero_apply (a : E → ℝ)
    (ha : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = a ξ) (f : SchwartzMap E ℂ) (ξ : E) :
    radianActionSpectrum a f ξ = (a ξ : ℂ) * 𝓕 (f : E → ℂ) ξ := by
  rw [radianActionSpectrum, ha tau tau_pos ξ]

theorem radianActionSpectrum_radial_apply (f : SchwartzMap E ℂ) (ξ : E) :
    radianActionSpectrum (fun z => ‖z‖) f ξ = ((tau * ‖ξ‖ : ℝ) : ℂ) * 𝓕 (f : E → ℂ) ξ := by
  simp only [radianActionSpectrum, norm_smul, Real.norm_of_nonneg tau_pos.le]

/-- Smoothness off zero, frequency L¹, and the actual physical Lᵖ input
needed to approximate a degree-zero multiplier by Schwartz functions. -/
theorem radianActionSpectrum_degreeZero_data (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ | ξ ≠ 0})
    (hh : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = a ξ) (f : SchwartzMap E ℂ) :
    ContDiffOn ℝ ∞ (radianActionSpectrum a f) {ξ | ξ ≠ 0} ∧
      Integrable (radianActionSpectrum a f) ∧
      ∀ p : ℝ, 1 < p → MemLp (𝓕⁻ (radianActionSpectrum a f)) (ENNReal.ofReal p) volume := by
  obtain ⟨M, hM⟩ := mikhlin_bounded_symbol a ha hh
  refine ⟨radianActionSpectrum_smooth a ha f, ?_, ?_⟩
  · have hi := (SchwartzMap.fourierTransformCLM ℂ f).integrable.bdd_mul M.measurable ⟨M.bound, M.norm_le⟩
    refine hi.congr <| Filter.Eventually.of_forall fun ξ => ?_
    change M ξ * 𝓕 (f : E → ℂ) ξ = _
    rw [hM, radianActionSpectrum_degreeZero_apply a hh]
  · intro p hp
    obtain ⟨_, S, _, _, _, _, tests⟩ := homogeneous_multiplier_all_Lp a ha hh p hp
    rw [radianActionSpectrum_inverse]
    exact (Lp.memLp (S (f.toLp (ENNReal.ofReal p) volume))).ae_eq (tests f)

private theorem norm_smooth : ContDiffOn ℝ ∞ (fun ξ : E => ‖ξ‖) {ξ | ξ ≠ 0} :=
  fun _ hx => (contDiffAt_id.norm ℝ hx).contDiffWithinAt

/-- The radius multiplier uses the manuscript's exact factor τ = 2π and
the already-proved finite sum of real Riesz transforms of Dⱼf. -/
theorem radianActionSpectrum_radial_data (f : SchwartzMap E ℂ) :
    ContDiffOn ℝ ∞ (radianActionSpectrum (fun z => ‖z‖) f) {ξ | ξ ≠ 0} ∧
      Integrable (radianActionSpectrum (fun z => ‖z‖) f) ∧
      ∀ p : ℝ, 1 < p → MemLp (𝓕⁻ (radianActionSpectrum (fun z => ‖z‖) f)) (ENNReal.ofReal p) volume := by
  refine ⟨radianActionSpectrum_smooth _ norm_smooth f, ?_, ?_⟩
  · let F := SchwartzMap.fourierTransformCLM ℂ f
    have hI : Integrable (fun ξ : E => ‖ξ‖ * ‖F ξ‖) := by
      simpa only [pow_one] using F.integrable_pow_mul volume 1
    have hSpectrum : radianActionSpectrum (fun z => ‖z‖) f =
        fun ξ : E => ((tau * ‖ξ‖ : ℝ) : ℂ) * F ξ :=
      funext (radianActionSpectrum_radial_apply f)
    refine (hI.const_mul tau).mono' ?_ ?_
    · rw [hSpectrum]
      exact ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_norm)).mul
        F.continuous).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ξ => by
        rw [radianActionSpectrum_radial_apply, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg tau_pos.le (norm_nonneg ξ)), mul_assoc]; exact le_rfl
  · intro p hp
    rw [radianActionSpectrum_inverse, mikhlin_radial_derivative_identity]
    apply memLp_finset_sum'
    intro j _
    obtain ⟨hR, hR0⟩ := mikhlinRiesz_regular j
    have R := (radianActionSpectrum_degreeZero_data _ hR hR0 (mikhlinDerivative j f)).2.2 p hp
    rwa [radianActionSpectrum_inverse] at R

/-- The specific angular component used in the paper's multiplier slots. -/
theorem radianActionSpectrum_angular_data (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hh : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (j : Index) (f : SchwartzMap E ℂ) :
    ContDiffOn ℝ ∞ (radianActionSpectrum (angularComponent b j) f) {ξ | ξ ≠ 0} ∧
      Integrable (radianActionSpectrum (angularComponent b j) f) ∧
      ∀ p : ℝ, 1 < p → MemLp (𝓕⁻ (radianActionSpectrum (angularComponent b j) f))
        (ENNReal.ofReal p) volume :=
  radianActionSpectrum_degreeZero_data _ (angularComponent_contDiffOn b hb j) (angularComponent_scale hh j) f

end Burnett.A02.FrequencySplit
