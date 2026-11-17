import Burnett.Analysis.Sobolev.Pairing
import Burnett.Analysis.Fourier.Projection

/-!
# H1FourierEnergy

Paper-specific Hminus support; scope and remaining geometric obligations are recorded separately.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section

namespace Burnett.Analysis.HminusWeightedDual
open MeasureTheory Filter
open scoped Topology ContDiff FourierTransform RealInnerProductSpace
open Burnett.X02.SobolevTestJet Burnett.X02.TestJetPairing
open Burnett.Fourier

def frequencyWeight (ξ : Space) : ℝ := 1 + 4 * Real.pi^2 * ‖ξ‖^2

def complexTest (φ : D) : SchwartzMap Space ℂ :=
  ((test_compactSupport φ).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (test_smooth φ))

theorem fourier_pderiv (f : SchwartzMap Space ℂ) (v ξ : Space) :
    𝓕 (SchwartzMap.pderivCLM ℂ v f : Space → ℂ) ξ =
      (2 * Real.pi * Complex.I) * (inner ℝ ξ v : ℂ) * 𝓕 (f : Space → ℂ) ξ := by
  change 𝓕 (fun x => fderiv ℝ (f : Space → ℂ) x v) ξ = _
  have hd := congrFun (Real.fourierIntegral_fderiv f.integrable f.differentiable
    (SchwartzMap.fderivCLM ℂ f).integrable) ξ
  have hv := congrArg (fun L : Space →L[ℝ] ℂ => L v) hd
  have hi : Integrable (fderiv ℝ (f : Space → ℂ)) :=
    (SchwartzMap.fderivCLM ℂ f).integrable
  change (𝓕 (fderiv ℝ (f : Space → ℂ)) ξ) v = _ at hv
  rw [Real.fourierIntegral_continuousLinearMap_apply (f := fderiv ℝ (f : Space → ℂ)) hi] at hv
  simpa only [VectorFourier.fourierSMulRight_apply, ContinuousLinearMap.neg_apply,
    innerSL_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_neg,
    neg_mul, mul_neg, neg_neg, mul_assoc] using hv

theorem complexTest_pderiv (φ : D) (i : Fin 4) (x : Space) :
    SchwartzMap.pderivCLM ℂ (EuclideanSpace.single i 1) (complexTest φ) x =
      (directional i (φ : Space → ℝ) x : ℂ) := by
  change fderiv ℝ (fun y => ((φ : Space → ℝ) y : ℂ)) x (EuclideanSpace.single i 1) = _
  have hd := (Complex.ofRealCLM.hasFDerivAt).comp x (test_differentiable φ x).hasFDerivAt
  change HasFDerivAt (fun y => ((φ : Space → ℝ) y : ℂ))
    (Complex.ofRealCLM.comp (fderiv ℝ (φ : Space → ℝ) x)) x at hd
  rw [hd.fderiv]
  rfl

theorem fourier_coordinate_pderiv_norm_sq (φ : D) (i : Fin 4) (ξ : Space) :
    ‖𝓕 (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single i 1) (complexTest φ) : Space → ℂ) ξ‖^2 =
      (4 * Real.pi^2 * (ξ i)^2) * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖^2 := by
  rw [fourier_pderiv]
  simp only [norm_mul, mul_pow, EuclideanSpace.inner_single_right, mul_one,
    Complex.norm_I, one_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num

theorem real_toLp_norm_sq {f : Space → ℝ} (hf : MemLp f 2 (volume : Measure Space)) :
    ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem value_fourier_energy (φ : D) :
    ‖valueLp φ‖^2 = ∫ ξ, ‖𝓕 (complexTest φ : Space → ℂ) ξ‖^2 := by
  rw [schwartz_parseval]
  have h := real_toLp_norm_sq (test_memLp φ)
  change ‖valueLp φ‖^2 = ∫ x, ‖((φ : Space → ℝ) x : ℂ)‖^2
  simpa only [valueLp, Complex.norm_real] using h

theorem directional_fourier_energy (φ : D) (i : Fin 4) :
    ‖directionalLp i φ‖^2 =
      ∫ ξ, (4 * Real.pi^2 * (ξ i)^2) * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖^2 := by
  calc
    ‖directionalLp i φ‖^2 = ∫ x, ‖directional i (φ : Space → ℝ) x‖^2 :=
      real_toLp_norm_sq (directional_memLp i φ)
    _ = ∫ x, ‖SchwartzMap.pderivCLM ℂ (EuclideanSpace.single i 1) (complexTest φ) x‖^2 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [complexTest_pderiv]
      simp
    _ = ∫ ξ, ‖𝓕 (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single i 1)
        (complexTest φ) : Space → ℂ) ξ‖^2 := (schwartz_parseval _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with ξ
      exact fourier_coordinate_pderiv_norm_sq φ i ξ

theorem frequencyWeight_pos (ξ : Space) : 0 < frequencyWeight ξ := by
  unfold frequencyWeight
  positivity

theorem frequencyWeight_continuous : Continuous frequencyWeight := by
  unfold frequencyWeight
  fun_prop

theorem test_jet_fourier_energy (φ : D) :
    ‖J φ‖^2 = ∫ ξ, frequencyWeight ξ * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖^2 := by
  have hi (i : Fin 4) : Integrable (fun ξ =>
      (4 * Real.pi^2 * (ξ i)^2) * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖^2) := by
    apply (fourier_norm_sq_integrable
      (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single i 1) (complexTest φ))).congr
    exact Eventually.of_forall (fourier_coordinate_pderiv_norm_sq φ i)
  have hjet : ‖J φ‖^2 = ‖valueLp φ‖^2 + ∑ i : Fin 4, ‖directionalLp i φ‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
    rfl
  rw [hjet, value_fourier_energy]
  simp_rw [directional_fourier_energy]
  rw [← integral_finset_sum _ (fun i _ => hi i), ← integral_add
    (fourier_norm_sq_integrable (complexTest φ)) (integrable_finset_sum _ (fun i _ => hi i))]
  apply integral_congr_ae
  filter_upwards with ξ
  have hξ : ‖ξ‖^2 = ∑ i : Fin 4, (ξ i)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [frequencyWeight, hξ]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

end Burnett.Analysis.HminusWeightedDual
