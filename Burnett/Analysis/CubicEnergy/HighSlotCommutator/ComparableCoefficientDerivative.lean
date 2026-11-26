import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowTest
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinGradient

set_option autoImplicit false
set_option maxHeartbeats 3300000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open scoped ContDiff FourierTransform Topology BigOperators NNReal

private def coefficientDerivativeSymbol (profile : SchwartzMap E ℂ) (j : Fin 4) (z : E) : ℂ :=
  profile z * ((z j / (tau*‖z‖^2) : ℝ) : ℂ)

private theorem coefficientDerivativeSymbol_contDiff (profile : SchwartzMap E ℂ) {a : ℝ}
    (ha : 0<a) (hprofile : ∀ z, ‖z‖<a → profile z=0) (j : Fin 4) :
    ContDiff ℝ ∞ (coefficientDerivativeSymbol profile j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : E) ha] with z hz
    rw [Metric.mem_ball,dist_zero_right] at hz
    simp only [coefficientDerivativeSymbol,hprofile z hz,zero_mul]
  · have hcoord : ContDiff ℝ ∞ (fun z : E => z j) :=
      (EuclideanSpace.proj j : E →L[ℝ] ℝ).contDiff
    have hden : ContDiff ℝ ∞ (fun z : E => tau*‖z‖^2) :=
      contDiff_const.mul (contDiff_norm_sq ℝ)
    have hτ : 0<tau := mul_pos (by norm_num) Real.pi_pos
    have hn : tau*‖x‖^2 ≠ 0 := mul_ne_zero hτ.ne' (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))
    have hdiv := hcoord.contDiffAt.div hden.contDiffAt hn
    exact profile.smooth'.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x hdiv)

private theorem coefficientDerivativeSymbol_compact (profile : SchwartzMap E ℂ)
    (hc : HasCompactSupport (profile : E → ℂ)) (j : Fin 4) :
    HasCompactSupport (coefficientDerivativeSymbol profile j) :=
  hc.of_isClosed_subset isClosed_closure tsupport_mul_subset_left

private theorem coefficientDerivativeSymbol_resolution (profile : SchwartzMap E ℂ) (h0 : profile 0=0)
    (z : E) :
    (∑ j : Fin 4, ((tau*z j : ℝ) : ℂ)*coefficientDerivativeSymbol profile j z) = profile z := by
  by_cases hz : z=0
  · subst z
    simp [h0,coefficientDerivativeSymbol]
  · have hτ : 0<tau := mul_pos (by norm_num) Real.pi_pos
    have hτC : (tau : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    have term (j : Fin 4) : ((tau*z j : ℝ) : ℂ)*coefficientDerivativeSymbol profile j z =
        profile z * (((z j)^2 : ℝ) : ℂ) / ((‖z‖^2 : ℝ) : ℂ) := by
      simp only [coefficientDerivativeSymbol,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow]
      field_simp [hτC,hn]
    have hsq : (∑ j : Fin 4, (z j)^2) = ‖z‖^2 := by
      simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
    simp_rw [term]
    rw [← Finset.sum_div,← Finset.mul_sum,← Complex.ofReal_sum,hsq,Complex.ofReal_pow]
    field_simp [hn]

theorem coefficientSchwartz_sum_value (F : Fin 4 → SchwartzMap E ℂ) (s : Finset (Fin 4)) (z : E) :
    (∑ j ∈ s, F j) z = ∑ j ∈ s, F j z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj,Finset.sum_insert hj,SchwartzMap.add_apply,ih]

/-- For a coefficient annulus which vanishes near zero, the normalized
actual filter is a sum of four annular filters of the actual derivatives. -/
theorem exists_coefficientBandpass_derivative_windows (profile : SchwartzMap E ℂ)
    (hc : HasCompactSupport (profile : E → ℂ)) {a b : ℝ} (ha : 0<a)
    (hprofile : ∀ z, profile z ≠ 0 → a ≤ ‖z‖ ∧ ‖z‖ ≤ b) :
    ∃ W : Fin 4 → SchwartzMap E ℂ,
      (∀ j z, W j z ≠ 0 → profile z ≠ 0) ∧
      ∀ (D : SchwartzMap E ℂ) {s : ℝ}, 0<s →
        (((s⁻¹ : ℝ) : ℂ) • windowTest profile D s) =
          ∑ j : Fin 4, windowTest (W j) (mikhlinDerivative j D) s := by
  have zero (z : E) (hz : ‖z‖<a) : profile z=0 := by
    by_contra h; exact (not_le_of_gt hz) (hprofile _ h).1
  let W (j : Fin 4) :=
    (coefficientDerivativeSymbol_compact profile hc j).toSchwartzMap
      (coefficientDerivativeSymbol_contDiff profile ha zero j)
  refine ⟨W,?_,?_⟩
  · intro j z h hp
    apply h
    change coefficientDerivativeSymbol profile j z=0
    simp only [coefficientDerivativeSymbol,hp,zero_mul]
  · intro D s hs
    apply (SchwartzMap.fourierTransformCLE ℂ).injective
    ext z
    change (SchwartzMap.fourierTransformCLM ℂ _ : SchwartzMap E ℂ) z =
      (SchwartzMap.fourierTransformCLM ℂ _ : SchwartzMap E ℂ) z
    rw [map_smul,map_sum,coefficientSchwartz_sum_value]
    simp only [SchwartzMap.smul_apply,smul_eq_mul,SchwartzMap.fourierTransformCLM_apply,
      windowTest_fourier,mikhlinDerivative_fourier]
    have calcTerms (j : Fin 4) :
        ((tau*z j : ℝ) : ℂ) * 𝓕 (D : E → ℂ) z * W j (s • z) =
        ((s⁻¹ : ℝ) : ℂ)*𝓕 (D : E → ℂ) z *
          (((tau*(s • z) j : ℝ) : ℂ)*coefficientDerivativeSymbol profile j (s • z)) := by
      change _ * coefficientDerivativeSymbol profile j (s • z) = _
      simp only [PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_inv]
      have sn : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      field_simp [sn]
    rw [show (((s⁻¹ : ℝ) : ℂ) * (𝓕 (D : E → ℂ) z * profile (s • z))) =
      (((s⁻¹ : ℝ) : ℂ) * 𝓕 (D : E → ℂ) z)*profile (s • z) by ring]
    simp_rw [calcTerms,← Finset.mul_sum,coefficientDerivativeSymbol_resolution profile (zero 0 (by simpa))]

theorem mikhlinDerivative_norm_le_lipschitz (D : SchwartzMap E ℂ) {L : ℝ≥0}
    (hD : LipschitzWith L D) (j : Fin 4) (x : E) :
    ‖mikhlinDerivative j D x‖ ≤ (L : ℝ) := by
  change ‖(-Complex.I) * fderiv ℝ (D : E → ℂ) x (EuclideanSpace.single j 1)‖ ≤ _
  rw [norm_mul,norm_neg,Complex.norm_I,one_mul]
  exact ((fderiv ℝ (D : E → ℂ) x).le_opNorm _).trans (by
    simpa only [EuclideanSpace.norm_single,norm_one,mul_one] using
      norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hD)

end Burnett.A06
