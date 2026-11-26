import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowTest
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 3900000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open MeasureTheory Filter
open scoped FourierTransform Topology RealInnerProductSpace

/-- The low-pass window of an actual Schwartz coefficient tends uniformly
to that coefficient as its physical scale tends to zero. The nonnegative
error is independent of the observation point. -/
theorem exists_windowTest_uniform_small_scale_error
    (χ D : SchwartzMap E ℂ) (hχ : χ 0=1) (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ, (∀ n, 0≤ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n x, ‖windowTest χ D (s n) x-D x‖ ≤ ε n := by
  let F := SchwartzMap.fourierTransformCLM ℂ D
  let U (n : ℕ) (z : E) := ‖F z‖*‖χ (s n • z)-1‖
  let A := SchwartzMap.seminorm ℝ 0 0 χ+1
  let ε (n : ℕ) := ∫ z : E, U n z
  have cont (n : ℕ) : Continuous (U n) := by
    let hF := F.continuous
    let hχC := χ.continuous
    unfold U
    fun_prop
  have upper (n : ℕ) (z : E) : ‖U n z‖≤‖F z‖*A := by
    rw [Real.norm_of_nonneg (show 0≤U n z by unfold U; positivity)]
    unfold U A
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have h := norm_sub_le (χ (s n • z)) (1:ℂ)
    rw [norm_one] at h
    exact h.trans (add_le_add_right (SchwartzMap.norm_le_seminorm ℝ χ (s n • z)) 1)
  have hzero (z : E) : Tendsto (fun n => U n z) atTop (𝓝 0) := by
    have sz : Tendsto (fun n => s n • z) atTop (𝓝 (0:E)) := by
      simpa only [zero_smul] using hs.smul (tendsto_const_nhds (x := z))
    have hc : Tendsto (fun n => χ (s n • z)) atTop (𝓝 (1:ℂ)) := by
      simpa only [hχ] using (χ.continuous.continuousAt.tendsto.comp sz)
    have h := (hc.sub (tendsto_const_nhds (x := (1:ℂ)))).norm
    simpa only [U,sub_self,norm_zero,mul_zero] using h.const_mul ‖F z‖
  have εlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,integral_zero] using
      (tendsto_integral_of_dominated_convergence (F := U) (f := fun _ : E => (0:ℝ))
        (fun z => ‖F z‖*A) (fun n => (cont n).aestronglyMeasurable)
        (F.integrable.norm.mul_const A) (fun n => .of_forall (upper n)) (.of_forall hzero))
  refine ⟨ε,fun n => integral_nonneg fun z => by unfold U; positivity,εlim,?_⟩
  intro n x
  let V := windowTest χ D (s n)-D
  let G := SchwartzMap.fourierTransformCLM ℂ V
  have hG (z : E) : G z = F z * (χ (s n • z)-1) := by
    unfold G V
    rw [map_sub]
    simp only [SchwartzMap.sub_apply,SchwartzMap.fourierTransformCLM_apply,windowTest_fourier,
      mul_sub,mul_one,F]
  have inv : 𝓕⁻ (G : E → ℂ) x = V x :=
    congrFun (V.continuous.fourier_inversion V.integrable G.integrable) x
  change ‖V x‖ ≤ ε n
  rw [← inv,Real.fourierIntegralInv_eq']
  refine (norm_integral_le_integral_norm _).trans ?_
  have eq (z : E) :
      ‖Complex.exp ((↑(2*Real.pi*inner ℝ z x) : ℂ)*Complex.I) • G z‖ = U n z := by
    rw [norm_smul,Complex.norm_exp_ofReal_mul_I,one_mul,hG,norm_mul]
  exact le_of_eq (integral_congr_ae (.of_forall eq))

end Burnett.A06
