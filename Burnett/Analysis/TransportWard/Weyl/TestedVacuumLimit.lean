import Burnett.Analysis.PrincipalEnergy.Energy.SymmetricEnergy
import Mathlib.Analysis.InnerProductSpace.Continuous

/-! The fixed background pairing and the exact coefficient of the quadratic Euler limit. -/

set_option autoImplicit false

noncomputable section

namespace Burnett.V03

open Filter Burnett.Analysis.SymmetricEnergy
open scoped InnerProductSpace Topology

/-- With the same formally symmetric test operator, move the test off the
strongly zero perturbation onto the fixed smooth background source. -/
theorem tendsto_fixed_background_test_pairing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (B : Op H) (hB : B.IsSymmetric) (source : H)
    (u : ℕ → H) (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => ⟪B (u n), source⟫_ℂ) atTop (𝓝 0) := by
  have h : Tendsto (fun n => ⟪u n, B source⟫_ℂ) atTop (𝓝 0) := by
    simpa only [inner_zero_left] using hu.inner (tendsto_const_nhds (x := B source))
  exact h.congr' (Eventually.of_forall fun n => (hB (u n) source).symm)

/-- At the exact tested vacuum identity, the half in the Taylor expansion
cancels the factor two in the linear energy pairing. The transport
input refers to the actual first variation and its own proved limit. -/
theorem tendsto_variational_quadratic_pairing_of_tested_vacuum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : Op H) (hB : B.IsSymmetric) (source : H)
    (u : ℕ → H) (hu : Tendsto u atTop (𝓝 0))
    (L Q R : ℕ → H) (m : ℝ)
    (hVac : ∀ n, ⟪B (u n), source + L n + ((1/2 : ℝ) : ℂ) • Q n + R n⟫_ℂ = 0)
    (hHessian : Tendsto (fun n => 2 * (⟪B (u n), L n⟫_ℂ).im) atTop (𝓝 (4*m)))
    (hRem : Tendsto (fun n => 2 * (⟪B (u n), R n⟫_ℂ).im) atTop (𝓝 0)) :
    Tendsto (fun n => (⟪B (u n), Q n⟫_ℂ).im) atTop (𝓝 (-(4*m))) := by
  have hBase := tendsto_fixed_background_test_pairing B hB source u hu
  have hBaseIm : Tendsto (fun n => 2*(⟪B (u n), source⟫_ℂ).im) atTop (𝓝 0) := by
    simpa only [Complex.zero_im, mul_zero] using
      ((Complex.continuous_im.tendsto 0).comp hBase).const_mul (2:ℝ)
  have hEq (n : ℕ) : (⟪B (u n), Q n⟫_ℂ).im =
      - (2*(⟪B (u n), source⟫_ℂ).im + 2*(⟪B (u n), L n⟫_ℂ).im +
        2*(⟪B (u n), R n⟫_ℂ).im) := by
    have h := congrArg Complex.im (hVac n)
    simp only [inner_add_right, inner_smul_right, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at h
    linarith
  simp_rw [hEq]
  simpa only [zero_add, add_zero] using ((hBaseIm.add hHessian).add hRem).neg

end Burnett.V03
