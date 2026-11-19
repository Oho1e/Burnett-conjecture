import Burnett.Analysis.CubicEnergy.JointMultiplier.JointTrilinearLimit
import Burnett.Analysis.CubicEnergy.JointMultiplier.SymbolSeminormJoint

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Burnett.RicciSymbol
open scoped ENNReal ContDiff

theorem kernelMoment_eq_ofReal (A : Joint → ℂ) (ha : HasCompactSupport A)
    (hs : ContDiff ℝ ∞ A) (j k : ℕ) :
    kernelMoment A j k =
      ENNReal.ofReal (∫ y : Joint, (1 + ‖y.1‖)^j * (1 + ‖y.2‖)^k * ‖blockKernel A y‖) := by
  exact (ofReal_integral_eq_lintegral_ofReal (blockKernel_mixed_moment A ha hs j k)
    (.of_forall fun _ => by positivity)).symm

/-- A finite ambient jet on the joint unit sphere controls the full-scale
trilinear Fourier pairing, with a constant uniform over the symbol. -/
theorem joint_trilinear_sphere_bound (p s z : ℝ) (hp : 1 < p) (hs : 1 < s) (hz : 1 < z)
    (bal : triBalance p s z) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (m : Joint → ℝ), ContDiffOn ℝ ∞ m {y | y ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ y, m (t • y) = m y) → ∀ (D : ℝ), 0 ≤ D →
      (∀ i : ℕ, i ≤ 15 → ∀ ξ ∈ sphere (0 : Freq8) 1,
        ‖iteratedFDeriv ℝ i (fun u => m (splitFreq u)) ξ‖ ≤ D) →
      ∀ f g h : SchwartzMap E ℂ,
        ‖jointTrilinear m f g h‖ₑ ≤ K * ENNReal.ofReal D * triLpMass f g h p s z := by
  obtain ⟨B₁, B₂, B₃, b₁, b₂, b₃, est⟩ := joint_trilinear_weighted p s z hp hs hz bal
  obtain ⟨C₁, c₁, est₁⟩ := symbol_joint_sphere_moment 1 1
  obtain ⟨C₂, c₂, est₂⟩ := symbol_joint_sphere_moment 5 1
  obtain ⟨C₃, c₃, est₃⟩ := symbol_joint_sphere_moment 1 5
  let K := B₁ * ENNReal.ofReal C₁ + B₂ * ENNReal.ofReal C₂ + B₃ * ENNReal.ofReal C₃
  have hK : K < ⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top b₁ ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top b₂ ENNReal.ofReal_lt_top⟩, ENNReal.mul_lt_top b₃ ENNReal.ofReal_lt_top⟩
  refine ⟨K, hK, ?_⟩
  intro m hm hh D d0 jet f g h
  obtain ⟨hc, hd⟩ := symbolBlock_regular m hm
  have bound (j k : ℕ) (C : ℝ) (c0 : 0 ≤ C)
      (hC : (∫ y : Joint, (1 + ‖y.1‖)^j * (1 + ‖y.2‖)^k * ‖blockKernel (symbolBlock m) y‖)
        ≤ C * D) :
      kernelMoment (symbolBlock m) j k ≤ ENNReal.ofReal C * ENNReal.ofReal D := by
    rw [kernelMoment_eq_ofReal _ hc hd, ← ENNReal.ofReal_mul c0]
    exact ENNReal.ofReal_le_ofReal hC
  have e₁ := mul_le_mul_left' (bound 1 1 C₁ c₁ (est₁ m hm hh D d0
    (fun i hi => jet i (by omega)))) B₁
  have e₂ := mul_le_mul_left' (bound 5 1 C₂ c₂ (est₂ m hm hh D d0
    (fun i hi => jet i (by omega)))) B₂
  have e₃ := mul_le_mul_left' (bound 1 5 C₃ c₃ (est₃ m hm hh D d0
    (fun i hi => jet i (by omega)))) B₃
  refine (est m hm hh f g h).trans (mul_le_mul_right' ?_ _)
  unfold K
  simp only [add_mul, mul_assoc]
  exact add_le_add (add_le_add e₁ e₂) e₃

end Burnett.A02.FrequencySplit
