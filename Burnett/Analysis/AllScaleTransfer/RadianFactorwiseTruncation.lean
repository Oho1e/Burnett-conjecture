import Burnett.Analysis.AllScaleTransfer.WeightedIntegerRadialFactor
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearChange
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointDyadicWindows

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.A05

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier
open scoped ENNReal

/-- Arbitrary finite signed smooth dyadic truncations of the three
actual inputs are absorbed independently by the same Fourier estimate. -/
theorem exists_radianTrilinearForm_factorwise_truncation_bound :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (m : Joint → ℂ) (C : ℝ), 0 ≤ C →
      (∀ f g h : SchwartzMap E ℂ,
        ‖radianTrilinearForm m f g h‖ ≤ C * (triLpMass f g h 3 3 3).toReal) →
      ∀ (I J L : Finset ℤ) (a b c : ℤ → ℂ),
      (∀ j ∈ I, ‖a j‖ ≤ 1) → (∀ j ∈ J, ‖b j‖ ≤ 1) → (∀ j ∈ L, ‖c j‖ ≤ 1) →
      ∀ f g h : SchwartzMap E ℂ,
        ‖radianTrilinearForm m (finiteIntegerRadialTruncation I a f)
            (finiteIntegerRadialTruncation J b g) (finiteIntegerRadialTruncation L c h)‖ ≤
          (K * C) * (triLpMass f g h 3 3 3).toReal := by
  obtain ⟨D,hD,trunc⟩ := exists_finiteIntegerRadialTruncation_L3_bound
  refine ⟨D.toReal^3,by positivity,?_⟩
  intro m C hC estimate I J L a b c ha hb hc f g h
  let e (q : SchwartzMap E ℂ) := (eLpNorm (q : E → ℂ) (ENNReal.ofReal 3) volume).toReal
  have one (I₀ : Finset ℤ) (ε : ℤ → ℂ) (hε : ∀ j ∈ I₀, ‖ε j‖ ≤ 1) (q : SchwartzMap E ℂ) :
      e (finiteIntegerRadialTruncation I₀ ε q) ≤ D.toReal * e q := by
    have hq : eLpNorm (q : E → ℂ) (ENNReal.ofReal 3) volume ≠ ⊤ :=
      (q.memLp (ENNReal.ofReal 3) volume).eLpNorm_ne_top
    have top : D * eLpNorm (q : E → ℂ) (ENNReal.ofReal 3) volume ≠ ⊤ :=
      ENNReal.mul_ne_top hD.ne hq
    simpa only [e,ENNReal.toReal_mul] using ENNReal.toReal_mono top (trunc I₀ ε hε q)
  have ep (q : SchwartzMap E ℂ) : 0 ≤ e q := ENNReal.toReal_nonneg
  have hd : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  have product :
      e (finiteIntegerRadialTruncation I a f) * e (finiteIntegerRadialTruncation J b g) *
        e (finiteIntegerRadialTruncation L c h) ≤
      (D.toReal*e f)*(D.toReal*e g)*(D.toReal*e h) :=
    mul_le_mul (mul_le_mul (one I a ha f) (one J b hb g) (ep _) (mul_nonneg hd (ep f)))
      (one L c hc h) (ep _) (mul_nonneg (mul_nonneg hd (ep f)) (mul_nonneg hd (ep g)))
  have mass₁ (x y z : SchwartzMap E ℂ) :
      (triLpMass x y z 3 3 3).toReal = e x * e y * e z := by
    simp only [triLpMass,ENNReal.toReal_mul,e]
  apply (estimate _ _ _).trans
  rw [mass₁,mass₁]
  exact (mul_le_mul_of_nonneg_left product hC).trans_eq (by ring)

end Burnett.A05
