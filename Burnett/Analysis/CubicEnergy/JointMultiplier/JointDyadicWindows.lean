import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowTest
import Burnett.Analysis.SignedFourierWindow.TwoAnnularOneLow

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset
open scoped ENNReal

def dyadicScale (t : ℝ) (k : ℕ) : ℝ := 2^k*t

def shiftedTest (a f : SchwartzMap E ℂ) (c t : ℝ) (k : ℕ) (y x : E) : ℂ :=
  windowTest a f (c*dyadicScale t k) (x-dyadicScale t k • y)

private theorem scale_pos (t : ℝ) (ht : 0<t) (k : ℕ) : 0<dyadicScale t k := mul_pos (by positivity) ht

theorem shiftedTest_fourier (a f : SchwartzMap E ℂ) (c t : ℝ) (hc : 0<c) (ht : 0<t)
    (k : ℕ) (y x : E) :
    shiftedTest a f c t k y x = shiftedWindowOperator a f (2^k*(c*t)) ((-c⁻¹) • y) x := by
  rw [shiftedTest,windowTest_translate _ _ _ _ (mul_pos hc (scale_pos t ht k))]
  have eq : -dyadicScale t k/(c*dyadicScale t k) = -c⁻¹ := by
    field_simp [hc.ne',(scale_pos t ht k).ne']
  rw [eq,dyadicScale,show c*((2:ℝ)^k*t)=2^k*(c*t) by ring]

private theorem shiftedTest_kernel (a f : SchwartzMap E ℂ) (c t : ℝ) (hc : 0<c) (ht : 0<t)
    (k : ℕ) (y x : E) :
    shiftedTest a f c t k y x = kernelApply (annularKernel a (c*t) ((-c⁻¹) • y) k) f x := by
  rw [shiftedTest_fourier _ _ _ _ hc ht,shifted_window_physical _ _ _ (mul_pos (by positivity) (mul_pos hc ht))]
  rfl

def triBalance (p s z : ℝ) : Prop :=
  (ENNReal.ofReal p)⁻¹+(ENNReal.ofReal s)⁻¹+(ENNReal.ofReal z)⁻¹ = 1

def triLpMass (f g h : SchwartzMap E ℂ) (p s z : ℝ) : ℝ≥0∞ :=
  eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume * eLpNorm (g : E → ℂ) (ENNReal.ofReal s) volume *
  eLpNorm (h : E → ℂ) (ENNReal.ofReal z) volume

/-- A common base dyadic scale cancels from each modulation ratio. The three
spatial translations may vary independently from each other. -/
theorem dyadic_two_high_one_low (a b d : SchwartzMap E ℂ) (ha : HasCompactSupport (a : E → ℂ))
    (hb : HasCompactSupport (b : E → ℂ)) (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (p s z : ℝ) (hp : 1<p) (hs : 1<s) (hz : 1<z)
    (bal : triBalance p s z) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (u v w t : ℝ), 0<u → 0<v → 0<w → 0<t → ∀ (y₁ y₂ y₃ : E) (n : ℕ)
      (f g h : SchwartzMap E ℂ),
      (∫⁻ x : E, ∑ i : Fin n, ‖shiftedTest a f u t i y₁ x*shiftedTest b g v t i y₂ x*
        shiftedTest d h w t i y₃ x‖ₑ) ≤
      C*ENNReal.ofReal (1+‖(-u⁻¹) • y₁‖)*ENNReal.ofReal (1+‖(-v⁻¹) • y₂‖)*
        ENNReal.ofReal ((1+‖(-w⁻¹) • y₃‖)^5)*triLpMass f g h p s z := by
  let P := ENNReal.ofReal p
  let S := ENNReal.ofReal s
  let Z := ENNReal.ofReal z
  let M := (P⁻¹+S⁻¹)⁻¹
  letI : ENNReal.HolderTriple P S M := ENNReal.HolderTriple.of P S
  letI : ENNReal.HolderTriple M Z 1 := ⟨by simpa only [M,inv_inv,inv_one] using bal⟩
  obtain ⟨C,cf,H⟩ := two_annular_one_low a b d ha hb ca cb p s z hp hs hz M
  refine ⟨C,cf,?_⟩
  intro u v w t hu hv hw ht y₁ y₂ y₃ n f g h
  let e : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  have bound := H (u*t) (v*t) (mul_pos hu ht) (mul_pos hv ht)
    ((-u⁻¹) • y₁) ((-v⁻¹) • y₂) ((-w⁻¹) • y₃) n e e (fun i => 2^(i:ℕ)*(w*t))
    (fun i => mul_pos (by positivity) (mul_pos hw ht)) f g h (f.memLp _) (g.memLp _)
  refine le_trans (le_of_eq (lintegral_congr (fun x => ?_))) (bound.trans_eq (by unfold triLpMass; ac_rfl))
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  apply sum_congr rfl
  intro i _
  rw [shiftedTest_kernel a f u t hu ht,shiftedTest_kernel b g v t hv ht,shiftedTest_fourier d h w t hw ht]
  simp only [enorm_mul,ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    ENNReal.ofReal_mul (norm_nonneg _),ofReal_norm_eq_enorm]
  rfl

end Burnett.A02.FrequencySplit
