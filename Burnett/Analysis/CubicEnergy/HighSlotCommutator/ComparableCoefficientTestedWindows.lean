import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighCoefficientGapWindows

set_option autoImplicit false
set_option maxHeartbeats 3800000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open MeasureTheory
open scoped ContDiff FourierTransform

/-- At comparable coefficient scales one actual test is still annular in
each commutator term. The other high slot can now use a low-pass window
covering all shifted frequencies, including zero. -/
theorem comparableCoefficient_insert_tested_windows
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ bc : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d : SchwartzMap E ℂ) (u v w l : ℝ)
    (hShift : ∀ z : E, ‖z‖ ≤ bc+(1+ρ)*hi → a (u • z) = 1)
    (hIn : ∀ z : E, lo ≤ ‖z‖ → ‖z‖ ≤ hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (l • z) = 1)
    (s : ℝ) (C f g h : SchwartzMap E ℂ)
    (hC : ∀ z : E, 𝓕 (C : E → ℂ) z ≠ 0 → ‖s • z‖ ≤ bc) :
    testedBlock A s f (gapSchwartzProduct C g) h =
      testedBlock A s (windowTest d f (l*s)) (gapSchwartzProduct C (windowTest a g (u*s)))
        (windowTest e h (w*s)) ∧
    testedBlock A s f g (gapSchwartzProduct C h) =
      testedBlock A s (windowTest d f (l*s)) (windowTest b g (v*s))
        (gapSchwartzProduct C (windowTest a h (u*s))) := by
  let F := windowTest d f (l*s)
  let G := windowTest b g (v*s)
  let H := windowTest e h (w*s)
  let Gshift := windowTest a g (u*s)
  let Hshift := windowTest a h (u*s)
  have dat (p : Joint) (hp : A (s • p) ≠ 0) :
      lo ≤ ‖s • p.2‖ ∧ ‖s • p.2‖ ≤ hi ∧ ‖s • p.1‖ ≤ ρ*‖s • p.2‖ := hBand (s • p) hp
  have pout (p : Joint) (hp : A (s • p) ≠ 0) :
      (1-ρ)*lo ≤ ‖s • (-(p.1+p.2))‖ ∧ ‖s • (-(p.1+p.2))‖ ≤ (1+ρ)*hi := by
    obtain ⟨hlo,hhi,hlow⟩ := dat p hp
    rw [smul_neg,smul_add,norm_neg]
    constructor
    · have ht := norm_sub_le (s • p.1+s • p.2) (s • p.1)
      rw [add_sub_cancel_left] at ht
      refine (mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr hρ'.le)).trans ?_
      linarith only [ht,hlow]
    · linarith only [norm_add_le (s • p.1) (s • p.2),hhi,hlow.trans
        (mul_le_mul_of_nonneg_left hhi hρ)]
  have fwin (p : Joint) (hp : A (s • p) ≠ 0) :
      𝓕 (F : E → ℂ) p.1 = 𝓕 (f : E → ℂ) p.1 := by
    rw [show F = windowTest d f (l*s) from rfl,windowTest_fourier,← smul_smul,hLow _ ((dat p hp).2.2.trans
      (mul_le_mul_of_nonneg_left (dat p hp).2.1 hρ)),mul_one]
  have gwin (p : Joint) (hp : A (s • p) ≠ 0) :
      𝓕 (G : E → ℂ) p.2 = 𝓕 (g : E → ℂ) p.2 := by
    rw [show G = windowTest b g (v*s) from rfl,windowTest_fourier,← smul_smul,
      hIn _ (dat p hp).1 (dat p hp).2.1,mul_one]
  have hwin (p : Joint) (hp : A (s • p) ≠ 0) :
      𝓕 (H : E → ℂ) (-(p.1+p.2)) = 𝓕 (h : E → ℂ) (-(p.1+p.2)) := by
    rw [show H = windowTest e h (w*s) from rfl,windowTest_fourier,← smul_smul,
      hOut _ (pout p hp).1 (pout p hp).2,mul_one]
  have place (q : E) (hq : ‖s • q‖≤(1+ρ)*hi) (v : SchwartzMap E ℂ) :
      𝓕 (gapSchwartzProduct C (windowTest a v (u*s)) : E → ℂ) q =
        𝓕 (gapSchwartzProduct C v : E → ℂ) q := by
    have coe (V : SchwartzMap E ℂ) : (gapSchwartzProduct C V : E → ℂ) = fun x => C x * V x :=
      funext (gapSchwartzProduct_apply C V)
    rw [coe,coe]
    apply fourier_schwartz_product_replace
    intro z hz
    have hqz : ‖s • (q-z)‖ ≤ bc+(1+ρ)*hi := by
      rw [smul_sub]
      linarith only [norm_sub_le (s • q) (s • z),hq,hC z hz]
    rw [windowTest_fourier,← smul_smul,hShift _ hqz,mul_one]
  have hinbound (p : Joint) (hp : A (s • p) ≠ 0) : ‖s • p.2‖ ≤ (1+ρ)*hi := by
    have hi0 := (norm_nonneg (s • p.2)).trans (dat p hp).2.1
    nlinarith only [(dat p hp).2.1,mul_nonneg hρ hi0]
  change testedBlock A s f (gapSchwartzProduct C g) h = testedBlock A s F
      (gapSchwartzProduct C Gshift) H ∧
    testedBlock A s f g (gapSchwartzProduct C h) = testedBlock A s F G (gapSchwartzProduct C Hshift)
  constructor <;> simp only [testedBlock_density A ha hA] <;> apply integral_congr_ae <;>
    filter_upwards with p <;> by_cases hp : A (s • p)=0
  · simp only [triDensity,hp,zero_mul]
  · simp only [triDensity,fwin p hp,hwin p hp,Gshift,place p.2 (hinbound p hp) g]
  · simp only [triDensity,hp,zero_mul]
  · simp only [triDensity,fwin p hp,gwin p hp,Hshift,place (-(p.1+p.2)) (pout p hp).2 h]

end Burnett.A06
