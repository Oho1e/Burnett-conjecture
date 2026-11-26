import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotLowCoefficientGeometry

set_option autoImplicit false
set_option maxHeartbeats 3900000
noncomputable section
namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit
open scoped ContDiff FourierTransform

private theorem shiftedCoefficient_interval {w z : E} {lo hi d : ℝ}
    (hlo : lo ≤ ‖z‖) (hhi : ‖z‖ ≤ hi) (hw : ‖w‖ ≤ d) :
    lo-d ≤ ‖w-z‖ ∧ ‖w-z‖ ≤ hi+d := by
  have hl := norm_sub_le w (w-z)
  rw [sub_sub_cancel] at hl
  exact ⟨by linarith,by linarith only [norm_sub_le w z,hhi,hw]⟩

/-- The coefficient annulus stays annular in either shifted high slot.
The second shifted slot uses the negative output frequency of the tested form. -/
theorem highCoefficient_separated_annuli {p q Z : E} {lo hi ρ a b r r₀ : ℝ}
    (hr : 0 ≤ r) (hrr : r ≤ r₀) (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hgap : r₀*(1+ρ)*hi < a)
    (hq : lo ≤ ‖q‖ ∧ ‖q‖ ≤ hi) (hp : ‖p‖ ≤ ρ*‖q‖)
    (hZ : a ≤ ‖Z‖ ∧ ‖Z‖ ≤ b) :
    let d := r₀*(1+ρ)*hi
    0 < a-d ∧ ‖p‖ ≤ ρ*hi ∧
    ((1-ρ)*lo ≤ ‖p+q‖ ∧ ‖p+q‖ ≤ (1+ρ)*hi) ∧
    (a-d ≤ ‖r • q-Z‖ ∧ ‖r • q-Z‖ ≤ b+d) ∧
    (a-d ≤ ‖r • (-(p+q))-Z‖ ∧ ‖r • (-(p+q))-Z‖ ≤ b+d) := by
  dsimp only
  have hi0 := (norm_nonneg q).trans hq.2
  have houtlo : (1-ρ)*‖q‖ ≤ ‖p+q‖ := by
    have h := norm_sub_le (p+q) p
    rw [add_sub_cancel_left] at h
    linarith only [h,hp]
  have houthi : ‖p+q‖ ≤ (1+ρ)*hi := by
    have hp' := hp.trans (mul_le_mul_of_nonneg_left hq.2 hρ)
    linarith only [norm_add_le p q,hp',hq.2]
  have hs (v : E) (hv : ‖v‖ ≤ (1+ρ)*hi) : ‖r • v‖ ≤ r₀*(1+ρ)*hi := by
    rw [norm_smul,Real.norm_of_nonneg hr,mul_assoc]
    exact mul_le_mul hrr hv (norm_nonneg v) (hr.trans hrr)
  exact ⟨sub_pos.mpr hgap,hp.trans (mul_le_mul_of_nonneg_left hq.2 hρ),
    ⟨(mul_le_mul_of_nonneg_left hq.1 (sub_nonneg.mpr hρ'.le)).trans houtlo,houthi⟩,
    shiftedCoefficient_interval hZ.1 hZ.2 (hs q (by nlinarith only [hq.2,mul_nonneg hρ hi0])),
    shiftedCoefficient_interval hZ.1 hZ.2 (hs (-(p+q)) (by simpa only [norm_neg] using houthi))⟩

def gapSchwartzProduct (C g : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) C.hasTemperateGrowth g

theorem gapSchwartzProduct_apply (C g : SchwartzMap E ℂ) (x : E) :
    gapSchwartzProduct C g x = C x * g x := mul_comm _ _

private theorem gapSchwartzProduct_coe (C g : SchwartzMap E ℂ) :
    (gapSchwartzProduct C g : E → ℂ) = fun x => C x * g x :=
  funext (gapSchwartzProduct_apply C g)

/-- Insertion of the actual windows in both reference multiplier terms.
Either the physical high input or the physical output test receives the
coefficient-scale annular window. -/
theorem highCoefficientGap_insert_tested_windows
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ ac bc r r₀ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hr : 0<r) (hrr : r≤r₀) (hgap : r₀*(1+ρ)*hi < ac)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d : SchwartzMap E ℂ) (u v w l : ℝ)
    (hTop : ∀ z : E, ac-r₀*(1+ρ)*hi ≤ ‖z‖ → ‖z‖ ≤ bc+r₀*(1+ρ)*hi → a (u • z) = 1)
    (hIn : ∀ z : E, lo ≤ ‖z‖ → ‖z‖ ≤ hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (l • z) = 1)
    (s : ℝ) (C f g h : SchwartzMap E ℂ)
    (hC : ∀ z : E, 𝓕 (C : E → ℂ) z ≠ 0 → ac ≤ ‖(r*s) • z‖ ∧ ‖(r*s) • z‖ ≤ bc) :
    testedBlock A s f (gapSchwartzProduct C g) h =
      testedBlock A s (windowTest d f (l*s)) (gapSchwartzProduct C (windowTest a g ((u*r)*s)))
        (windowTest e h (w*s)) ∧
    testedBlock A s f g (gapSchwartzProduct C h) =
      testedBlock A s (windowTest d f (l*s)) (windowTest b g (v*s))
        (gapSchwartzProduct C (windowTest a h ((u*r)*s))) := by
  let F := windowTest d f (l*s)
  let G := windowTest b g (v*s)
  let H := windowTest e h (w*s)
  let Gtop := windowTest a g ((u*r)*s)
  let Htop := windowTest a h ((u*r)*s)
  have dat (p : Joint) (hp : A (s • p) ≠ 0) :
      lo ≤ ‖s • p.2‖ ∧ ‖s • p.2‖ ≤ hi ∧ ‖s • p.1‖ ≤ ρ*‖s • p.2‖ := hBand (s • p) hp
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
    have hlo : (1-ρ)*lo ≤ ‖s • (-(p.1+p.2))‖ := by
      have ht := norm_sub_le (s • p.1+s • p.2) (s • p.1)
      rw [add_sub_cancel_left] at ht
      rw [smul_neg,smul_add,norm_neg]
      apply (mul_le_mul_of_nonneg_left (dat p hp).1 (sub_nonneg.mpr hρ'.le)).trans
      linarith only [ht,(dat p hp).2.2]
    have hhi : ‖s • (-(p.1+p.2))‖ ≤ (1+ρ)*hi := by
      rw [smul_neg,smul_add,norm_neg]
      linarith only [norm_add_le (s • p.1) (s • p.2),(dat p hp).2.1,
        (dat p hp).2.2.trans (mul_le_mul_of_nonneg_left (dat p hp).2.1 hρ)]
    rw [show H = windowTest e h (w*s) from rfl,windowTest_fourier,← smul_smul,hOut _ hlo hhi,mul_one]
  have shifted (p : Joint) (hp : A (s • p) ≠ 0) (z : E) (hz : 𝓕 (C : E → ℂ) z ≠ 0) :
      (ac-r₀*(1+ρ)*hi ≤ ‖(r*s) • (p.2-z)‖ ∧ ‖(r*s) • (p.2-z)‖ ≤ bc+r₀*(1+ρ)*hi) ∧
      (ac-r₀*(1+ρ)*hi ≤ ‖(r*s) • (-(p.1+p.2)-z)‖ ∧
        ‖(r*s) • (-(p.1+p.2)-z)‖ ≤ bc+r₀*(1+ρ)*hi) := by
    obtain ⟨hl,hu,hp'⟩ := dat p hp
    have geom := highCoefficient_separated_annuli hr.le hrr hρ hρ' hgap ⟨hl,hu⟩ hp' (hC z hz)
    simpa only [smul_sub,smul_smul,smul_neg,smul_add] using geom.2.2.2
  have gpwin (p : Joint) (hp : A (s • p) ≠ 0) :
      𝓕 (gapSchwartzProduct C Gtop : E → ℂ) p.2 = 𝓕 (gapSchwartzProduct C g : E → ℂ) p.2 := by
    rw [gapSchwartzProduct_coe,gapSchwartzProduct_coe]
    apply fourier_schwartz_product_replace
    intro z hz
    have hw := (shifted p hp z hz).1
    rw [show Gtop = windowTest a g ((u*r)*s) from rfl,windowTest_fourier,
      show (u*r)*s = u*(r*s) by ring,← smul_smul,hTop _ hw.1 hw.2,mul_one]
  have hpwin (p : Joint) (hp : A (s • p) ≠ 0) :
      𝓕 (gapSchwartzProduct C Htop : E → ℂ) (-(p.1+p.2)) =
        𝓕 (gapSchwartzProduct C h : E → ℂ) (-(p.1+p.2)) := by
    rw [gapSchwartzProduct_coe,gapSchwartzProduct_coe]
    apply fourier_schwartz_product_replace
    intro z hz
    have hw := (shifted p hp z hz).2
    rw [show Htop = windowTest a h ((u*r)*s) from rfl,windowTest_fourier,
      show (u*r)*s = u*(r*s) by ring,← smul_smul,hTop _ hw.1 hw.2,mul_one]
  change testedBlock A s f (gapSchwartzProduct C g) h = testedBlock A s F
      (gapSchwartzProduct C Gtop) H ∧
    testedBlock A s f g (gapSchwartzProduct C h) = testedBlock A s F G (gapSchwartzProduct C Htop)
  constructor <;> simp only [testedBlock_density A ha hA] <;> apply integral_congr_ae <;>
    filter_upwards with p <;> by_cases hp : A (s • p) = 0
  · simp only [triDensity,hp,zero_mul]
  · simp only [triDensity,fwin p hp,gpwin p hp,hwin p hp]
  · simp only [triDensity,hp,zero_mul]
  · simp only [triDensity,fwin p hp,gwin p hp,hpwin p hp]

end Burnett.A06
