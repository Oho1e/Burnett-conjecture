import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CoefficientRadianLimit

set_option autoImplicit false
set_option maxHeartbeats 5100000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Metric Set
open scoped ContDiff ENNReal NNReal

def cartesianRemainderSymbol (w : SchwartzMap E ℂ) (s : ℝ)
    (η χ : ℝ → ℝ) (b : Joint → ℂ) (p : Joint) : ℂ :=
  w ((2*s/tau) • p.2)*regularizedLowCartesianSymbol η χ b p

/-- The complementary low operator window has compact joint support. The
fixed near-zero vanishing of the original infrared factor makes this a
smooth single-block kernel. -/
theorem cartesianRemainderSymbol_regular
    (w : SchwartzMap E ℂ) (h₀ : ∀ q : E, (17/16 : ℝ)≤‖q‖ → w q=0)
    {s r ρ : ℝ} (hs : 0<s) (hr : 0<r) (hρ : 0≤ρ)
    (η χ : ℝ → ℝ) (b : Joint → ℂ) (hη : ContDiff ℝ ∞ η)
    (hηzero : ∀ z ≤ r, η z=0) (hχ : ContDiff ℝ ∞ χ)
    (hcut : ∀ z ≥ ρ^2, χ z=0)
    {V : Set Joint} (hV : IsOpen V)
    (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    HasCompactSupport (cartesianRemainderSymbol w s η χ b) ∧
      ContDiff ℝ ∞ (cartesianRemainderSymbol w s η χ b) := by
  have τpos : 0<tau := mul_pos (by norm_num) Real.pi_pos
  let S := 2*s/tau
  have hS : 0<S := by unfold S; positivity
  let H := (17/16 : ℝ)/S
  refine ⟨?_,?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0:E) (ρ*H)).prod (isCompact_closedBall (0:E) H))
    intro p hp
    change cartesianRemainderSymbol w s η χ b p ≠ 0 at hp
    have hq : ‖p.2‖≤H := by
      by_contra! hh
      apply hp
      have h := (div_lt_iff₀ hS).mp hh
      have hhigh : (17/16 : ℝ)≤‖S • p.2‖ := by
        rw [norm_smul,Real.norm_of_nonneg hS.le]
        simpa only [mul_comm] using h.le
      unfold cartesianRemainderSymbol
      rw [h₀ _ hhigh,zero_mul]
    have hp' : ‖p.1‖≤ρ*‖p.2‖ := by
      by_contra! hh
      apply hp
      unfold cartesianRemainderSymbol regularizedLowCartesianSymbol
      rw [lowCartesianSymbol_eq_zero_outside χ b hρ hcut hh.le,smul_zero,mul_zero]
    exact ⟨mem_closedBall_zero_iff.mpr (hp'.trans (mul_le_mul_of_nonneg_left hq hρ)),
      mem_closedBall_zero_iff.mpr hq⟩
  · have smooth := regularizedLowCartesianSymbol_contDiff η χ b hr hρ hη hηzero hχ hcut hV hContains hb
    exact (w.smooth'.comp (contDiff_const.smul contDiff_snd)).mul smooth

private theorem realPart_lipschitz (D : SchwartzMap E ℂ) (L : ℝ≥0)
    (hD : LipschitzWith L D) : LipschitzWith L (fun x : E => (D x).re) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (by simpa only [dist_eq_norm] using hD.dist_le_mul x y)

/-- A compact smooth joint symbol uses exactly one radian reference block.
The actual real Schwartz coefficient may have any value at the origin. -/
theorem exists_compactRadianHighCommutatorPair_bound (B : Joint → ℂ)
    (hc : HasCompactSupport B) (hB : ContDiff ℝ ∞ B) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair B (fun x => (D x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 ∧
      ‖radianHighCommutatorPair B (fun x => (D x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 2 4 := by
  have τpos : 0<tau := mul_pos (by norm_num) Real.pi_pos
  let S := (LinearEquiv.smulOfNeZero (K := ℝ) (M := Joint) tau τpos.ne').toContinuousLinearEquiv
  let A := fun p => B (tau • p)
  have hcA : HasCompactSupport A := hc.comp_homeomorph S.toHomeomorph
  have hA : ContDiff ℝ ∞ A := hB.comp S.contDiff
  have eq : radianHighReferenceBlock A 1 = B := by
    funext p
    simp only [radianHighReferenceBlock,A,inv_one,one_smul,one_div,smul_smul,
      mul_inv_cancel₀ τpos.ne']
  refine ⟨highSlotBlockMoment A,highSlotBlockMoment_lt_top A hcA hA,?_⟩
  intro D L hD f g h
  have prod (v : SchwartzMap E ℂ) (x : E) :
      gapSchwartzProduct (coefficientRealPart D) v x = ((D x).re : ℂ)*v x := by
    rw [gapSchwartzProduct_apply,coefficientRealPart_apply]
  rw [← eq]
  exact radianHighCommutatorPair_referenceBlock_two_paper_bounds A hcA hA
    (by norm_num : (0:ℝ)<1) (realPart_lipschitz D L hD) f g h
    (gapSchwartzProduct (coefficientRealPart D) g) (gapSchwartzProduct (coefficientRealPart D) h) (prod g) (prod h)

/-- A smooth compact symbol has the actual order-one size bound used for
linearity of the radian pairing. -/
theorem exists_cartesianCompact_orderOne_size (B : Joint → ℂ)
    (hc : HasCompactSupport B) (hB : Continuous B) :
    ∃ M : ℝ, 0≤M ∧ ∀ p : Joint, ‖B p‖≤M*(1+‖p.1‖+‖p.2‖) := by
  obtain ⟨x,H⟩ := hB.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  refine ⟨‖B x‖,norm_nonneg _,fun p => (H p).trans ?_⟩
  exact le_mul_of_one_le_right (norm_nonneg _) (by linarith only [norm_nonneg p.1,norm_nonneg p.2])

end Burnett.A06
