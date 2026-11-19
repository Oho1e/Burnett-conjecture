import Burnett.Analysis.DyadicSquare.SquareEnergy

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.DyadicSquare
open MeasureTheory Finset Set Burnett.Fourier
open scoped BigOperators

private def openShell : Set Space := {ξ | 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2}
private def shellMask : BoundedSymbol Space where
  toFun := openShell.indicator (fun _ => 1)
  measurable := by
    have hm : MeasurableSet openShell := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
    exact (measurable_const.indicator hm).aestronglyMeasurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le ξ := by by_cases h : ξ ∈ openShell <;> simp [h]

private theorem mask_support (ξ : Space) (h : shellMask ξ ≠ 0) : 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2 := by
  by_contra hn
  have outside : ξ ∉ openShell := hn
  exact h (by simp [shellMask,outside])

private theorem signed_symbol_bound (m : BoundedSymbol Space)
    (cut : ∀ ξ, m ξ ≠ 0 → ξ ∈ openShell) (t : ℝ) (ht : 0<t)
    (c : ℕ → ℂ) (hc : ∀ k, ‖c k‖ ≤ 1) (ξ : Space) (I : Finset ℕ) :
    ‖∑ k ∈ I, c k * m (((2:ℝ)^k*t) • ξ)‖ ≤ 2*m.bound := by
  let z := fun k : ℕ => ((2:ℝ)^k*t) • ξ
  have term (k : ℕ) : ‖c k * m (z k)‖ ≤ ‖shellMask (z k)‖^2 * m.bound := by
    by_cases h : z k ∈ openShell
    · simpa [shellMask,h,norm_mul] using mul_le_mul (hc k) (m.norm_le (z k)) (norm_nonneg _) zero_le_one
    · have hm : m (z k) = 0 := by by_contra hn; exact h (cut _ hn)
      simp [hm,shellMask,h]
  refine (norm_sum_le _ _).trans ((sum_le_sum (fun k _ => term k)).trans ?_)
  rw [← sum_mul]
  apply mul_le_mul_of_nonneg_right _ m.bound_nonneg
  simpa only [shellMask,one_pow,mul_one,z] using two_annular_scales shellMask mask_support t ht ξ I

/-- A finite sum of dyadic annular symbols with arbitrary coefficients in the
closed complex unit disk. Its multiplier bound is uniform in their number. -/
def signedBandsSymbol (m : BoundedSymbol Space)
    (cut : ∀ ξ, m ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (t : ℝ) (ht : 0<t)
    (c : ℕ → ℂ) (hc : ∀ k, ‖c k‖ ≤ 1) (I : Finset ℕ) : BoundedSymbol Space where
  toFun ξ := ∑ k ∈ I, c k * m (((2:ℝ)^k*t) • ξ)
  measurable := I.aestronglyMeasurable_fun_sum fun k _ => aestronglyMeasurable_const.mul
    (rescaleSymbol m ((2:ℝ)^k*t) (mul_pos (by positivity) ht)).measurable
  bound := 2*m.bound
  bound_nonneg := mul_nonneg (by norm_num) m.bound_nonneg
  norm_le ξ := signed_symbol_bound m cut t ht c hc ξ I

private theorem aeval_sum (m : BoundedSymbol Space) (t : ℝ) (ht : 0<t)
    (c : ℕ → ℂ) (I : Finset ℕ) (u : ComplexL2 Space) :
    (fun ξ => (∑ k ∈ I, c k • symbolL2 (rescaleSymbol m ((2:ℝ)^k*t) (mul_pos (by positivity) ht)) u) ξ) =ᵐ[volume]
      fun ξ => (∑ k ∈ I, c k * m (((2:ℝ)^k*t) • ξ)) * u ξ := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simpa only [sum_empty,zero_mul] using (Lp.coeFn_zero ℂ 2 (volume : Measure Space))
  | @insert k I hk ih =>
    let B := rescaleSymbol m ((2:ℝ)^k*t) (mul_pos (by positivity) ht)
    simp only [sum_insert hk]
    filter_upwards [Lp.coeFn_add (c k • symbolL2 B u)
      (∑ j ∈ I, c j • symbolL2 (rescaleSymbol m ((2:ℝ)^j*t) (mul_pos (by positivity) ht)) u),
      Lp.coeFn_smul (c k) (symbolL2 B u),symbolL2_ae B u,ih] with ξ ha hc hs hi
    rw [ha,Pi.add_apply,hc,Pi.smul_apply,smul_eq_mul,hs,hi]
    dsimp only [B,rescaleSymbol]
    ring

theorem signed_annular_sum_L2 (m : BoundedSymbol Space)
    (cut : ∀ ξ, m ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (t : ℝ) (ht : 0<t)
    (c : ℕ → ℂ) (hc : ∀ k, ‖c k‖ ≤ 1) (I : Finset ℕ) (u : ComplexL2 Space) :
    ‖∑ k ∈ I, c k • fourierMultiplier (rescaleSymbol m ((2:ℝ)^k*t) (mul_pos (by positivity) ht)) u‖ ≤
      (2*m.bound) * ‖u‖ := by
  let B := signedBandsSymbol m cut t ht c hc I
  have he : (∑ k ∈ I, c k • fourierMultiplier (rescaleSymbol m ((2:ℝ)^k*t) (mul_pos (by positivity) ht)) u) =
      fourierMultiplier B u := by
    apply fourierL2Equiv.injective
    simp only [map_sum,map_smul,fourier_fourierMultiplier]
    apply Lp.ext
    exact (aeval_sum m t ht c I (fourierL2Equiv u)).trans (symbolL2_ae B _).symm
  rw [he]
  exact fourierMultiplier_norm_le B u

end Burnett.Analysis.SignedFourierWindow
