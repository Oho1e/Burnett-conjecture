import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Burnett.Analysis.LowRatio

/-- A fixed positive ratio strip allows only finitely many relative dyadic
annular shifts. The radial annulus bounds can already include the fixed
comparison of physical and transformed magnitudes. -/
theorem exists_uniform_annular_shift_bound (ratioLo ratioHi annLo annHi : ℝ)
    (hRatioLo : 0 < ratioLo) (hRatioHi : 0 ≤ ratioHi) (hAnnLo : 0 < annLo) :
    ∃ N : ℕ, ∀ (i j : ℤ) (u v : ℝ),
      annLo * (2 : ℝ)^i ≤ u → u ≤ annHi * (2 : ℝ)^i →
      annLo * (2 : ℝ)^j ≤ v → v ≤ annHi * (2 : ℝ)^j →
      ratioLo ≤ u / v → u / v ≤ ratioHi →
      -(N : ℤ) ≤ i - j ∧ i - j ≤ N := by
  let A := ratioHi * annHi / annLo
  let B := annHi / (ratioLo * annLo)
  have hTwo : (1 : ℝ) < 2 := by norm_num
  have hTwoPos : (0 : ℝ) < 2 := zero_lt_one.trans hTwo
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max A B) hTwo
  refine ⟨N, ?_⟩
  intro i j u v huL huU hvL hvU hrL hrU
  have hi : 0 < (2 : ℝ)^i := zpow_pos hTwoPos _
  have hj : 0 < (2 : ℝ)^j := zpow_pos hTwoPos _
  have hvPos : 0 < v := (mul_pos hAnnLo hj).trans_le hvL
  have hRatioU := (div_le_iff₀ hvPos).mp hrU
  have hRatioL := (le_div_iff₀ hvPos).mp hrL
  have hUp : (2 : ℝ)^(i - j) ≤ A := by
    rw [zpow_sub₀ hTwoPos.ne']
    apply (div_le_iff₀ hj).mpr
    have h : annLo * (2 : ℝ)^i ≤ ratioHi * (annHi * (2 : ℝ)^j) :=
      huL.trans (hRatioU.trans (mul_le_mul_of_nonneg_left hvU hRatioHi))
    calc
      _ ≤ (ratioHi * (annHi * (2 : ℝ)^j)) / annLo := by
        apply (le_div_iff₀ hAnnLo).mpr
        rwa [mul_comm]
      _ = _ := by dsimp [A]; ring
  have hDn : (2 : ℝ)^(j - i) ≤ B := by
    rw [zpow_sub₀ hTwoPos.ne']
    apply (div_le_iff₀ hi).mpr
    have h : ratioLo * (annLo * (2 : ℝ)^j) ≤ annHi * (2 : ℝ)^i :=
      (mul_le_mul_of_nonneg_left hvL hRatioLo.le).trans (hRatioL.trans huU)
    calc
      _ ≤ (annHi * (2 : ℝ)^i) / (ratioLo * annLo) := by
        apply (le_div_iff₀ (mul_pos hRatioLo hAnnLo)).mpr
        simpa only [mul_comm ((2 : ℝ)^j), mul_assoc] using h
      _ = _ := by dsimp [B]; ring
  have hUpper : i - j ≤ (N : ℤ) := (zpow_le_zpow_iff_right₀ hTwo).mp (by
    simpa only [zpow_natCast] using hUp.trans ((le_max_left _ _).trans hN.le))
  have hLower : j - i ≤ (N : ℤ) := (zpow_le_zpow_iff_right₀ hTwo).mp (by
    simpa only [zpow_natCast] using hDn.trans ((le_max_right _ _).trans hN.le))
  exact ⟨by omega, hUpper⟩

end Burnett.Analysis.LowRatio
