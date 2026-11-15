import Burnett.Analysis.Sobolev.TestJet
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/- A genuine C∞ compactly supported test of integral one.  The smooth order
in the Test space is ∞.  The bump API's `n : ℕ∞` is set to its own top,
whose coercion into the ContDiff order is precisely C∞, not analytic ω. -/
noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Burnett.X02.NonzeroTest

open SobolevTestJet

def bump : ContDiffBump (0 : Space) := default

def unitTest : D :=
  ⟨bump.normed (volume : Measure Space),
    ⟨bump.contDiff_normed (n := ⊤), bump.hasCompactSupport_normed⟩⟩

theorem unitTest_integral : (∫ x : Space, (unitTest : Space → ℝ) x) = 1 :=
  bump.integral_normed

theorem unitTest_nonneg (x : Space) : 0 ≤ (unitTest : Space → ℝ) x :=
  bump.nonneg_normed x

theorem unitTest_integrable : Integrable (unitTest : Space → ℝ) volume :=
  bump.integrable_normed

theorem unitTest_integral_ne_zero : (∫ x : Space, (unitTest : Space → ℝ) x) ≠ 0 := by
  rw [unitTest_integral]
  exact one_ne_zero

theorem exists_test_integral_one : ∃ φ : D, (∫ x : Space, (φ : Space → ℝ) x) = 1 :=
  ⟨unitTest, unitTest_integral⟩

theorem exists_test_integral_ne_zero : ∃ φ : D, (∫ x : Space, (φ : Space → ℝ) x) ≠ 0 :=
  ⟨unitTest, unitTest_integral_ne_zero⟩

#print axioms unitTest_integral
#print axioms unitTest_integrable
#print axioms exists_test_integral_ne_zero

end Burnett.X02.NonzeroTest
