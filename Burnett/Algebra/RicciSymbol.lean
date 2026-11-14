import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace Burnett.RicciSymbol

open scoped BigOperators

/-- Four coordinate indices at a fixed spacetime point. -/
abbrev Index := Fin 4
/-- Real covector components. -/
abbrev Covector := Index → ℝ
/-- Covariant two-tensor components; all contractions use ordered pairs. -/
abbrev Tensor2 := Index → Index → ℝ

/-- Raising one covector index using the inverse metric components. -/
def raiseCovector (gInv : Tensor2) (v : Covector) (a : Index) : ℝ :=
  ∑ d, gInv a d * v d

/-- Raising the second index of a covariant two-tensor. -/
def raiseSecond (gInv k : Tensor2) (c a : Index) : ℝ :=
  ∑ d, gInv a d * k c d

/-- The scalar `s = g^{ab} ξ_a ξ_b` in the Ricci symbol. -/
def symbolNorm (gInv : Tensor2) (ξ : Covector) : ℝ :=
  ∑ a, ∑ b, gInv a b * ξ a * ξ b

/-- The metric trace `t = g^{ab} k_ab`, summing all ordered indices. -/
def metricTrace (gInv k : Tensor2) : ℝ :=
  ∑ a, ∑ b, gInv a b * k a b

/-- The covector `q_b = ξ^a k_ab`. -/
def contracted (gInv : Tensor2) (ξ : Covector) (k : Tensor2) (b : Index) : ℝ :=
  ∑ a, raiseCovector gInv ξ a * k a b

/-- The Ricci symbol in paper/burnett.tex, equation (ricci-symbol). -/
def ricciSymbol (gInv : Tensor2) (ξ : Covector) (k : Tensor2) (a b : Index) : ℝ :=
  (symbolNorm gInv ξ * k a b + ξ a * ξ b * metricTrace gInv k -
    ξ a * contracted gInv ξ k b - ξ b * contracted gInv ξ k a) / 2

/-- The covariant pure gauge tensor `ξ ⊗ v + v ⊗ ξ`. -/
def pureGauge (ξ v : Covector) (a b : Index) : ℝ := ξ a * v b + v a * ξ b

/-- The explicit gauge covector `(q - t ξ / 2) / s` off the characteristic cone. -/
def kernelGaugeVector (gInv : Tensor2) (ξ : Covector) (k : Tensor2) (b : Index) : ℝ :=
  (contracted gInv ξ k b - metricTrace gInv k * ξ b / 2) / symbolNorm gInv ξ

/-- Every tensor in the noncharacteristic Ricci-symbol kernel has the paper's
explicit pure gauge representation. This implication needs no signature assumption. -/
theorem kernel_eq_pureGauge (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hs : symbolNorm gInv ξ ≠ 0) (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0) :
    k = pureGauge ξ (kernelGaugeVector gInv ξ k) := by
  funext a b
  have h := hk a b
  unfold ricciSymbol at h
  unfold pureGauge kernelGaugeVector
  field_simp [hs]
  nlinarith

/-- The first-order connection symbol `c(k)^a_bc` used to define `B`. -/
def connectionSymbol (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (a b c : Index) : ℝ :=
  (ξ b * raiseSecond gInv k c a + ξ c * raiseSecond gInv k b a -
    raiseCovector gInv ξ a * k b c) / 2

/-- The quadratic tensor `B_bc(k,k)` from the paper, with both contracted indices
summed over all ordered values. -/
def quadraticSymbol (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (b c : Index) : ℝ :=
  ∑ a, ∑ e,
    (connectionSymbol gInv ξ k a c e * connectionSymbol gInv ξ k e b a -
      connectionSymbol gInv ξ k a a e * connectionSymbol gInv ξ k e b c)

/-- Raising the second index of a pure gauge tensor expands by linearity. -/
theorem raiseSecond_pureGauge (gInv : Tensor2) (ξ v : Covector) (c a : Index) :
    raiseSecond gInv (pureGauge ξ v) c a =
      ξ c * raiseCovector gInv v a + v c * raiseCovector gInv ξ a := by
  unfold raiseSecond pureGauge raiseCovector
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro d hd <;> ring

/-- The paper's pure gauge connection-symbol identity. -/
theorem connectionSymbol_pureGauge (gInv : Tensor2) (ξ v : Covector) (a b c : Index) :
    connectionSymbol gInv ξ (pureGauge ξ v) a b c =
      ξ b * ξ c * raiseCovector gInv v a := by
  simp only [connectionSymbol, raiseSecond_pureGauge, pureGauge]
  ring

/-- A pure gauge tensor makes the paper's full ordered-sum quadratic symbol vanish. -/
theorem quadraticSymbol_pureGauge (gInv : Tensor2) (ξ v : Covector) (b c : Index) :
    quadraticSymbol gInv ξ (pureGauge ξ v) b c = 0 := by
  unfold quadraticSymbol
  simp only [connectionSymbol_pureGauge]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro e he
  ring

/-- The quadratic symbol vanishes on the noncharacteristic Ricci-symbol kernel.
This is the real, diagonal identity only; no polarization or measure assertion
is included in this statement. -/
theorem quadraticSymbol_eq_zero_of_noncharacteristic_kernel
    (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hs : symbolNorm gInv ξ ≠ 0) (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0)
    (b c : Index) : quadraticSymbol gInv ξ k b c = 0 := by
  rw [kernel_eq_pureGauge gInv ξ k hs hk]
  exact quadraticSymbol_pureGauge gInv ξ (kernelGaugeVector gInv ξ k) b c

end Burnett.RicciSymbol
