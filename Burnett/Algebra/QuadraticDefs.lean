import Burnett.Algebra.RicciSymbol

noncomputable section

namespace Burnett.RicciSymbol

open scoped BigOperators

/-- Component symmetry, used explicitly for both the inverse metric and amplitude. -/
def IsSymmetricTensor (k : Tensor2) : Prop := ∀ a b, k a b = k b a

/-- Real bilinear contraction `k_ab l^{ab}`, with all ordered indices included. -/
def tensorPairing (gInv k l : Tensor2) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, gInv a c * gInv b d * k a b * l c d

/-- The tensor `(k²)_bc = k_b{}^a k_ac` in the full quadratic expansion. -/
def tensorSquare (gInv k : Tensor2) (b c : Index) : ℝ :=
  ∑ a, raiseSecond gInv k b a * k a c

/-- The real bilinear physical form. A future Hermitian extension is separate. -/
def physicalPairing (gInv k l : Tensor2) : ℝ :=
  tensorPairing gInv k l - metricTrace gInv k * metricTrace gInv l / 2

end Burnett.RicciSymbol
