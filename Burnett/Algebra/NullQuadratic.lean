import Burnett.Algebra.QuadraticExpansion
import Burnett.Algebra.NullKernel

noncomputable section

namespace Burnett.RicciSymbol

/-- Integrate the two parallel branches to obtain the real diagonal null formula
in paper/burnett.tex, equations (B-null), lines 454--457. -/
theorem quadraticSymbol_eq_physicalPairing_of_null_kernel
    (gInv : Tensor2) (ξ : Covector) (k : Tensor2)
    (hgSymm : IsSymmetricTensor gInv) (hkSymm : IsSymmetricTensor k)
    (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0) (b c : Index) :
    quadraticSymbol gInv ξ k b c =
      ξ b * ξ c * physicalPairing gInv k k / 4 := by
  have hq := (null_kernel_iff_contracted gInv ξ k hξ hs).mp hk
  have hB := four_quadraticSymbol_expansion gInv ξ k hgSymm hkSymm b c
  simp only [hs, zero_mul, mul_zero, sub_zero, hq] at hB
  unfold physicalPairing
  nlinarith [hB]

end Burnett.RicciSymbol
