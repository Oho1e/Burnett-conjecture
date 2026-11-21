import Burnett.Analysis.Fourier.Projection

set_option autoImplicit false
noncomputable section

namespace Burnett.Microlocal.SeparablePositive

open MeasureTheory Burnett.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def productSymbol (a b : BoundedSymbol V) : BoundedSymbol V where
  toFun x := a x * b x
  measurable := a.measurable.mul b.measurable
  bound := a.bound * b.bound
  bound_nonneg := mul_nonneg a.bound_nonneg b.bound_nonneg
  norm_le x := by
    rw [norm_mul]
    exact mul_le_mul (a.norm_le x) (b.norm_le x) (norm_nonneg _) a.bound_nonneg

@[simp] theorem productSymbol_apply (a b : BoundedSymbol V) (x : V) :
    productSymbol a b x = a x * b x := rfl

end Burnett.Microlocal.SeparablePositive
