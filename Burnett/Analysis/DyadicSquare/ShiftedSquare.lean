import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Burnett.Analysis.DyadicSquare.SquareEnergy

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.DyadicSquare
open MeasureTheory Burnett.Fourier Metric
open scoped RealInnerProductSpace BigOperators

private def linearWindow : ContDiffBump (0:Space) := ⟨1,2,by norm_num,by norm_num⟩

/-- A smooth annular symbol, including the Fourier-series modulation parameter. -/
def shiftedAnnulus (q : Space) : BoundedSymbol Space where
  toFun := fun ξ => ((linearWindow ξ - linearWindow ((2:ℝ) • ξ) : ℝ) : ℂ) *
    Complex.exp ((↑(2*Real.pi*(inner ℝ q ξ)) : ℂ)*Complex.I)
  measurable := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (linearWindow.continuous.sub (linearWindow.continuous.comp (continuous_const.smul continuous_id)))
    · fun_prop
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by
    intro ξ
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have he : ‖Complex.exp ((↑(2*Real.pi*(inner ℝ q ξ)) : ℂ)*Complex.I)‖ = 1 := by simp [Complex.norm_exp]
    rw [he,mul_one]
    apply abs_le.mpr
    constructor <;> linarith [linearWindow.nonneg (x := ξ),linearWindow.nonneg (x := (2:ℝ) • ξ),
      linearWindow.le_one (x := ξ),linearWindow.le_one (x := (2:ℝ) • ξ)]

private theorem shifted_support (q ξ : Space) (hn : shiftedAnnulus q ξ ≠ 0) :
    1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2 := by
  have h2 : ‖(2:ℝ) • ξ‖ = 2*‖ξ‖ := by rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hone (z : Space) (hz : ‖z‖ ≤ 1) : linearWindow z = 1 :=
    linearWindow.one_of_mem_closedBall (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hzero (z : Space) (hz : 2 ≤ ‖z‖) : linearWindow z = 0 :=
    linearWindow.zero_of_le_dist (by simpa only [dist_zero_right] using hz)
  constructor
  · by_contra! h
    exact hn (by simp [shiftedAnnulus,hone ξ (by linarith),hone ((2:ℝ) • ξ) (by linarith)])
  · by_contra! h
    exact hn (by simp [shiftedAnnulus,hzero ξ h,hzero ((2:ℝ) • ξ) (by linarith)])

/-- The actual four-dimensional square estimate is uniform in the modulation
vector, all finite sets of dyadic scales and the common initial scale. -/
theorem shifted_annular_square_L2 (q : Space) (t : ℝ) (ht : 0<t) (I : Finset ℕ) (u : ComplexL2 Space) :
    (∑ k ∈ I, ‖fourierMultiplier (rescaleSymbol (shiftedAnnulus q) ((2:ℝ)^k*t) (mul_pos (by positivity) ht)) u‖^2)
      ≤ 2*‖u‖^2 := by
  simpa only [shiftedAnnulus,one_pow,mul_one] using
    annular_square_L2 (shiftedAnnulus q) (shifted_support q) t ht I u

end Burnett.Analysis.DyadicSquare
