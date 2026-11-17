import Burnett.Algebra.MinkowskiNull
import Burnett.Analysis.Cubic.Explicit

noncomputable section
namespace Burnett.RotatingNullMoments
open Burnett.RicciSymbol
open scoped BigOperators ContDiff

/-- Euclidean square length of the four covector components. -/
def euclideanSquare (ξ : Covector) : ℝ := ∑ i, (ξ i)^2

/-- An odd degree-one angular extension, smooth on every nonzero covector. -/
def oddAngular (ξ : Covector) : ℝ := -2 * ξ 0 * ξ 1 * ξ 2 / euclideanSquare ξ

theorem euclideanSquare_nonneg (ξ : Covector) : 0 ≤ euclideanSquare ξ :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (ξ i))

theorem euclideanSquare_pos (ξ : Covector) (hξ : ξ ≠ 0) : 0 < euclideanSquare ξ := by
  by_contra h
  have hs : euclideanSquare ξ = 0 := le_antisymm (le_of_not_gt h) (euclideanSquare_nonneg ξ)
  have hi : ∀ i ∈ Finset.univ, (ξ i)^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ξ i))).mp hs
  apply hξ
  funext i
  exact (sq_eq_zero_iff).mp (hi i (Finset.mem_univ i))

theorem euclideanSquare_smul (r : ℝ) (ξ : Covector) :
    euclideanSquare (r • ξ) = r^2 * euclideanSquare ξ := by
  simp only [euclideanSquare, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem euclideanSquare_neg (ξ : Covector) : euclideanSquare (-ξ) = euclideanSquare ξ := by
  simp [euclideanSquare]

theorem oddAngular_neg (ξ : Covector) : oddAngular (-ξ) = -oddAngular ξ := by
  unfold oddAngular
  rw [euclideanSquare_neg]
  simp only [Pi.neg_apply]
  ring

theorem oddAngular_homogeneous (r : ℝ) (ξ : Covector) :
    oddAngular (r • ξ) = r * oddAngular ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ, oddAngular, euclideanSquare]
  by_cases hr : r = 0
  · simp [hr, oddAngular, euclideanSquare]
  have hs : euclideanSquare ξ ≠ 0 := ne_of_gt (euclideanSquare_pos ξ hξ)
  unfold oddAngular
  rw [euclideanSquare_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hr, hs]

theorem oddAngular_smooth :
    ContDiffOn ℝ ∞ oddAngular {ξ : Covector | ξ ≠ 0} := by
  have hc (i : Index) : ContDiff ℝ ∞ (fun ξ : Covector => ξ i) := contDiff_apply ℝ ℝ i
  have hn : ContDiff ℝ ∞ (fun ξ : Covector => -2 * ξ 0 * ξ 1 * ξ 2) :=
    ((contDiff_const.mul (hc 0)).mul (hc 1)).mul (hc 2)
  have hd : ContDiff ℝ ∞ euclideanSquare :=
    ContDiff.sum (fun i _ => (hc i).pow 2)
  exact hn.contDiffOn.div hd.contDiffOn (fun ξ hξ => ne_of_gt (euclideanSquare_pos ξ hξ))

theorem euclideanSquare_on_null (ξ : Covector)
    (hn : symbolNorm NullScreen.minkowskiInverse ξ = 0) :
    euclideanSquare ξ = 2 * (ξ 0)^2 := by
  rw [MinkowskiNull.symbolNorm_eq_coordinates] at hn
  simp [euclideanSquare, Fin.sum_univ_succ, Fin.isValue]
  nlinarith

theorem oddAngular_on_nonzero_null (ξ : Covector) (hξ : ξ ≠ 0)
    (hn : symbolNorm NullScreen.minkowskiInverse ξ = 0) :
    oddAngular ξ = ξ 1 * ξ 2 / (-ξ 0) := by
  have h0 := MinkowskiNull.temporal_component_ne_zero ξ hξ hn
  unfold oddAngular
  rw [euclideanSquare_on_null ξ hn]
  field_simp [h0]

end Burnett.RotatingNullMoments

namespace Burnett.RotatingNullMoments
open Burnett.RicciSymbol
open scoped BigOperators ContDiff

theorem null_component_abs_le_time (ξ : Covector)
    (hn : symbolNorm NullScreen.minkowskiInverse ξ = 0) (i : Index) :
    |ξ i| ≤ |ξ 0| := by
  apply sq_le_sq.mp
  rw [MinkowskiNull.symbolNorm_eq_coordinates] at hn
  fin_cases i
  · exact le_rfl
  · change (ξ 1)^2 ≤ (ξ 0)^2
    nlinarith [sq_nonneg (ξ 2), sq_nonneg (ξ 3)]
  · change (ξ 2)^2 ≤ (ξ 0)^2
    nlinarith [sq_nonneg (ξ 1), sq_nonneg (ξ 3)]
  · change (ξ 3)^2 ≤ (ξ 0)^2
    nlinarith [sq_nonneg (ξ 1), sq_nonneg (ξ 2)]

theorem time_mul_oddAngular_on_null (ξ : Covector) (hξ : ξ ≠ 0)
    (hn : symbolNorm NullScreen.minkowskiInverse ξ = 0) :
    (-ξ 0) * oddAngular ξ = ξ 1 * ξ 2 := by
  rw [oddAngular_on_nonzero_null ξ hξ hn]
  have h0 := MinkowskiNull.temporal_component_ne_zero ξ hξ hn
  field_simp [h0]

theorem component_mul_oddAngular_abs_le (ξ : Covector) (hξ : ξ ≠ 0)
    (hn : symbolNorm NullScreen.minkowskiInverse ξ = 0) (i : Index) :
    |ξ i * oddAngular ξ| ≤ (ξ 0)^2 := by
  rw [oddAngular_on_nonzero_null ξ hξ hn]
  simp only [abs_mul, abs_div, abs_neg]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (abs_pos.mpr (MinkowskiNull.temporal_component_ne_zero ξ hξ hn))).mpr
  calc
    _ ≤ |ξ 0| * (|ξ 0| * |ξ 0|) := mul_le_mul
      (null_component_abs_le_time ξ hn i)
      (mul_le_mul (null_component_abs_le_time ξ hn 1) (null_component_abs_le_time ξ hn 2)
        (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
    _ = (ξ 0)^2 * |ξ 0| := by rw [← sq_abs (ξ 0)]; ring

/-- The true base Frechet derivative in the flat Minkowski Hamilton field.
The vertical metric-derivative term is zero for this constant metric. -/
def flatHamilton (a : Burnett.CubicExplicit.Space → Covector → ℝ)
    (x : Burnett.CubicExplicit.Space) (ξ : Covector) : ℝ :=
  ∑ i, raiseCovector NullScreen.minkowskiInverse ξ i *
    fderiv ℝ (fun y => a y ξ) x (Burnett.CubicExplicit.basis i)

def separatedTest (φ : Burnett.CubicExplicit.Space → ℝ)
    (x : Burnett.CubicExplicit.Space) (ξ : Covector) : ℝ := φ x * oddAngular ξ

theorem separatedTest_homogeneous (φ : Burnett.CubicExplicit.Space → ℝ)
    (x : Burnett.CubicExplicit.Space) (r : ℝ) (ξ : Covector) :
    separatedTest φ x (r • ξ) = r * separatedTest φ x ξ := by
  unfold separatedTest
  rw [oddAngular_homogeneous]
  ring

theorem separatedTest_smooth (φ : Burnett.CubicExplicit.Space → ℝ)
    (hφ : ContDiff ℝ ∞ φ) :
    ContDiffOn ℝ ∞ (fun p : Burnett.CubicExplicit.Space × Covector => separatedTest φ p.1 p.2)
      {p | p.2 ≠ 0} := by
  exact (hφ.comp contDiff_fst).contDiffOn.mul
    (oddAngular_smooth.comp contDiffOn_snd (fun _ hx => hx))

theorem separatedTest_zero_outside_base_support (φ : Burnett.CubicExplicit.Space → ℝ)
    (x : Burnett.CubicExplicit.Space) (hx : x ∉ tsupport φ) (ξ : Covector) :
    separatedTest φ x ξ = 0 := by
  rw [separatedTest, image_eq_zero_of_notMem_tsupport hx, zero_mul]

theorem flatHamilton_separated (φ : Burnett.CubicExplicit.Space → ℝ)
    (hf : Differentiable ℝ φ) (x : Burnett.CubicExplicit.Space) (ξ : Covector) :
    flatHamilton (separatedTest φ) x ξ = oddAngular ξ *
      ∑ i, raiseCovector NullScreen.minkowskiInverse ξ i * Burnett.CubicExplicit.D i φ x := by
  unfold flatHamilton separatedTest Burnett.CubicExplicit.D
  rw [fderiv_mul_const (hf x)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem flatHamilton_separated_coordinates (φ : Burnett.CubicExplicit.Space → ℝ)
    (hf : Differentiable ℝ φ) (x : Burnett.CubicExplicit.Space) (ξ : Covector) :
    flatHamilton (separatedTest φ) x ξ = oddAngular ξ *
      (-ξ 0 * Burnett.CubicExplicit.D 0 φ x + ξ 1 * Burnett.CubicExplicit.D 1 φ x +
        ξ 2 * Burnett.CubicExplicit.D 2 φ x + ξ 3 * Burnett.CubicExplicit.D 3 φ x) := by
  rw [flatHamilton_separated φ hf]
  congr 1
  simp [raiseCovector, NullScreen.minkowskiInverse, Fin.sum_univ_succ]
  ring

theorem flatHamilton_separated_null (φ : Burnett.CubicExplicit.Space → ℝ)
    (hf : Differentiable ℝ φ) (x : Burnett.CubicExplicit.Space) (ξ : Covector)
    (hξ : ξ ≠ 0) (hn : symbolNorm NullScreen.minkowskiInverse ξ = 0) :
    flatHamilton (separatedTest φ) x ξ =
      ξ 1 * ξ 2 * Burnett.CubicExplicit.D 0 φ x +
      ∑ j : Fin 3, ξ j.succ * oddAngular ξ * Burnett.CubicExplicit.D j.succ φ x := by
  rw [flatHamilton_separated_coordinates φ hf]
  have h := time_mul_oddAngular_on_null ξ hξ hn
  simp [Fin.sum_univ_succ]
  nlinarith only [congrArg (fun z : ℝ => z * Burnett.CubicExplicit.D 0 φ x) h]

/-- Direct bound for the spatial error, controlled by the 00 moment density. -/
theorem flatHamilton_spatial_error_bound (φ : Burnett.CubicExplicit.Space → ℝ)
    (hf : Differentiable ℝ φ) (x : Burnett.CubicExplicit.Space) (ξ : Covector)
    (hξ : ξ ≠ 0) (hn : symbolNorm NullScreen.minkowskiInverse ξ = 0) :
    |flatHamilton (separatedTest φ) x ξ - ξ 1 * ξ 2 * Burnett.CubicExplicit.D 0 φ x| ≤
      (ξ 0)^2 * ∑ j : Fin 3, |Burnett.CubicExplicit.D j.succ φ x| := by
  rw [flatHamilton_separated_null φ hf x ξ hξ hn]
  simp only [add_sub_cancel_left, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (component_mul_oddAngular_abs_le ξ hξ hn j.succ) (abs_nonneg _)

theorem flatHamilton_separated_antipodal (φ : Burnett.CubicExplicit.Space → ℝ)
    (hf : Differentiable ℝ φ) (x : Burnett.CubicExplicit.Space) (ξ : Covector) :
    flatHamilton (separatedTest φ) x (-ξ) = flatHamilton (separatedTest φ) x ξ := by
  rw [flatHamilton_separated_coordinates φ hf, flatHamilton_separated_coordinates φ hf,
    oddAngular_neg]
  simp only [Pi.neg_apply]
  ring

end Burnett.RotatingNullMoments
