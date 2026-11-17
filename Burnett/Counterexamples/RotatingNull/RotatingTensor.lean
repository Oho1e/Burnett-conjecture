import Burnett.Algebra.MinkowskiNull
import Burnett.Analysis.Cubic.Explicit

noncomputable section
namespace Burnett.RotatingNullMoments
open Burnett.RicciSymbol
open scoped BigOperators ContDiff

/-- The spatial rotating unit vector, with a zero time component. -/
def direction (t : ℝ) : Covector :=
  fun a => if a = 1 then Real.cos t else if a = 2 then Real.sin t else 0

/-- The two unnormalized future null covectors (-1, sign v). -/
def ray (sign t : ℝ) : Covector :=
  fun a => if a = 0 then -1 else sign * direction t a

/-- The same tensor as in the paper, written as a sum of two null squares. -/
def tensor (c t : ℝ) : Tensor2 :=
  fun a b => c * (ray 1 t a * ray 1 t b + ray (-1) t a * ray (-1) t b)

theorem direction_unit (t : ℝ) : ∑ a, (direction t a)^2 = 1 := by
  simp [direction, Fin.sum_univ_succ, Real.cos_sq_add_sin_sq]

theorem ray_null (sign t : ℝ) (hs : sign^2 = 1) :
    symbolNorm NullScreen.minkowskiInverse (ray sign t) = 0 := by
  rw [MinkowskiNull.symbolNorm_eq_coordinates]
  simp [ray, direction, mul_pow, hs]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem ray_ne_zero (sign t : ℝ) : ray sign t ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [ray] at h0

theorem tensor_components (c t : ℝ) (a b : Index) :
    tensor c t a b = if a = 0 ∧ b = 0 then 2*c
      else if a = 0 ∨ b = 0 then 0 else 2*c * direction t a * direction t b := by
  fin_cases a <;> fin_cases b <;> simp [tensor, ray, direction, Fin.isValue] <;> ring

theorem tensor_symmetric (c t : ℝ) : ∀ a b, tensor c t a b = tensor c t b a := by
  intro a b
  unfold tensor
  ring

theorem tensor_trace_free (c t : ℝ) : metricTrace NullScreen.minkowskiInverse (tensor c t) = 0 := by
  simp [metricTrace, NullScreen.minkowskiInverse, tensor_components, direction, Fin.sum_univ_succ]
  have ht := congrArg (fun z : ℝ => 2*c*z) (Real.sin_sq_add_cos_sq t)
  nlinarith only [ht]

theorem tensor_quadratic (c t : ℝ) (u : Covector) :
    (∑ a, ∑ b, tensor c t a b * u a * u b) =
      c * ((∑ a, ray 1 t a * u a)^2 + (∑ a, ray (-1) t a * u a)^2) := by
  simp [tensor, Fin.sum_univ_succ]
  ring

theorem tensor_positive_semidefinite (c t : ℝ) (hc : 0 ≤ c) (u : Covector) :
    0 ≤ ∑ a, ∑ b, tensor c t a b * u a * u b := by
  rw [tensor_quadratic]
  exact mul_nonneg hc (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem direction_component_smooth (a : Index) :
    ContDiff ℝ ∞ (fun t => direction t a) := by
  unfold direction
  split_ifs <;> fun_prop

theorem ray_component_smooth (sign : ℝ) (a : Index) :
    ContDiff ℝ ∞ (fun t => ray sign t a) := by
  unfold ray
  split_ifs
  · exact contDiff_const
  · exact contDiff_const.mul (direction_component_smooth a)

theorem tensor_component_smooth (c : ℝ) (a b : Index) :
    ContDiff ℝ ∞ (fun t => tensor c t a b) :=
  contDiff_const.mul (((ray_component_smooth 1 a).mul (ray_component_smooth 1 b)).add
    ((ray_component_smooth (-1) a).mul (ray_component_smooth (-1) b)))

/-- Smoothness of the actual tensor field on the four-dimensional base. -/
theorem tensor_spacetime_smooth (c : ℝ) :
    ContDiff ℝ ∞ (fun x : Burnett.CubicExplicit.Space => tensor c (x 0)) := by
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  exact (tensor_component_smooth c a b).comp (Burnett.CubicExplicit.coord 0).contDiff

/-- The physical spacetime divergence with the Minkowski (-+++) contraction. -/
def divergence (c : ℝ) (x : Burnett.CubicExplicit.Space) (b : Index) : ℝ :=
  -Burnett.CubicExplicit.D 0 (fun y => tensor c (y 0) 0 b) x +
   Burnett.CubicExplicit.D 1 (fun y => tensor c (y 0) 1 b) x +
   Burnett.CubicExplicit.D 2 (fun y => tensor c (y 0) 2 b) x +
   Burnett.CubicExplicit.D 3 (fun y => tensor c (y 0) 3 b) x

theorem spatial_D_timeOnly (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (i : Index) (hi : i ≠ 0) (x : Burnett.CubicExplicit.Space) :
    Burnett.CubicExplicit.D i (fun y => f (y 0)) x = 0 := by
  unfold Burnett.CubicExplicit.D
  have h := fderiv_comp x (hf (x 0)) (Burnett.CubicExplicit.coord 0).differentiableAt
  rw [show (fun y : Burnett.CubicExplicit.Space => f (y 0)) =
    f ∘ Burnett.CubicExplicit.coord 0 from rfl, h]
  simp [Burnett.CubicExplicit.basis, Burnett.CubicExplicit.coord, EuclideanSpace.single_apply,
    ContinuousLinearMap.comp_apply, Ne.symm hi]

theorem tensor_divergence_free (c : ℝ) (x : Burnett.CubicExplicit.Space) (b : Index) :
    divergence c x b = 0 := by
  unfold divergence
  rw [spatial_D_timeOnly _ ((tensor_component_smooth c 1 b).differentiable (by simp)) 1 (by decide),
    spatial_D_timeOnly _ ((tensor_component_smooth c 2 b).differentiable (by simp)) 2 (by decide),
    spatial_D_timeOnly _ ((tensor_component_smooth c 3 b).differentiable (by simp)) 3 (by decide)]
  have h0 : (fun y : Burnett.CubicExplicit.Space => tensor c (y 0) 0 b) =
      (fun _ => if b = 0 then 2*c else 0) := by
    funext y
    simp [tensor_components]
  rw [h0]
  simp [Burnett.CubicExplicit.D]

/-- The two zero perpendicular square tests that positivity must force a.e. -/
def perpendicular (t : ℝ) (ξ : Covector) : ℝ :=
  -Real.sin t * ξ 1 + Real.cos t * ξ 2

def parallelComponent (t : ℝ) (ξ : Covector) : ℝ :=
  Real.cos t * ξ 1 + Real.sin t * ξ 2

theorem perpendicular_decomposition (t : ℝ) (ξ : Covector) :
    ξ 1 = Real.cos t * parallelComponent t ξ - Real.sin t * perpendicular t ξ ∧
    ξ 2 = Real.sin t * parallelComponent t ξ + Real.cos t * perpendicular t ξ := by
  have h := Real.sin_sq_add_cos_sq t
  constructor
  · have h1 := congrArg (fun z : ℝ => z * ξ 1) h
    dsimp [parallelComponent, perpendicular]
    nlinarith only [h1]
  · have h2 := congrArg (fun z : ℝ => z * ξ 2) h
    dsimp [parallelComponent, perpendicular]
    nlinarith only [h2]

theorem parallel_perpendicular_square (t : ℝ) (ξ : Covector) :
    (parallelComponent t ξ)^2 + (perpendicular t ξ)^2 = (ξ 1)^2 + (ξ 2)^2 := by
  calc
    _ = (Real.sin t ^ 2 + Real.cos t ^ 2) * ((ξ 1)^2 + (ξ 2)^2) := by
      dsimp [parallelComponent, perpendicular]
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

/-- Pure pointwise support classification; measure-a.e. forcing is a separate obligation. -/
theorem null_perpendicular_eq_ray (t : ℝ) (ξ : Covector)
    (hn : symbolNorm NullScreen.minkowskiInverse ξ = 0)
    (hp : perpendicular t ξ = 0) (hz : ξ 3 = 0) :
    ξ = (-ξ 0) • ray 1 t ∨ ξ = (-ξ 0) • ray (-1) t := by
  have hd := perpendicular_decomposition t ξ
  have hsq := parallel_perpendicular_square t ξ
  rw [MinkowskiNull.symbolNorm_eq_coordinates] at hn
  have hs : (parallelComponent t ξ)^2 = (ξ 0)^2 := by nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
  · right
    rw [hp, h] at hd
    simp only [mul_zero, sub_zero, add_zero] at hd
    funext i
    fin_cases i <;> simp [ray, direction, Pi.smul_apply, smul_eq_mul]
    · nlinarith [hd.1]
    · nlinarith [hd.2]
    · exact hz
  · left
    rw [hp, h] at hd
    simp only [mul_zero, sub_zero, add_zero] at hd
    funext i
    fin_cases i <;> simp [ray, direction, Pi.smul_apply, smul_eq_mul]
    · nlinarith [hd.1]
    · nlinarith [hd.2]
    · exact hz

end Burnett.RotatingNullMoments
