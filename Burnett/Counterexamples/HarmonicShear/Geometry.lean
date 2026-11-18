import Burnett.Geometry.FlatRigidity.WeakCurvature
import Burnett.Geometry.ConnectionDifference
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Burnett.Geometry.MetricJetNaturality
import Burnett.Geometry.TensorCoordinateChange
import Burnett.Geometry.SmoothMetricConnection
import Burnett.Geometry.CurvatureDifference

set_option autoImplicit false

noncomputable section

open scoped ContDiff Manifold BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference

namespace Burnett.HarmonicShear

def frequency (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)

def eps (n : ℕ) : ℝ := (frequency n)⁻¹

def delta (n : ℕ) : ℝ := ((frequency n)^3)⁻¹

theorem frequency_pos (n : ℕ) : 0 < frequency n := by
  unfold frequency
  positivity

theorem eps_pos (n : ℕ) : 0 < eps n := inv_pos.mpr (frequency_pos n)

theorem delta_pos (n : ℕ) : 0 < delta n := inv_pos.mpr (pow_pos (frequency_pos n) 3)

def firstShear (n : ℕ) (a : ℝ) : ℝ := (eps n)^2 * Real.sin (a / eps n)

def secondShear (n : ℕ) (a : ℝ) : ℝ := (delta n)^2 * Real.sin (a / delta n)

theorem contDiff_firstShear (n : ℕ) : ContDiff ℝ ∞ (firstShear n) := by
  unfold firstShear
  fun_prop

theorem contDiff_secondShear (n : ℕ) : ContDiff ℝ ∞ (secondShear n) := by
  unfold secondShear
  fun_prop

def p (x : CoordinateSpace) : ℝ := x 0 - x 3

def q (x : CoordinateSpace) : ℝ := x 0 - x 1

def phase (f : ℝ → ℝ) (x : CoordinateSpace) : ℝ := q x + f (p x)

def s (n : ℕ) : CoordinateSpace → ℝ := phase (firstShear n)

def source (n : ℕ) (x : CoordinateSpace) : ℝ :=
  (2 * eps n / delta n) * Real.cos (p x / eps n) * Real.cos (s n x / delta n)

def point (a b c d : ℝ) : CoordinateSpace := WithLp.toLp 2 ![a,b,c,d]

@[simp] theorem point_zero (a b c d : ℝ) : point a b c d 0 = a := rfl

@[simp] theorem point_one (a b c d : ℝ) : point a b c d 1 = b := rfl

@[simp] theorem point_two (a b c d : ℝ) : point a b c d 2 = c := rfl

@[simp] theorem point_three (a b c d : ℝ) : point a b c d 3 = d := rfl

/-- The global harmonic coordinate map \(y\mapsto x\). -/
def forward (f j : ℝ → ℝ) (y : CoordinateSpace) : CoordinateSpace :=
  point (y 0) (y 1 + f (p y)) (y 2 + j (q y)) (y 3)

/-- The global inverse coordinate map \(x\mapsto y\). -/
def inverse (f j : ℝ → ℝ) (x : CoordinateSpace) : CoordinateSpace :=
  point (x 0) (x 1 - f (p x)) (x 2 - j (phase f x)) (x 3)

theorem inverse_forward (f j : ℝ → ℝ) (y : CoordinateSpace) : inverse f j (forward f j y) = y := by
  have hp : p (forward f j y) = p y := by simp [p, forward]
  have hphase : phase f (forward f j y) = q y := by
    simp only [phase, q, forward, point_zero, point_one, p, point_three]
    ring
  ext i
  fin_cases i
  · rfl
  · change y 1 + f (p y) - f (p (forward f j y)) = y 1
    rw [hp, add_sub_cancel_right]
  · change y 2 + j (q y) - j (phase f (forward f j y)) = y 2
    rw [hphase, add_sub_cancel_right]
  · rfl

theorem forward_inverse (f j : ℝ → ℝ) (x : CoordinateSpace) : forward f j (inverse f j x) = x := by
  have hp : p (inverse f j x) = p x := by simp [p, inverse]
  have hq : q (inverse f j x) = phase f x := by
    simp only [phase, q, inverse, point_zero, point_one]
    ring
  ext i
  fin_cases i
  · rfl
  · change x 1 - f (p x) + f (p (inverse f j x)) = x 1
    rw [hp, sub_add_cancel]
  · change x 2 - j (phase f x) + j (q (inverse f j x)) = x 2
    rw [hq, sub_add_cancel]
  · rfl

theorem contDiff_coordinate (a : Index) : ContDiff ℝ ∞ (fun x : CoordinateSpace => x a) := by
  change ContDiff ℝ ∞ (EuclideanSpace.proj (𝕜 := ℝ) a)
  exact (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff

theorem contDiff_p : ContDiff ℝ ∞ p := (contDiff_coordinate 0).sub (contDiff_coordinate 3)

theorem contDiff_q : ContDiff ℝ ∞ q := (contDiff_coordinate 0).sub (contDiff_coordinate 1)

theorem contDiff_phase {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (phase f) :=
  contDiff_q.add (hf.comp contDiff_p)

theorem contDiff_forward {f j : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j) :
    ContDiff ℝ ∞ (forward f j) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_coordinate 0
  · exact (contDiff_coordinate 1).add (hf.comp contDiff_p)
  · exact (contDiff_coordinate 2).add (hj.comp contDiff_q)
  · exact contDiff_coordinate 3

theorem contDiff_inverse {f j : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j) :
    ContDiff ℝ ∞ (inverse f j) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_coordinate 0
  · exact (contDiff_coordinate 1).sub (hf.comp contDiff_p)
  · exact (contDiff_coordinate 2).sub (hj.comp (contDiff_phase hf))
  · exact contDiff_coordinate 3

def diffeomorph (f j : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j) :
    Diffeomorph 𝓘(ℝ, CoordinateSpace) 𝓘(ℝ, CoordinateSpace) CoordinateSpace CoordinateSpace ∞ where
  toEquiv := ⟨forward f j, inverse f j, inverse_forward f j, forward_inverse f j⟩
  contMDiff_toFun := (contDiff_forward hf hj).contMDiff
  contMDiff_invFun := (contDiff_inverse hf hj).contMDiff

def minkowskiPair (u v : CoordinateSpace) : ℝ :=
  -(u 0 * v 0) + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

def minkowski : LinearMap.BilinForm ℝ CoordinateSpace :=
  LinearMap.mk₂ ℝ minkowskiPair
    (by intros; simp only [minkowskiPair, PiLp.add_apply]; ring)
    (by intros; simp only [minkowskiPair, PiLp.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [minkowskiPair, PiLp.add_apply]; ring)
    (by intros; simp only [minkowskiPair, PiLp.smul_apply, smul_eq_mul]; ring)

/-- The genuine pullback of the constant Minkowski form by the inverse shear. -/
def pullbackMetric (f j : ℝ → ℝ) (x : CoordinateSpace) : LinearMap.BilinForm ℝ CoordinateSpace :=
  minkowski.comp (fderiv ℝ (inverse f j) x).toLinearMap (fderiv ℝ (inverse f j) x).toLinearMap

def metric (n : ℕ) : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace :=
  pullbackMetric (firstShear n) (secondShear n)

def perturbation (n : ℕ) (x : CoordinateSpace) : Tensor2 :=
  metricComponents (metric n) x - metricComponents (fun _ => minkowski) x

end Burnett.HarmonicShear

namespace Burnett.HarmonicShear

def coordPartial (a : Index) (h : CoordinateSpace → ℝ) (x : CoordinateSpace) : ℝ :=
  fderiv ℝ h x (EuclideanSpace.single a 1)

def sign (a : Index) : ℝ := if a = 0 then -1 else 1

/-- The trace of the actual coordinate Hessian for the inverse Minkowski metric. -/
def box (h : CoordinateSpace → ℝ) (x : CoordinateSpace) : ℝ :=
  ∑ a : Index, sign a * coordPartial a (coordPartial a h) x

def gradientSquare (h : CoordinateSpace → ℝ) (x : CoordinateSpace) : ℝ :=
  ∑ a : Index, sign a * (coordPartial a h x)^2

private theorem index_zero_ne_one : (0 : Index) ≠ 1 := by decide
private theorem index_zero_ne_two : (0 : Index) ≠ 2 := by decide
private theorem index_zero_ne_three : (0 : Index) ≠ 3 := by decide
private theorem index_one_ne_zero : (1 : Index) ≠ 0 := by decide
private theorem index_one_ne_two : (1 : Index) ≠ 2 := by decide
private theorem index_one_ne_three : (1 : Index) ≠ 3 := by decide
private theorem index_two_ne_zero : (2 : Index) ≠ 0 := by decide
private theorem index_two_ne_one : (2 : Index) ≠ 1 := by decide
private theorem index_two_ne_three : (2 : Index) ≠ 3 := by decide
private theorem index_three_ne_zero : (3 : Index) ≠ 0 := by decide
private theorem index_three_ne_one : (3 : Index) ≠ 1 := by decide
private theorem index_three_ne_two : (3 : Index) ≠ 2 := by decide

attribute [local simp]
  index_zero_ne_one
  index_zero_ne_two
  index_zero_ne_three
  index_one_ne_zero
  index_one_ne_two
  index_one_ne_three
  index_two_ne_zero
  index_two_ne_one
  index_two_ne_three
  index_three_ne_zero
  index_three_ne_one
  index_three_ne_two

private theorem contDiff_partial (a : Index) {h : CoordinateSpace → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (coordPartial a h) :=
  (hh.fderiv_right (by simp)).clm_apply contDiff_const

theorem coordPartial_coordinate (a i : Index) :
    coordPartial a (fun x : CoordinateSpace => x i) = fun _ => if a = i then 1 else 0 := by
  funext x
  change fderiv ℝ (EuclideanSpace.proj i) x (EuclideanSpace.single a 1) = _
  rw [ContinuousLinearMap.fderiv]
  simp [EuclideanSpace.single_apply, eq_comm]

theorem coordPartial_const (a : Index) (c : ℝ) : coordPartial a (fun _ => c) = 0 := by
  funext x
  simp [coordPartial]

theorem coordPartial_add (a : Index) {f h : CoordinateSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    coordPartial a (fun y => f y + h y) = fun y => coordPartial a f y + coordPartial a h y := by
  funext x
  simp only [coordPartial, fderiv_fun_add (hf.differentiable (by simp) x) (hh.differentiable (by simp) x),
    ContinuousLinearMap.add_apply]

theorem coordPartial_sub (a : Index) {f h : CoordinateSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    coordPartial a (fun y => f y - h y) = fun y => coordPartial a f y - coordPartial a h y := by
  funext x
  simp only [coordPartial, fderiv_fun_sub (hf.differentiable (by simp) x) (hh.differentiable (by simp) x),
    ContinuousLinearMap.sub_apply]

theorem coordPartial_comp (a : Index) {f : ℝ → ℝ} {h : CoordinateSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    coordPartial a (fun y => f (h y)) = fun y => deriv f (h y) * coordPartial a h y := by
  funext x
  have hd := ((hf.differentiable (by simp) (h x)).hasDerivAt).comp_hasFDerivAt x
    (hh.differentiable (by simp) x).hasFDerivAt
  change fderiv ℝ (f ∘ h) x (EuclideanSpace.single a 1) = _
  rw [hd.fderiv]
  rfl

theorem coordPartial_comp_twice (a : Index) {f : ℝ → ℝ} {h : CoordinateSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (x : CoordinateSpace) :
    coordPartial a (coordPartial a (fun y => f (h y))) x =
      deriv (deriv f) (h x) * (coordPartial a h x)^2 +
      deriv f (h x) * coordPartial a (coordPartial a h) x := by
  have hf' : ContDiff ℝ ∞ (deriv f) := ContDiff.deriv' (n := ∞) (by simpa using hf)
  have h1 : DifferentiableAt ℝ (fun y => deriv f (h y)) x :=
    (hf'.comp hh).differentiable (by simp) x
  have h2 : DifferentiableAt ℝ (coordPartial a h) x := (contDiff_partial a hh).differentiable (by simp) x
  rw [coordPartial_comp a hf hh]
  change fderiv ℝ (fun y => deriv f (h y) * coordPartial a h y) x (EuclideanSpace.single a 1) = _
  rw [fderiv_fun_mul h1 h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  change deriv f (h x) * coordPartial a (coordPartial a h) x +
      coordPartial a h x * coordPartial a (fun y => deriv f (h y)) x = _
  rw [coordPartial_comp a hf' hh]
  ring

theorem box_comp {f : ℝ → ℝ} {h : CoordinateSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (hh : ContDiff ℝ ∞ h) (x : CoordinateSpace) :
    box (fun y => f (h y)) x = deriv (deriv f) (h x) * gradientSquare h x + deriv f (h x) * box h x := by
  unfold box gradientSquare
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [coordPartial_comp_twice a hf hh]
  ring

theorem box_add {f h : CoordinateSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (x : CoordinateSpace) : box (fun y => f y + h y) x = box f x + box h x := by
  unfold box
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [coordPartial_add a hf hh, coordPartial_add a (contDiff_partial a hf) (contDiff_partial a hh)]
  ring

theorem box_coordinate (i : Index) (x : CoordinateSpace) :
    box (fun y : CoordinateSpace => y i) x = 0 := by
  simp only [box, coordPartial_coordinate, coordPartial_const, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem coordPartial_p (a : Index) :
    coordPartial a p = fun _ => (if a = 0 then 1 else 0) - (if a = 3 then 1 else 0) := by
  unfold p
  rw [coordPartial_sub a (contDiff_coordinate 0) (contDiff_coordinate 3), coordPartial_coordinate,
    coordPartial_coordinate]

theorem coordPartial_q (a : Index) :
    coordPartial a q = fun _ => (if a = 0 then 1 else 0) - (if a = 1 then 1 else 0) := by
  unfold q
  rw [coordPartial_sub a (contDiff_coordinate 0) (contDiff_coordinate 1), coordPartial_coordinate,
    coordPartial_coordinate]

theorem box_p (x : CoordinateSpace) : box p x = 0 := by
  simp only [box, coordPartial_p, coordPartial_const, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem box_q (x : CoordinateSpace) : box q x = 0 := by
  simp only [box, coordPartial_q, coordPartial_const, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem gradientSquare_p (x : CoordinateSpace) : gradientSquare p x = 0 := by
  norm_num [gradientSquare, sign, Fin.sum_univ_four, coordPartial_p]

theorem gradientSquare_q (x : CoordinateSpace) : gradientSquare q x = 0 := by
  norm_num [gradientSquare, sign, Fin.sum_univ_four, coordPartial_q]

theorem box_phase {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : CoordinateSpace) : box (phase f) x = 0 := by
  unfold phase
  have h : ContDiff ℝ ∞ (fun y => f (p y)) := hf.comp contDiff_p
  rw [box_add contDiff_q h, box_comp hf contDiff_p, box_q, box_p, gradientSquare_p]
  ring

theorem coordPartial_phase (a : Index) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    coordPartial a (phase f) = fun x =>
      coordPartial a q x + deriv f (p x) * coordPartial a p x := by
  unfold phase
  have h : ContDiff ℝ ∞ (fun y => f (p y)) := hf.comp contDiff_p
  rw [coordPartial_add a contDiff_q h, coordPartial_comp a hf contDiff_p]

theorem gradientSquare_phase {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : CoordinateSpace) :
    gradientSquare (phase f) x = -2 * deriv f (p x) := by
  norm_num [gradientSquare, sign, Fin.sum_univ_four, coordPartial_phase _ hf, coordPartial_q, coordPartial_p]
  ring

theorem forward_coordinate_harmonic {f j : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j) (x : CoordinateSpace) (a : Index) :
    box (fun y => forward f j y a) x = 0 := by
  fin_cases a
  · exact box_coordinate 0 x
  · change box (fun y => y 1 + f (p y)) x = 0
    have h : ContDiff ℝ ∞ (fun y => f (p y)) := hf.comp contDiff_p
    rw [box_add (contDiff_coordinate 1) h, box_coordinate, box_comp hf contDiff_p,
      box_p, gradientSquare_p]
    ring
  · change box (fun y => y 2 + j (q y)) x = 0
    have h : ContDiff ℝ ∞ (fun y => j (q y)) := hj.comp contDiff_q
    rw [box_add (contDiff_coordinate 2) h, box_coordinate, box_comp hj contDiff_q,
      box_q, gradientSquare_q]
    ring
  · exact box_coordinate 3 x

end Burnett.HarmonicShear

namespace Burnett.HarmonicShear

private theorem fderiv_coordinate_component {F : CoordinateSpace → CoordinateSpace} {x : CoordinateSpace}
    (hF : DifferentiableAt ℝ F x) (v : CoordinateSpace) (i : Index) :
    (fderiv ℝ F x v) i = fderiv ℝ (fun y => F y i) x v := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hF.hasFDerivAt
  exact congrArg (fun L : CoordinateSpace →L[ℝ] ℝ => L v) h.fderiv.symm

private theorem coordinateBasis_eq_single (i : Index) :
    coordinateBasis i = EuclideanSpace.single i 1 := EuclideanSpace.basisFun_apply _ _ i

theorem inverse_fderiv_on_basis {f j : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j)
    (x : CoordinateSpace) (a : Index) :
    fderiv ℝ (inverse f j) x (EuclideanSpace.single a 1) =
      point (if a = 0 then 1 else 0)
        ((if a = 1 then 1 else 0) - deriv f (p x) * coordPartial a p x)
        ((if a = 2 then 1 else 0) - deriv j (phase f x) * coordPartial a (phase f) x)
        (if a = 3 then 1 else 0) := by
  have hF : DifferentiableAt ℝ (inverse f j) x := (contDiff_inverse hf hj).differentiable (by simp) x
  have hf' : ContDiff ℝ ∞ (fun y => f (p y)) := hf.comp contDiff_p
  have hj' : ContDiff ℝ ∞ (fun y => j (phase f y)) := hj.comp (contDiff_phase hf)
  ext i
  rw [fderiv_coordinate_component hF]
  change coordPartial a (fun y => inverse f j y i) x = _
  fin_cases i
  · change coordPartial a (fun y : CoordinateSpace => y 0) x = _
    rw [coordPartial_coordinate]
    rfl
  · change coordPartial a (fun y => y 1 - f (p y)) x = _
    rw [coordPartial_sub a (contDiff_coordinate 1) hf', coordPartial_coordinate, coordPartial_comp a hf contDiff_p]
    rfl
  · change coordPartial a (fun y => y 2 - j (phase f y)) x = _
    rw [coordPartial_sub a (contDiff_coordinate 2) hj', coordPartial_coordinate,
      coordPartial_comp a hj (contDiff_phase hf)]
    rfl
  · change coordPartial a (fun y : CoordinateSpace => y 3) x = _
    rw [coordPartial_coordinate]
    rfl

theorem pullbackMetric_components {f j : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j)
    (x : CoordinateSpace) (a b : Index) :
    metricComponents (pullbackMetric f j) x a b =
      -(coordPartial a (fun y : CoordinateSpace => y 0) x *
          coordPartial b (fun y : CoordinateSpace => y 0) x) +
      (coordPartial a (fun y => y 1 - f (p y)) x *
          coordPartial b (fun y => y 1 - f (p y)) x) +
      (coordPartial a (fun y => y 2 - j (phase f y)) x *
          coordPartial b (fun y => y 2 - j (phase f y)) x) +
      coordPartial a (fun y : CoordinateSpace => y 3) x *
          coordPartial b (fun y : CoordinateSpace => y 3) x := by
  have hF : DifferentiableAt ℝ (inverse f j) x := (contDiff_inverse hf hj).differentiable (by simp) x
  simp only [metricComponents, Burnett.Geometry.FiberMetric.covariant, pullbackMetric,
    LinearMap.BilinForm.comp_apply, ContinuousLinearMap.coe_coe, minkowski, LinearMap.mk₂_apply,
    coordinateBasis_eq_single, minkowskiPair, fderiv_coordinate_component hF]
  rfl

theorem pullbackMetric_component_21 {f j : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j)
    (x : CoordinateSpace) : metricComponents (pullbackMetric f j) x 2 1 = deriv j (phase f x) := by
  rw [pullbackMetric_components hf hj]
  have hf' : ContDiff ℝ ∞ (fun y => f (p y)) := hf.comp contDiff_p
  have hj' : ContDiff ℝ ∞ (fun y => j (phase f y)) := hj.comp (contDiff_phase hf)
  simp only [coordPartial_sub _ (contDiff_coordinate 1) hf',
    coordPartial_sub _ (contDiff_coordinate 2) hj',
    coordPartial_coordinate, coordPartial_comp _ hf contDiff_p, coordPartial_comp _ hj (contDiff_phase hf),
    coordPartial_phase _ hf, coordPartial_p, coordPartial_q]
  norm_num [show (2 : Index) ≠ 0 by decide, show (2 : Index) ≠ 1 by decide,
    show (2 : Index) ≠ 3 by decide, show (1 : Index) ≠ 0 by decide, show (1 : Index) ≠ 2 by decide,
    show (1 : Index) ≠ 3 by decide]

theorem minkowski_component_21 (x : CoordinateSpace) :
    metricComponents (fun _ => minkowski) x 2 1 = 0 := by
  norm_num [metricComponents, Burnett.Geometry.FiberMetric.covariant, minkowski, LinearMap.mk₂_apply,
    coordinateBasis_eq_single, minkowskiPair, EuclideanSpace.single_apply,
    show (1 : Index) ≠ 2 by decide, show (2 : Index) ≠ 1 by decide,
    show (3 : Index) ≠ 1 by decide, show (3 : Index) ≠ 2 by decide]

theorem perturbation_21 (n : ℕ) (x : CoordinateSpace) :
    perturbation n x 2 1 = deriv (secondShear n) (s n x) := by
  simp only [perturbation, metric, Pi.sub_apply, s, pullbackMetric_component_21
    (contDiff_firstShear n) (contDiff_secondShear n), minkowski_component_21, sub_zero]

private theorem hasDerivAt_sin_div (k a : ℝ) :
    HasDerivAt (fun t => Real.sin (t / k)) (Real.cos (a / k) / k) a := by
  simpa only [Function.comp_def, id_eq, one_mul, one_div, div_eq_mul_inv] using
    (Real.hasDerivAt_sin (a / k)).comp a ((hasDerivAt_id a).div_const k)

private theorem hasDerivAt_cos_div (k a : ℝ) :
    HasDerivAt (fun t => Real.cos (t / k)) (-Real.sin (a / k) / k) a := by
  simpa only [Function.comp_def, id_eq, one_mul, one_div, div_eq_mul_inv] using
    (Real.hasDerivAt_cos (a / k)).comp a ((hasDerivAt_id a).div_const k)

private theorem deriv_shear (k : ℝ) (hk : k ≠ 0) (a : ℝ) :
    deriv (fun t => k^2 * Real.sin (t / k)) a = k * Real.cos (a / k) := by
  rw [((hasDerivAt_sin_div k a).const_mul (k^2)).deriv]
  field_simp

theorem deriv_firstShear (n : ℕ) (a : ℝ) :
    deriv (firstShear n) a = eps n * Real.cos (a / eps n) :=
  deriv_shear (eps n) (eps_pos n).ne' a

theorem deriv_secondShear (n : ℕ) (a : ℝ) :
    deriv (secondShear n) a = delta n * Real.cos (a / delta n) :=
  deriv_shear (delta n) (delta_pos n).ne' a

theorem deriv_secondShear_twice (n : ℕ) (a : ℝ) :
    deriv (deriv (secondShear n)) a = -Real.sin (a / delta n) := by
  rw [show deriv (secondShear n) = fun t => delta n * Real.cos (t / delta n) from funext (deriv_secondShear n)]
  rw [((hasDerivAt_cos_div (delta n) a).const_mul (delta n)).deriv]
  field_simp [(delta_pos n).ne']

theorem deriv_secondShear_thrice (n : ℕ) (a : ℝ) :
    deriv (deriv (deriv (secondShear n))) a = -Real.cos (a / delta n) / delta n := by
  rw [show deriv (deriv (secondShear n)) = fun t => -Real.sin (t / delta n) from
    funext (deriv_secondShear_twice n)]
  simpa only [Pi.neg_apply, neg_div] using (hasDerivAt_sin_div (delta n) a).neg.deriv

theorem box_perturbation_21 (n : ℕ) (x : CoordinateSpace) :
    box (fun y => perturbation n y 2 1) x = source n x := by
  rw [show (fun y => perturbation n y 2 1) = fun y => deriv (secondShear n) (s n y) from
    funext (perturbation_21 n)]
  have hj : ContDiff ℝ ∞ (deriv (secondShear n)) :=
    ContDiff.deriv' (n := ∞) (by simpa using contDiff_secondShear n)
  change box (fun y => deriv (secondShear n) (phase (firstShear n) y)) x = _
  rw [box_comp hj (contDiff_phase (contDiff_firstShear n))]
  change deriv (deriv (deriv (secondShear n))) (s n x) * gradientSquare (phase (firstShear n)) x +
    deriv (deriv (secondShear n)) (s n x) * box (phase (firstShear n)) x = _
  rw [box_phase (contDiff_firstShear n), gradientSquare_phase (contDiff_firstShear n),
    deriv_firstShear, deriv_secondShear_thrice]
  unfold source
  ring

end Burnett.HarmonicShear



namespace Burnett.HarmonicShear

open Matrix Set
open Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.ConnectionCoordinateChange
open Burnett.Geometry.ChartVolume (derivativeMatrix)
open Burnett.Geometry.MetricJetNaturality
open Burnett.Geometry.AffineConnection (fderiv_tensorForm directionalTensor)
open Burnett.Geometry.CoordinateCovariantDerivative (tensorForm tensorForm_apply)
open Burnett.Geometry.CurvatureDifference

def jac (F : CoordinateSpace → CoordinateSpace) (x : CoordinateSpace) : Matrix Index Index ℝ :=
  derivativeMatrix (fderiv ℝ F x)

def hess (F : CoordinateSpace → CoordinateSpace) (x : CoordinateSpace) : Connection :=
  fun a b c => ((fderiv ℝ (fderiv ℝ F) x (coordinateBasis b)) (coordinateBasis c)) a

def minkowskiMatrix : Matrix Index Index ℝ := Matrix.diagonal sign

theorem minkowskiMatrix_mul_self : minkowskiMatrix * minkowskiMatrix = 1 := by
  rw [minkowskiMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases h : a = 0 <;> simp [sign, h]

theorem isUnit_minkowskiMatrix : IsUnit minkowskiMatrix := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_of_mul_eq_one _ (Matrix.det minkowskiMatrix)
  rw [← Matrix.det_mul, minkowskiMatrix_mul_self, Matrix.det_one]

theorem minkowskiMatrix_inv : minkowskiMatrix⁻¹ = minkowskiMatrix := by
  have h := Matrix.nonsing_inv_mul minkowskiMatrix ((Matrix.isUnit_iff_isUnit_det _).mp isUnit_minkowskiMatrix)
  calc
    minkowskiMatrix⁻¹ = minkowskiMatrix⁻¹ * (minkowskiMatrix * minkowskiMatrix) := by
      rw [minkowskiMatrix_mul_self, Matrix.mul_one]
    _ = minkowskiMatrix := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]

theorem minkowskiMatrix_symm : IsSymmetricTensor minkowskiMatrix := by
  intro a b
  by_cases h : a = b
  · subst b
    rfl
  · simp [minkowskiMatrix, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem minkowski_tensorForm (u v : CoordinateSpace) : tensorForm minkowskiMatrix u v = minkowskiPair u v := by
  simp only [tensorForm_apply, minkowskiMatrix]
  have h (a : Index) : (∑ b, u a * (Matrix.diagonal sign) a b * v b) = u a * sign a * v a := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · exact fun ha => (ha (Finset.mem_univ a)).elim
  rw [Finset.sum_congr rfl (fun a _ => h a)]
  norm_num [minkowskiPair, Fin.sum_univ_four, sign, show (1 : Index) ≠ 0 by decide,
    show (2 : Index) ≠ 0 by decide, show (3 : Index) ≠ 0 by decide]

theorem jac_comp (F G : CoordinateSpace → CoordinateSpace) (x : CoordinateSpace)
    (hF : DifferentiableAt ℝ F (G x)) (hG : DifferentiableAt ℝ G x) :
    jac (F ∘ G) x = jac F (G x) * jac G x := by
  rw [jac, fderiv_comp x hF hG]
  exact LinearMap.toMatrix_comp _ _ _ _ _

theorem jac_id (x : CoordinateSpace) : jac (id : CoordinateSpace → CoordinateSpace) x = 1 := by
  simp [jac, fderiv_id, derivativeMatrix]

theorem jac_leftInverse (F G : CoordinateSpace → CoordinateSpace)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (h : Function.LeftInverse F G) (x : CoordinateSpace) :
    jac F (G x) * jac G x = 1 := by
  rw [← jac_comp F G x (hF.differentiable (by simp) (G x)) (hG.differentiable (by simp) x),
    show F ∘ G = id from funext h, jac_id]

theorem isUnit_jac_of_leftInverse (F G : CoordinateSpace → CoordinateSpace)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (h : Function.LeftInverse F G) (x : CoordinateSpace) :
    IsUnit (jac G x) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_of_mul_eq_one _ (jac F (G x)).det
  rw [mul_comm, ← Matrix.det_mul, jac_leftInverse F G hF hG h, Matrix.det_one]

theorem hess_lower_symm {F : CoordinateSpace → CoordinateSpace} (hF : ContDiff ℝ ∞ F)
    (x : CoordinateSpace) (a b c : Index) : hess F x a b c = hess F x a c b := by
  have hs := (hF.contDiffAt (x := x)).isSymmSndFDerivAt (by
    norm_num
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  exact congrArg (fun z : CoordinateSpace => z a) (hs.eq (coordinateBasis b) (coordinateBasis c))

def metricPullback (F : CoordinateSpace → CoordinateSpace) (x : CoordinateSpace) :
    LinearMap.BilinForm ℝ CoordinateSpace :=
  minkowski.comp (fderiv ℝ F x).toLinearMap (fderiv ℝ F x).toLinearMap

theorem shear_eq_metricPullback (f j : ℝ → ℝ) :
    pullbackMetric f j = metricPullback (inverse f j) := rfl

theorem metricPullback_components (F : CoordinateSpace → CoordinateSpace) (x : CoordinateSpace) :
    (metricComponents (metricPullback F) x : Matrix Index Index ℝ) =
      (jac F x)ᵀ * minkowskiMatrix * jac F x := by
  ext a b
  rw [matrix_triple_entry]
  simp only [metricComponents, Burnett.Geometry.FiberMetric.covariant, metricPullback,
    LinearMap.BilinForm.comp_apply, ContinuousLinearMap.coe_coe, minkowski, LinearMap.mk₂_apply,
    ← minkowski_tensorForm, tensorForm_apply, jac,
    derivativeMatrix_apply]

theorem contDiff_jac_entry {F : CoordinateSpace → CoordinateSpace} (hF : ContDiff ℝ ∞ F)
    (a b : Index) : ContDiff ℝ ∞ (fun x => jac F x a b) := by
  simp only [jac, derivativeMatrix_apply]
  exact (contDiff_coordinate a).comp ((hF.fderiv_right (by simp)).clm_apply contDiff_const)

theorem metricPullback_jet {F : CoordinateSpace → CoordinateSpace} (hF : ContDiff ℝ ∞ F)
    (x : CoordinateSpace) :
    coordinateJet (metricComponents (metricPullback F)) x =
      transformedJet (jac F x) minkowskiMatrix 0 (hess F x) := by
  have hF' : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x := hF'.differentiable (by simp) x
  have hc (i : Index) : DifferentiableAt ℝ (fun x => fderiv ℝ F x (coordinateBasis i)) x :=
    hd.clm_apply (differentiableAt_const _)
  funext b i j
  have hfun : (fun y => metricComponents (metricPullback F) y i j) =
      (fun y => tensorForm minkowskiMatrix (fderiv ℝ F y (coordinateBasis i))
        (fderiv ℝ F y (coordinateBasis j))) := by
    funext y
    exact (minkowski_tensorForm _ _).symm
  unfold coordinateJet
  rw [hfun, ← coordinateBasis_eq_single, fderiv_tensorForm (fun _ => minkowskiMatrix) _ _ x
    (coordinateBasis b) (fun _ _ => differentiableAt_const _) (hc i) (hc j),
    fderiv_jacobian_column F x (coordinateBasis b) hd i,
    fderiv_jacobian_column F x (coordinateBasis b) hd j]
  simp only [transformedJet, transformedMetricDerivative, Pi.zero_apply, smul_zero, Finset.sum_const_zero,
    add_zero, Matrix.add_apply, matrix_triple_entry,
    tensorForm_apply, directionalTensor, fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_mul,
    mul_zero, Finset.sum_const_zero, connectionMatrix, hess, jac, derivativeMatrix_apply]

theorem metricPullback_connection {F G : CoordinateSpace → CoordinateSpace}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (h : Function.LeftInverse G F) (x : CoordinateSpace) :
    computedConnection (metricPullback F) x = transformedConnection (jac F x) 0 (hess F x) := by
  unfold computedConnection
  rw [metricPullback_components, metricPullback_jet hF]
  have ht := (transformed_christoffel (jac F x) minkowskiMatrix 0 (hess F x)
    (isUnit_jac_of_leftInverse G F hG hF h x) isUnit_minkowskiMatrix minkowskiMatrix_symm
    (fun _ _ _ => rfl) (hess_lower_symm hF x)).symm
  change christoffel (((jac F x)ᵀ * minkowskiMatrix * jac F x)⁻¹ : Matrix Index Index ℝ)
    (transformedJet (jac F x) minkowskiMatrix 0 (hess F x)) = _
  convert ht using 2
  ext a b c
  simp [christoffel, koszul]

end Burnett.HarmonicShear

namespace Burnett.HarmonicShear

open Matrix Set
open Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.InverseField (matrixInverse)
open Burnett.Geometry.ConnectionCoordinateChange
open Burnett.Geometry.MetricJetNaturality
open Burnett.Geometry.CoordinateCovariantDerivative (tensorForm tensorForm_apply)

theorem coordPartial_comp_jac {F : CoordinateSpace → CoordinateSpace} {f : CoordinateSpace → ℝ}
    (hF : ContDiff ℝ ∞ F) (hf : ContDiff ℝ ∞ f) (x : CoordinateSpace) (b : Index) :
    coordPartial b (f ∘ F) x = ∑ a, jac F x a b * coordPartial a f (F x) := by
  rw [coordPartial, fderiv_comp x (hf.differentiable (by simp) (F x))
    (hF.differentiable (by simp) x), ContinuousLinearMap.comp_apply, ← coordinateBasis_eq_single]
  have hv : fderiv ℝ F x (coordinateBasis b) = ∑ a, jac F x a b • coordinateBasis a := by
    simpa only [jac, derivativeMatrix_apply, coordinateBasis, EuclideanSpace.basisFun_repr] using
      (coordinateBasis.sum_repr (fderiv ℝ F x (coordinateBasis b))).symm
  rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul, coordPartial, coordinateBasis_eq_single]

def metricGradientSquare (G : Matrix Index Index ℝ) (f : CoordinateSpace → ℝ)
    (x : CoordinateSpace) : ℝ := ∑ b, ∑ c, G b c * coordPartial b f x * coordPartial c f x

theorem metricGradientSquare_minkowski (f : CoordinateSpace → ℝ) (x : CoordinateSpace) :
    metricGradientSquare minkowskiMatrix f x = gradientSquare f x := by
  unfold metricGradientSquare gradientSquare
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single b]
  · simp [minkowskiMatrix, pow_two, mul_assoc]
  · intro c _ hcb
    simp [minkowskiMatrix, Matrix.diagonal_apply_ne _ (Ne.symm hcb)]
  · exact fun hb => (hb (Finset.mem_univ b)).elim

theorem metricGradientSquare_pullback {F G : CoordinateSpace → CoordinateSpace}
    {f : CoordinateSpace → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (h : Function.LeftInverse G F) (hf : ContDiff ℝ ∞ f) (x : CoordinateSpace) :
    metricGradientSquare (matrixInverse (metricComponents (metricPullback F) x))
      (f ∘ F) x = gradientSquare f (F x) := by
  let A := jac F x
  let B := (Aᵀ * minkowskiMatrix * A)⁻¹
  have hAB : A * B * Aᵀ = minkowskiMatrix := by
    simpa only [Burnett.Geometry.TensorCoordinateChange.pullbackMetric, minkowskiMatrix_inv] using
      Burnett.Geometry.TensorCoordinateChange.inverse_pullback_cancel minkowskiMatrix A
        (isUnit_jac_of_leftInverse G F hG hF h x)
  rw [metricPullback_components, ← metricGradientSquare_minkowski]
  unfold metricGradientSquare
  simp_rw [coordPartial_comp_jac hF hf]
  change (∑ b, ∑ c, B b c * (∑ a, A a b * coordPartial a f (F x)) *
    (∑ e, A e c * coordPartial e f (F x))) = _
  have hm : minkowskiMatrixᵀ = minkowskiMatrix := by
    ext i j
    exact minkowskiMatrix_symm j i
  have hB : Bᵀ = B := by
    rw [show B = (Aᵀ * minkowskiMatrix * A)⁻¹ from rfl, Matrix.transpose_nonsing_inv,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hm, Matrix.mul_assoc]
  have hreorder :
      (∑ b, ∑ c, B b c * (∑ a, A a b * coordPartial a f (F x)) *
          (∑ e, A e c * coordPartial e f (F x))) =
        ∑ a, ∑ e, (A * B * Aᵀ) a e * coordPartial a f (F x) * coordPartial e f (F x) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    conv_lhs =>
      enter [2, b]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    conv_lhs =>
      enter [2, b]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    have hbc : B b c = B c b := congrArg (fun M : Matrix Index Index ℝ => M c b) hB
    rw [hbc]
    ring
  rw [hreorder, hAB]

theorem coordPartial_comp_mixed (b c : Index) {f : ℝ → ℝ} {g : CoordinateSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : CoordinateSpace) :
    coordPartial b (coordPartial c (fun y => f (g y))) x =
      deriv (deriv f) (g x) * coordPartial b g x * coordPartial c g x +
      deriv f (g x) * coordPartial b (coordPartial c g) x := by
  have hf' : ContDiff ℝ ∞ (deriv f) := ContDiff.deriv' (n := ∞) (by simpa using hf)
  have h1 : DifferentiableAt ℝ (fun y => deriv f (g y)) x :=
    (hf'.comp hg).differentiable (by simp) x
  have h2 : DifferentiableAt ℝ (coordPartial c g) x := (contDiff_partial c hg).differentiable (by simp) x
  rw [coordPartial_comp c hf hg]
  change fderiv ℝ (fun y => deriv f (g y) * coordPartial c g y) x (EuclideanSpace.single b 1) = _
  rw [fderiv_fun_mul h1 h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  change deriv f (g x) * coordPartial b (coordPartial c g) x +
      coordPartial c g x * coordPartial b (fun y => deriv f (g y)) x = _
  rw [coordPartial_comp b hf' hg]
  ring

theorem hess_coordPartial {F : CoordinateSpace → CoordinateSpace} (hF : ContDiff ℝ ∞ F)
    (x : CoordinateSpace) (a b c : Index) :
    hess F x a b c = coordPartial b (coordPartial c (fun y => F y a)) x := by
  have hF' : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hd := hF'.differentiable (by simp) x
  rw [hess, ← fderiv_jacobian_entry F x (coordinateBasis b) hd a c]
  unfold coordPartial
  rw [← coordinateBasis_eq_single b]
  have heq : (fun y => Burnett.Geometry.ChartVolume.derivativeMatrix (fderiv ℝ F y) a c) =
      (fun y => fderiv ℝ (fun z => F z a) y (EuclideanSpace.single c 1)) := by
    funext y
    rw [derivativeMatrix_apply, fderiv_coordinate_component (hF.differentiable (by simp) y),
      coordinateBasis_eq_single]
  rw [heq]

theorem mixed_p (b c : Index) (x : CoordinateSpace) : coordPartial b (coordPartial c p) x = 0 := by
  simp only [coordPartial_p, coordPartial_const, Pi.zero_apply]

theorem mixed_q (b c : Index) (x : CoordinateSpace) : coordPartial b (coordPartial c q) x = 0 := by
  simp only [coordPartial_q, coordPartial_const, Pi.zero_apply]

theorem mixed_coordinate (a b c : Index) (x : CoordinateSpace) :
    coordPartial b (coordPartial c (fun y : CoordinateSpace => y a)) x = 0 := by
  simp only [coordPartial_coordinate, coordPartial_const, Pi.zero_apply]

theorem mixed_phase {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (b c : Index) (x : CoordinateSpace) :
    coordPartial b (coordPartial c (phase f)) x =
      deriv (deriv f) (p x) * coordPartial b p x * coordPartial c p x := by
  have h : ContDiff ℝ ∞ (fun y => f (p y)) := hf.comp contDiff_p
  unfold phase
  rw [coordPartial_add c contDiff_q h, coordPartial_add b (contDiff_partial c contDiff_q)
    (contDiff_partial c h)]
  change coordPartial b (coordPartial c q) x + coordPartial b (coordPartial c (fun y => f (p y))) x = _
  rw [coordPartial_comp_mixed b c hf contDiff_p, mixed_q, mixed_p]
  ring

theorem hess_inverseContract_zero {f j : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j)
    (x : CoordinateSpace) (a : Index) :
    (∑ b, ∑ c, (matrixInverse (metricComponents (pullbackMetric f j) x)) b c *
      hess (inverse f j) x a b c) = 0 := by
  let Y := inverse f j
  let X := forward f j
  let G := (matrixInverse (metricComponents (pullbackMetric f j) x))
  have hy := contDiff_inverse hf hj
  have hx := contDiff_forward hf hj
  have hi : Function.LeftInverse X Y := forward_inverse f j
  have hp : p ∘ Y = p := by
    funext y
    rfl
  have hq : q ∘ Y = phase f := by
    funext y
    change y 0 - (y 1 - f (p y)) = y 0 - y 1 + f (p y)
    ring
  have hnp : metricGradientSquare G p x = 0 := by
    change metricGradientSquare (matrixInverse (metricComponents (metricPullback Y) x)) p x = 0
    rw [← hp, metricGradientSquare_pullback hy hx hi contDiff_p, gradientSquare_p]
  have hnq : metricGradientSquare G (phase f) x = 0 := by
    change metricGradientSquare (matrixInverse (metricComponents (metricPullback Y) x)) (phase f) x = 0
    rw [← hq, metricGradientSquare_pullback hy hx hi contDiff_q, gradientSquare_q]
  change (∑ b, ∑ c, G b c * hess Y x a b c) = 0
  simp_rw [hess_coordPartial (F := Y) hy]
  fin_cases a
  · change (∑ b, ∑ c, G b c * coordPartial b (coordPartial c (fun y : CoordinateSpace => y 0)) x) = 0
    simp only [mixed_coordinate, mul_zero, Finset.sum_const_zero]
  · change (∑ b, ∑ c, G b c * coordPartial b (coordPartial c (fun y => y 1 - f (p y))) x) = 0
    have hc : ContDiff ℝ ∞ (fun y => f (p y)) := hf.comp contDiff_p
    simp_rw [coordPartial_sub _ (contDiff_coordinate 1) hc,
      coordPartial_sub _ (contDiff_partial _ (contDiff_coordinate 1)) (contDiff_partial _ hc),
      mixed_coordinate, coordPartial_comp_mixed _ _ hf contDiff_p, mixed_p, mul_zero, add_zero, zero_sub]
    rw [← mul_zero (-(deriv (deriv f) (p x))), ← hnp]
    simp only [metricGradientSquare, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring
  · change (∑ b, ∑ c, G b c * coordPartial b (coordPartial c (fun y => y 2 - j (phase f y))) x) = 0
    have hc : ContDiff ℝ ∞ (fun y => j (phase f y)) := hj.comp (contDiff_phase hf)
    simp_rw [coordPartial_sub _ (contDiff_coordinate 2) hc,
      coordPartial_sub _ (contDiff_partial _ (contDiff_coordinate 2)) (contDiff_partial _ hc),
      mixed_coordinate, coordPartial_comp_mixed _ _ hj (contDiff_phase hf), mixed_phase hf, zero_sub]
    have hfactor :
        (∑ b, ∑ c, G b c *
          -(deriv (deriv j) (phase f x) * coordPartial b (phase f) x * coordPartial c (phase f) x +
            deriv j (phase f x) * (deriv (deriv f) (p x) * coordPartial b p x * coordPartial c p x))) =
        -(deriv (deriv j) (phase f x) * metricGradientSquare G (phase f) x +
          deriv j (phase f x) * deriv (deriv f) (p x) * metricGradientSquare G p x) := by
      rw [neg_add]
      simp only [metricGradientSquare, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [hfactor, hnp, hnq]
    ring
  · change (∑ b, ∑ c, G b c * coordPartial b (coordPartial c (fun y : CoordinateSpace => y 3)) x) = 0
    simp only [mixed_coordinate, mul_zero, Finset.sum_const_zero]

/-- The actual contracted Christoffel gauge vector of the pulled-back metric. -/
def gauge (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace) (x : CoordinateSpace) (a : Index) : ℝ :=
  ∑ b, ∑ c, (matrixInverse (metricComponents g x)) b c * computedConnection g x a b c

theorem pullbackMetric_gauge_zero {f j : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j)
    (x : CoordinateSpace) (a : Index) : gauge (pullbackMetric f j) x a = 0 := by
  let Y := inverse f j
  let A := jac Y x
  let Gi := (matrixInverse (metricComponents (pullbackMetric f j) x))
  have hΓ : computedConnection (pullbackMetric f j) x = transformedConnection A 0 (hess Y x) :=
    metricPullback_connection (contDiff_inverse hf hj) (contDiff_forward hf hj) (forward_inverse f j) x
  unfold gauge
  rw [hΓ]
  have htr (b c : Index) :
      transformedConnection A 0 (hess Y x) a b c = ∑ i, A⁻¹ a i * hess Y x i b c := by
    have h0 (p : Index) : connectionMatrix (0 : Connection) p = 0 := rfl
    simp [transformedConnection, transformedConnectionMatrix, directionalConnection, h0, connectionMatrix,
      Matrix.mul_apply]
  simp_rw [htr, Finset.mul_sum]
  change (∑ b, ∑ c, ∑ i, Gi b c * (A⁻¹ a i * hess Y x i b c)) = 0
  conv_lhs =>
    enter [2, b]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have hfactor (i : Index) : (∑ b, ∑ c, Gi b c * (A⁻¹ a i * hess Y x i b c)) =
      A⁻¹ a i * ∑ b, ∑ c, Gi b c * hess Y x i b c := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring
  apply Finset.sum_eq_zero
  intro i _
  rw [hfactor, hess_inverseContract_zero hf hj, mul_zero]

theorem metric_gauge_zero (n : ℕ) (x : CoordinateSpace) (a : Index) : gauge (metric n) x a = 0 :=
  pullbackMetric_gauge_zero (contDiff_firstShear n) (contDiff_secondShear n) x a

end Burnett.HarmonicShear

namespace Burnett.HarmonicShear

open Matrix
open Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.MetricJetNaturality

theorem minkowski_connection_zero (x : CoordinateSpace) : computedConnection (fun _ => minkowski) x = 0 := by
  have hJ : coordinateJet (metricComponents (fun _ => minkowski)) x = 0 := by
    funext d a b
    change fderiv ℝ (fun _ : CoordinateSpace => minkowski (coordinateBasis a) (coordinateBasis b))
      x (EuclideanSpace.single d 1) = 0
    simp [fderiv_const_apply]
  funext a b c
  simp [computedConnection, hJ, christoffel, koszul]

theorem minkowski_gauge_zero (x : CoordinateSpace) (a : Index) :
    gauge (fun _ => minkowski) x a = 0 := by
  simp [gauge, minkowski_connection_zero]

theorem jac_forward_row {f j : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j)
    (x : CoordinateSpace) (a b : Index) :
    jac (forward f j) x a b = ![(if b = 0 then 1 else 0),
        ((if b = 1 then 1 else 0) + deriv f (p x) * coordPartial b p x),
        ((if b = 2 then 1 else 0) + deriv j (q x) * coordPartial b q x),
        (if b = 3 then 1 else 0)] a := by
  have hF : DifferentiableAt ℝ (forward f j) x := (contDiff_forward hf hj).differentiable (by simp) x
  rw [jac, derivativeMatrix_apply, fderiv_coordinate_component hF, coordinateBasis_eq_single]
  change coordPartial b (fun y => forward f j y a) x = _
  have hf' : ContDiff ℝ ∞ (fun y => f (p y)) := hf.comp contDiff_p
  have hj' : ContDiff ℝ ∞ (fun y => j (q y)) := hj.comp contDiff_q
  fin_cases a
  · change coordPartial b (fun y : CoordinateSpace => y 0) x = _
    rw [coordPartial_coordinate]
    rfl
  · change coordPartial b (fun y => y 1 + f (p y)) x = _
    rw [coordPartial_add b (contDiff_coordinate 1) hf', coordPartial_coordinate, coordPartial_comp b hf contDiff_p]
    rfl
  · change coordPartial b (fun y => y 2 + j (q y)) x = _
    rw [coordPartial_add b (contDiff_coordinate 2) hj', coordPartial_coordinate, coordPartial_comp b hj contDiff_q]
    rfl
  · change coordPartial b (fun y : CoordinateSpace => y 3) x = _
    rw [coordPartial_coordinate]
    rfl

theorem jac_forward_det {f j : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j)
    (x : CoordinateSpace) : (jac (forward f j) x).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.submatrix_apply, Matrix.det_fin_three]
  simp only [jac_forward_row hf hj]
  norm_num [coordPartial_p, coordPartial_q, Fin.succ, Fin.succAbove, Fin.castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    show (1 : Index) ≠ 0 by decide, show (2 : Index) ≠ 0 by decide, show (3 : Index) ≠ 0 by decide,
    show (1 : Index) ≠ 2 by decide, show (2 : Index) ≠ 1 by decide, show (3 : Index) ≠ 1 by decide,
    show (3 : Index) ≠ 2 by decide, show (2 : Index) ≠ 3 by decide, show (1 : Index) ≠ 3 by decide]
  norm_num [show (⟨2, by decide⟩ : Index) = 2 by rfl, show (⟨3, by decide⟩ : Index) = 3 by rfl,
    show (2 : Index) ≠ 3 by decide, show (3 : Index) ≠ 2 by decide]

theorem jac_inverse_det {f j : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j)
    (x : CoordinateSpace) : (jac (inverse f j) x).det = 1 := by
  have h := congrArg Matrix.det (jac_leftInverse (forward f j) (inverse f j)
    (contDiff_forward hf hj) (contDiff_inverse hf hj) (forward_inverse f j) x)
  simpa only [Matrix.det_mul, jac_forward_det hf hj, Matrix.det_one, one_mul] using h

end Burnett.HarmonicShear

namespace Burnett.HarmonicShear

open Matrix Set Filter
open scoped Topology
open Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.ConnectionCoordinateChange (transformedConnection transformedConnectionMatrix directionalConnection)
open Burnett.Geometry.MetricJetNaturality
open Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.FlatRigidity

theorem metricPullback_component_contDiff {F : CoordinateSpace → CoordinateSpace}
    (hF : ContDiff ℝ ∞ F) (i j : Index) :
    ContDiff ℝ ∞ (fun x => metricComponents (metricPullback F) x i j) := by
  have hc (a b : Index) : ContDiff ℝ ∞
      (fun x => jac F x a i * minkowskiMatrix a b * jac F x b j) :=
    ((contDiff_jac_entry hF a i).mul contDiff_const).mul (contDiff_jac_entry hF b j)
  have h : (fun x => metricComponents (metricPullback F) x i j) =
      (fun x => ∑ a, ∑ b, jac F x a i * minkowskiMatrix a b * jac F x b j) := by
    funext x
    exact congrArg (fun A : Matrix Index Index ℝ => A i j) (metricPullback_components F x) |>.trans
      (matrix_triple_entry _ _ _ i j)
  rw [h]
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ => hc a b

theorem metricPullback_nondegenerate {F G : CoordinateSpace → CoordinateSpace}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (h : Function.LeftInverse G F) (x : CoordinateSpace) :
    (metricPullback F x).Nondegenerate := by
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero coordinateBasis).mpr
  rw [← Burnett.Geometry.ManifoldMetricTransition.metricComponents_eq_toMatrix (metricPullback F) x]
  rw [metricPullback_components, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hf := ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_jac_of_leftInverse G F hG hF h x)).ne_zero
  have hm := ((Matrix.isUnit_iff_isUnit_det _).mp isUnit_minkowskiMatrix).ne_zero
  exact mul_ne_zero (mul_ne_zero hf hm) hf

theorem jac_coordinateJet (F : CoordinateSpace → CoordinateSpace) (hF : ContDiff ℝ ∞ F)
    (x : CoordinateSpace) (d : Index) :
    frameCoordinateJet (jac F) x d = connectionMatrix (hess F x) d := by
  ext a b
  have hF' : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  simpa only [frameCoordinateJet, coordinateJet, jac, connectionMatrix, hess, coordinateBasis_eq_single] using
    fderiv_jacobian_entry F x (coordinateBasis d) (hF'.differentiable (by simp) x) a b

theorem coordinateJet_matrix_mul {A B : CoordinateSpace → Matrix Index Index ℝ}
    (x : CoordinateSpace) (d : Index) (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) x) :
    frameCoordinateJet (fun y => A y * B y) x d =
      frameCoordinateJet A x d * B x +
        A x * frameCoordinateJet B x d := by
  ext i j
  change coordPartial d (fun y => ∑ k, A y i k * B y k j) x = _
  unfold coordPartial
  simp only [Matrix.add_apply, Matrix.mul_apply, frameCoordinateJet, coordinateJet]
  rw [fderiv_fun_sum (u := Finset.univ) (fun k _ => (hA i k).fun_mul (hB k j)), ContinuousLinearMap.sum_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_fun_mul (hA i k) (hB k j)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem metricPullback_parallel {F G : CoordinateSpace → CoordinateSpace}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (h : Function.LeftInverse G F)
    (x : CoordinateSpace) (d : Index) :
    frameCoordinateJet (fun y => jac G (F y)) x d =
      -(connectionMatrix (computedConnection (metricPullback F) x) d * jac G (F x)) := by
  let A := jac F
  let E := fun y => jac G (F y)
  have hEA : ∀ y, E y * A y = 1 := jac_leftInverse G F hG hF h
  have ha : IsUnit (A x).det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_jac_of_leftInverse G F hG hF h x)
  have hAr := Matrix.mul_nonsing_inv (A x) ha
  have hAl := Matrix.nonsing_inv_mul (A x) ha
  have hE : E x = (A x)⁻¹ := by
    calc
      E x = E x * (A x * (A x)⁻¹) := by rw [hAr, Matrix.mul_one]
      _ = (A x)⁻¹ := by rw [← Matrix.mul_assoc, hEA, Matrix.one_mul]
  have hprod : frameCoordinateJet E x d * A x + E x *
        frameCoordinateJet A x d = 0 := by
    rw [← coordinateJet_matrix_mul (A := E) (B := A) x d (fun i j => ((contDiff_jac_entry hG i j).comp hF).differentiable
      (by simp) x) (fun i j => (contDiff_jac_entry hF i j).differentiable (by simp) x)]
    rw [show (fun y => E y * A y) = fun _ => 1 from funext hEA]
    ext i j
    simp [frameCoordinateJet, coordinateJet]
  have hΓ : connectionMatrix (computedConnection (metricPullback F) x) d =
      (A x)⁻¹ * frameCoordinateJet A x d := by
    rw [metricPullback_connection hF hG h, jac_coordinateJet F hF]
    have hzero (p : Index) : Burnett.Geometry.ConnectionCoordinateChange.connectionMatrix (0 : Connection) p = 0 := rfl
    ext a b
    simp [connectionMatrix, transformedConnection, transformedConnectionMatrix, directionalConnection, hzero]
    rfl
  change frameCoordinateJet E x d = -(connectionMatrix (computedConnection (metricPullback F) x) d * E x)
  rw [hΓ]
  have hp := congrArg (fun Q : Matrix Index Index ℝ => Q * E x) hprod
  change (frameCoordinateJet E x d * A x + E x *
        frameCoordinateJet A x d) * E x = 0 * E x at hp
  rw [add_mul, Matrix.zero_mul, Matrix.mul_assoc (frameCoordinateJet E x d), hE, hAr, Matrix.mul_one] at hp
  rw [hE]
  exact eq_neg_of_add_eq_zero_left hp

theorem metricPullback_riemann_zero {F G : CoordinateSpace → CoordinateSpace}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (h : Function.LeftInverse G F)
    (x : CoordinateSpace) (d e : Index) :
    coordinateRiemann (computedConnection (metricPullback F)) x d e = 0 := by
  apply coordinateRiemann_computedConnection_eq_zero_of_parallel_frame isOpen_univ
    (metricPullback F) (fun i j => (metricPullback_component_contDiff hF i j).contDiffOn)
    (fun y _ => metricPullback_nondegenerate hF hG h y) (fun y => jac G (F y))
    (fun i j => (((contDiff_jac_entry hG i j).comp hF).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)).contDiffOn)
    (fun y _ => ?_) (fun y _ => metricPullback_parallel hF hG h y) x (mem_univ _) d e
  apply isUnit_of_mul_eq_one _ (jac F y).det
  rw [← Matrix.det_mul, jac_leftInverse G F hG hF h, Matrix.det_one]

theorem metric_riemann_zero (n : ℕ) (x : CoordinateSpace) (d e : Index) :
    coordinateRiemann (computedConnection (metric n)) x d e = 0 :=
  metricPullback_riemann_zero (contDiff_inverse (contDiff_firstShear n) (contDiff_secondShear n))
    (contDiff_forward (contDiff_firstShear n) (contDiff_secondShear n))
    (forward_inverse (firstShear n) (secondShear n)) x d e

theorem metric_ricci_zero (n : ℕ) (x : CoordinateSpace) (b c : Index) :
    coordinateRicci (computedConnection (metric n)) x b c = 0 := by
  have hf := contDiff_firstShear n
  have hj := contDiff_secondShear n
  let F := inverse (firstShear n) (secondShear n)
  let G := forward (firstShear n) (secondShear n)
  have hF := contDiff_inverse hf hj
  have hG := contDiff_forward hf hj
  have hi : Function.LeftInverse G F := forward_inverse _ _
  have hT : ∀ᶠ y in 𝓝 x, ∀ a b c, computedConnection (metric n) y a b c =
      computedConnection (metric n) y a c b := Eventually.of_forall fun y => by
    change ∀ a b c, computedConnection (metricPullback F) y a b c =
      computedConnection (metricPullback F) y a c b
    rw [metricPullback_connection hF hG hi]
    exact Burnett.Geometry.ConnectionCoordinateChange.transformed_connection_torsion_free _ _ _
      (fun _ _ _ => rfl) (hess_lower_symm hF y)
  rw [coordinateRicci_eq_riemann_contract _ _ hT]
  simp_rw [metric_riemann_zero, Matrix.zero_apply, Finset.sum_const_zero]

end Burnett.HarmonicShear
