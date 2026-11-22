import Burnett.Analysis.GaugeProjection.ProjectedSourceGaugeDerivative

set_option autoImplicit false
set_option maxHeartbeats 2700000

noncomputable section

namespace Burnett.P01

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open scoped BigOperators

/-- Coordinate derivative of a scalar field, on the same Euclidean chart. -/
def scalarPartial (f : CoordinateSpace → ℝ) (a : Index) (x : CoordinateSpace) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single a 1)

theorem scalarPartial_product
    (f g : CoordinateSpace → ℝ) (a : Index) (x : CoordinateSpace)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    scalarPartial (fun y => f y * g y) a x =
      scalarPartial f a x * g x + f x * scalarPartial g a x := by
  simp only [scalarPartial, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem scalarSecondPartial_product
    (f g : CoordinateSpace → ℝ) (a b : Index) (x : CoordinateSpace)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hdf : DifferentiableAt ℝ (scalarPartial f b) x)
    (hdg : DifferentiableAt ℝ (scalarPartial g b) x) :
    scalarPartial (scalarPartial (fun y => f y * g y) b) a x =
      scalarPartial (scalarPartial f b) a x * g x +
        scalarPartial f b x * scalarPartial g a x +
        scalarPartial f a x * scalarPartial g b x +
        f x * scalarPartial (scalarPartial g b) a x := by
  have h : scalarPartial (fun y => f y * g y) b =
      fun y => scalarPartial f b y * g y + f y * scalarPartial g b y :=
    funext fun y => scalarPartial_product f g b y (hf y) (hg y)
  rw [h]
  change fderiv ℝ (fun y => scalarPartial f b y * g y + f y * scalarPartial g b y) x
      (EuclideanSpace.single a 1) = _
  have hprod := ((hdf.hasFDerivAt.fun_mul (hg x).hasFDerivAt).fun_add
    ((hf x).hasFDerivAt.fun_mul hdg.hasFDerivAt)).fderiv
  rw [hprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, scalarPartial]
  ring

/-- The nondivergence scalar term on the exact chart coefficient. -/
def scalarWaveAt (A : Tensor2) (f : CoordinateSpace → ℝ) (x : CoordinateSpace) : ℝ :=
  ∑ a, ∑ b, A a b * scalarPartial (scalarPartial f b) a x

/-- Localization of the nondivergence wave term. The cutoff errors use at
most first derivatives of the localized field. -/
theorem scalarWaveAt_localized
    (A : Tensor2) (χ f : CoordinateSpace → ℝ) (x : CoordinateSpace)
    (hχ : Differentiable ℝ χ) (hf : Differentiable ℝ f)
    (hχ2 : ∀ b, DifferentiableAt ℝ (scalarPartial χ b) x)
    (hf2 : ∀ b, DifferentiableAt ℝ (scalarPartial f b) x) :
    scalarWaveAt A (fun y => χ y * f y) x = χ x * scalarWaveAt A f x +
      ∑ a, ∑ b, A a b * (scalarPartial (scalarPartial χ b) a x * f x +
        scalarPartial χ b x * scalarPartial f a x +
        scalarPartial χ a x * scalarPartial f b x) := by
  simp only [scalarWaveAt, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [scalarSecondPartial_product χ f a b x hχ hf (hχ2 b) (hf2 b)]
  ring

/-- Moving a scalar chart cutoff inside the symmetrized gauge gradient. -/
theorem localizedGaugeGradient
    (χ : CoordinateSpace → ℝ) (V : CoordinateSpace → Covector) (x : CoordinateSpace)
    (hχ : DifferentiableAt ℝ χ x) (hV : ∀ j, DifferentiableAt ℝ (fun y => V y j) x)
    (i j : Index) :
    χ x * (scalarPartial (fun y => V y j) i x + scalarPartial (fun y => V y i) j x) =
      scalarPartial (fun y => χ y * V y j) i x + scalarPartial (fun y => χ y * V y i) j x -
        (scalarPartial χ i x * V x j + scalarPartial χ j x * V x i) := by
  rw [scalarPartial_product χ (fun y => V y j) i x hχ (hV j),
    scalarPartial_product χ (fun y => V y i) j x hχ (hV i)]
  ring

end Burnett.P01
