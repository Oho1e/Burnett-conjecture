import Burnett.Analysis.GaugeProjection.ProjectedSourceLocalization
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.P01

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CurvatureDifference
open scoped BigOperators

private theorem scalarPartial_sub_global (f g : CoordinateSpace → ℝ) (b : Index)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    scalarPartial (fun y => f y - g y) b = fun y => scalarPartial f b y - scalarPartial g b y := by
  funext y
  simp only [scalarPartial, fderiv_fun_sub (hf y) (hg y), ContinuousLinearMap.sub_apply]

private theorem scalarWaveAt_sub (A : Tensor2) (f g : CoordinateSpace → ℝ) (x : CoordinateSpace)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hf2 : ∀ b, DifferentiableAt ℝ (scalarPartial f b) x)
    (hg2 : ∀ b, DifferentiableAt ℝ (scalarPartial g b) x) :
    scalarWaveAt A (fun y => f y - g y) x = scalarWaveAt A f x - scalarWaveAt A g x := by
  simp only [scalarWaveAt, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [scalarPartial_sub_global f g b hf hg]
  change A a b * (fderiv ℝ (fun y => scalarPartial f b y - scalarPartial g b y) x)
      (EuclideanSpace.single a 1) = _
  rw [fderiv_fun_sub (hf2 b) (hg2 b), ContinuousLinearMap.sub_apply]
  exact mul_sub _ _ _

/-- The cutoff terms from the scalar wave operator on a localized fluctuation. -/
def localizedWaveError (A : Tensor2) (χ f : CoordinateSpace → ℝ) (x : CoordinateSpace) : ℝ :=
  ∑ a, ∑ b, A a b * (scalarPartial (scalarPartial χ b) a x * f x +
    scalarPartial χ b x * scalarPartial f a x + scalarPartial χ a x * scalarPartial f b x)

/-- The rest of the localized vacuum source after moving the cutoff into the
symmetrized gauge gradient. The second derivatives present here are those
of the fixed background and the scalar cutoff. -/
def localizedVacuumSourceRemainder
    (inv g g₀ : CoordinateSpace → Tensor2) (χ : CoordinateSpace → ℝ)
    (x : CoordinateSpace) (i j : Index) : ℝ :=
  χ x * (projectedSourceFirstJetRemainder (inv x) (coordinateJet g x) (coordinateJet inv x) i j -
      scalarWaveAt (inv x) (fun y => g₀ y i j) x) +
    localizedWaveError (inv x) χ (fun y => g y i j - g₀ y i j) x -
    (scalarPartial χ i x * coordinateGaugeCovector inv g x j +
      scalarPartial χ j x * coordinateGaugeCovector inv g x i)

/-- The raw local vacuum equation before the fixed projection. This is the
scalar nondivergence source on the cutoff fluctuation and its exact
symmetrized-gradient contribution. -/
theorem localizedVacuumSource_eq_symmetrizedGauge_add_remainder
    (inv g g₀ : CoordinateSpace → Tensor2) (χ : CoordinateSpace → ℝ)
    (x : CoordinateSpace) (i j : Index)
    (hχ : Differentiable ℝ χ) (hχ2 : ∀ b, DifferentiableAt ℝ (scalarPartial χ b) x)
    (hg : ∀ b c, Differentiable ℝ (fun y => g y b c))
    (hg₀ : ∀ b c, Differentiable ℝ (fun y => g₀ y b c))
    (hdg : ∀ a b c, DifferentiableAt ℝ (fun y => coordinateJet g y a b c) x)
    (hdg₀ : ∀ a b c, DifferentiableAt ℝ (fun y => coordinateJet g₀ y a b c) x)
    (hInv : DifferentiableComponentsAt inv x) (hSym : IsSymmetricTensor (inv x))
    (hMixed : ∀ a b, coordinateSecondMetricJet g x a b = coordinateSecondMetricJet g x b a)
    (hMetric : ∀ a b, IsSymmetricTensor (coordinateSecondMetricJet g x a b))
    (hGauge : ∀ b, DifferentiableAt ℝ (fun y => coordinateGaugeCovector inv g y b) x)
    (hVac : coordinateRicci (fun y => christoffel (inv y) (coordinateJet g y)) x i j = 0) :
    scalarWaveAt (inv x) (fun y => χ y * (g y i j - g₀ y i j)) x =
      scalarPartial (fun y => χ y * coordinateGaugeCovector inv g y j) i x +
      scalarPartial (fun y => χ y * coordinateGaugeCovector inv g y i) j x +
      localizedVacuumSourceRemainder inv g g₀ χ x i j := by
  let f (y : CoordinateSpace) := g y i j
  let f₀ (y : CoordinateSpace) := g₀ y i j
  have hDf : ∀ b, DifferentiableAt ℝ (scalarPartial f b) x := fun b => hdg b i j
  have hDf₀ : ∀ b, DifferentiableAt ℝ (scalarPartial f₀ b) x := fun b => hdg₀ b i j
  have hDiff : Differentiable ℝ (fun y => f y - f₀ y) := (hg i j).sub (hg₀ i j)
  have hDiffSub : ∀ b, DifferentiableAt ℝ (scalarPartial (fun y => f y - f₀ y) b) x := by
    intro b
    rw [scalarPartial_sub_global f f₀ b (hg i j) (hg₀ i j)]
    exact (hDf b).sub (hDf₀ b)
  have hRic := twice_coordinateRicci_eq_wave_symmetrizedGauge_remainder
    inv g x hInv hdg hSym hMixed hMetric i j
  rw [hVac, mul_zero] at hRic
  change 0 = -scalarWaveAt (inv x) f x +
    scalarPartial (fun y => coordinateGaugeCovector inv g y j) i x +
    scalarPartial (fun y => coordinateGaugeCovector inv g y i) j x +
    projectedSourceFirstJetRemainder (inv x) (coordinateJet g x) (coordinateJet inv x) i j at hRic
  have hWave : scalarWaveAt (inv x) f x =
      scalarPartial (fun y => coordinateGaugeCovector inv g y j) i x +
      scalarPartial (fun y => coordinateGaugeCovector inv g y i) j x +
      projectedSourceFirstJetRemainder (inv x) (coordinateJet g x) (coordinateJet inv x) i j := by
    linarith only [hRic]
  have hCut := localizedGaugeGradient χ (coordinateGaugeCovector inv g) x (hχ x) hGauge i j
  change scalarWaveAt (inv x) (fun y => χ y * (f y - f₀ y)) x = _
  rw [scalarWaveAt_localized (inv x) χ (fun y => f y - f₀ y) x hχ hDiff hχ2 hDiffSub,
    scalarWaveAt_sub (inv x) f f₀ x (hg i j) (hg₀ i j) hDf hDf₀, hWave]
  unfold localizedVacuumSourceRemainder localizedWaveError
  dsimp only [f, f₀]
  linear_combination hCut

end Burnett.P01
