import Burnett.Analysis.Microlocal.ChartDensitySymmetry
import Burnett.Geometry.FlatRigidity.WeakCurvature

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.ActualCoordinateCurlDensity

open Set Filter MeasureTheory Matrix Burnett.Fourier
open scoped ContDiff Topology ENNReal InnerProduct BigOperators ComplexOrder Matrix
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricSequence Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetricTransition
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport test_memLp directional)
open Burnett.F05.CoordinateCurl Burnett.F05.OriginalCoordinateCurl
open Burnett.Microlocal.CurlDensity Burnett.Microlocal.FixedChartGeometricDensity
open Burnett.Microlocal.SmoothBaseTests Burnett.Microlocal.SmoothAngularTests
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.BesselLocalization Burnett.Microlocal.RowKernelDensity
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.FixedSubsequenceSeparableExtension
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- One smooth coefficient plateau covers the actual compact ball and has
topological support inside the same chart. -/
theorem exists_chartCurl_plateau (K : BallData) (c : M)
    (hKt : K.closedBall ⊆ (chartAt CoordinateSpace c).target) :
    ∃ θ : D, tsupport (θ : Space → ℝ) ⊆ (chartAt CoordinateSpace c).target ∧
      ∀ x ∈ K.closedBall, (θ : Space → ℝ) x = 1 := by
  obtain ⟨L, _, _, hLt, θ, hs, hc, hθL, _, hOne⟩ :=
    Burnett.Geometry.FlatRigidity.exists_smooth_cutoff_on_compact_chart
      (isCompact_closedBall K.center K.radius) (chartAt CoordinateSpace c).open_target hKt
  exact ⟨⟨θ, hs, hc⟩, hθL.trans hLt, hOne⟩

/-- The actual grouped finite principal curl coefficient row on the round
cosphere. The Fourier factor is the same imaginary unit in every component. -/
theorem curl_separableRowCoefficients_eq (K : BallData) (θ : D)
    (hθ : ∀ x ∈ K.closedBall, (θ : Space → ℝ) x = 1)
    (x : Chart K) (r : CurlSlot) (i : JetSlot) :
    separableRowCoefficients K (curlRowInputs r.1 r.2.1 r.2.2)
      (fun s => physicalCoefficient (curlRowCoefficients θ s))
      (fun s => angularDirectionSymbol (curlRowDirections r.1 r.2.1 s)) x i =
      Complex.I * curlMatrix (roundCovector x) r i := by
  rw [rowPrincipalCoefficients_eq_round, Fin.sum_univ_two]
  have hInner (a : Axis) : inner ℝ (x.2 : Space) (axis a) = roundCovector x a := by
    rw [axis, EuclideanSpace.inner_single_right]
    simp [roundCovector]
  have hOne := hθ x.1 x.1.property
  have hNeg : ((-θ : D) : Space → ℝ) x.1 = -1 := by
    change -(θ : Space → ℝ) x.1 = -1
    rw [hOne]
  change Complex.I *
      ((if (r.2.1,r.2.2) = i then
        (((θ : Space → ℝ) x.1 * inner ℝ (x.2 : Space) (axis r.1) : ℝ) : ℂ) else 0) +
        (if (r.1,r.2.2) = i then
        ((((-θ : D) : Space → ℝ) x.1 * inner ℝ (x.2 : Space) (axis r.2.1) : ℝ) : ℂ) else 0)) = _
  simp only [hInner, hOne, hNeg, one_mul, neg_one_mul, Complex.ofReal_neg, curlMatrix,
    sub_eq_add_neg]
  apply congrArg (fun z : ℂ => Complex.I * z)
  have hfirst (p : JetSlot) (b : ℂ) :
      (if p = i then b else 0) = if i = p then b else 0 := by
    by_cases hp : p = i
    · rw [if_pos hp, if_pos hp.symm]
    · rw [if_neg hp, if_neg (Ne.symm hp)]
  have hsecond (p : JetSlot) (b : ℂ) :
      (if p = i then -b else 0) = -(if i = p then b else 0) := by
    by_cases hp : p = i
    · rw [if_pos hp, if_pos hp.symm]
    · rw [if_neg hp, if_neg (Ne.symm hp), neg_zero]
  exact congrArg₂ (· + ·) (hfirst _ _) (hsecond _ _)

variable [IsManifold Model ∞ M]

def localizedOriginalDerivative (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (c : M) (χ : D) (n : ℕ) (k : JetSlot) (x : Space) : ℝ :=
  (χ : Space → ℝ) x * directional k.1 (originalComponent g₀ g c n k.2) x

theorem localizedOriginalDerivative_symmetry (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (hs₀ : IsSymmetric g₀) (hsg : ∀ n, IsSymmetric (g n)) (c : M) (χ : D)
    (n : ℕ) (a b d : Axis) :
    localizedOriginalDerivative g₀ g c χ n (a,b,d) =
      localizedOriginalDerivative g₀ g c χ n (a,d,b) := by
  have h : originalComponent g₀ g c n (b,d) = originalComponent g₀ g c n (d,b) := by
    funext y
    unfold originalComponent metricComponents
    rw [Burnett.Geometry.FiberMetric.covariant_symmetric _ (coordinateBilinear_symmetric _ (hsg n) c y),
      Burnett.Geometry.FiberMetric.covariant_symmetric _ (coordinateBilinear_symmetric _ hs₀ c y)]
  exact congrArg (fun f => fun x => (χ : Space → ℝ) x * directional a f x) h

theorem originalGradient_toLp_symmetry (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (hs₀ : IsSymmetric g₀)
    (hsg : ∀ n, IsSymmetric (g n)) (c : M) (χ : D)
    (hχ : tsupport (χ : Space → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (a b d : Axis) :
    (originalGradientSchwartz g₀ g h₀ hg c χ hχ n (a,b,d)).toLp 2 volume =
      (originalGradientSchwartz g₀ g h₀ hg c χ hχ n (a,d,b)).toLp 2 volume := by
  apply congrArg (fun s : SchwartzMap Space ℂ => s.toLp 2 volume)
  apply SchwartzMap.ext
  intro x
  exact congrArg (fun f : Space → ℝ => (f x : ℂ))
    (localizedOriginalDerivative_symmetry g₀ g hs₀ hsg c χ n a b d)


end Burnett.F05.ActualCoordinateCurlDensity
