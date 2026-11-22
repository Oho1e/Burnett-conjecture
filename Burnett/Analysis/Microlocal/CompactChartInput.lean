import Burnett.Analysis.Microlocal.OriginalCoordinateCurl

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CurlDensity

open Burnett.RicciSymbol
abbrev Pair := Index × Index
abbrev JetSlot := Index × Pair

end Burnett.Microlocal.CurlDensity

namespace Burnett.Microlocal.SmoothBaseTests

open Set
open Burnett.X02.SobolevTestJet (Space)

/-- One fixed compact coordinate ball and its cutoff data. -/
structure BallData where
  center : Space
  radius : ℝ
  nonnegative : 0 ≤ radius

def BallData.closedBall (K : BallData) : Set Space :=
  Metric.closedBall K.center K.radius

abbrev BallData.Point (K : BallData) := ↥K.closedBall

instance instCompactBall (K : BallData) : CompactSpace K.Point :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

end Burnett.Microlocal.SmoothBaseTests

namespace Burnett.Microlocal.CountableAuxiliaryCharts

open Set MeasureTheory Filter Burnett.Fourier Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricSequence Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetricTransition
open Burnett.X02.SobolevTestJet (D Space)
open Burnett.F05.OriginalCoordinateCurl Burnett.Microlocal.CurlDensity
open Burnett.Microlocal.SmoothBaseTests
open scoped ContDiff Topology

/-- A true compact coordinate ball and one smooth inner cutoff. -/
structure CompactChartInput (M : Type*) [TopologicalSpace M] [ChartedSpace CoordinateSpace M] where
  center : M
  ball : BallData
  ball_in_chart : ball.closedBall ⊆ (chartAt CoordinateSpace center).target
  cutoff : D
  cutoff_support : tsupport (cutoff : Space → ℝ) ⊆ ball.closedBall

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The same coordinate-gradient L² input used in the single-chart theorem. -/
def chartJetL2 (q : CompactChartInput M) (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (n : ℕ) (i : JetSlot) : ComplexL2 Space :=
  (originalGradientSchwartz g₀ g h₀ hg q.center q.cutoff
    (q.cutoff_support.trans q.ball_in_chart) n i).toLp 2 volume

theorem chartJetL2_comp (q : CompactChartInput M) (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (h₀ : IsSmooth g₀) (hg : ∀ n, IsSmooth (g n)) (φ : ℕ → ℕ) (n : ℕ) (i : JetSlot) :
    chartJetL2 q g₀ (g ∘ φ) h₀ (fun n => hg (φ n)) n i =
      chartJetL2 q g₀ g h₀ hg (φ n) i := rfl

/-- Physical local uniform convergence is inherited by every strict subsequence. -/
theorem locallyUniformlyConverges_comp_strictMono (r : Metric (M := M))
    (g₀ : Field (M := M)) (g : ℕ → Field (M := M))
    (hconv : LocallyUniformlyConverges r g g₀) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    LocallyUniformlyConverges r (g ∘ φ) g₀ := by
  intro S hS U hU
  exact hφ.tendsto_atTop.eventually ((hconv S hS) U hU)

end Burnett.Microlocal.CountableAuxiliaryCharts
