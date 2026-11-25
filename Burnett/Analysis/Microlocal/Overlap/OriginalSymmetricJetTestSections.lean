import Burnett.Analysis.Microlocal.Overlap.SmoothCompactSymmetricJetTests

/-! The original covariant input is a genuine compact smooth symmetric jet. -/

set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option synthInstance.maxHeartbeats 390000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Filter Classical MeasureTheory Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient
  (fixedHalfDensity fixedHalfDensity_smooth fixedVolumeCovariantGradientSchwartz
    fixedVolumeCovariantGradientSchwartz_tsupport)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped Manifold ContDiff Topology BigOperators ComplexConjugate

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- The original geometrically cut off covariant jet, as an actual compact
smooth symmetric jet test. -/
def originalCovariantSymmetricJetTest (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (c : AtlasChart M) (χ : D)
    (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) (n : ℕ) :
    smoothCompactSymmetricJet M := by
  let f (i : JetSlot) : E → ℂ := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i
  let K := tsupport (χ : E → ℝ)
  have hf : ∀ i, ContDiff ℝ ∞ (f i) := fun i =>
    (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i).smooth ⊤
  have hS : ∀ i, support (f i) ⊆ K := fun i => (subset_tsupport _).trans
    (fixedVolumeCovariantGradientSchwartz_tsupport r B g hB hg hn c χ hχ n i)
  exact compactSymmetricJetChartTest B hB hn c f hf K (test_compactSupport χ) hχ hS

theorem originalCovariantSymmetricJetTest_support (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (c : AtlasChart M) (χ : D)
    (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) (S : Set M) (hSc : S ⊆ c.chart.source)
    (hχS : tsupport (χ : E → ℝ) ⊆ c.chart '' S) (n : ℕ) :
    symmetricJetSectionSupport (originalCovariantSymmetricJetTest r B g hB hg hn c χ hχ n).val ⊆ S := by
  refine (symmetricJetChartLift_support B c _ (c.chart '' S) fun i =>
    (subset_tsupport _).trans ((fixedVolumeCovariantGradientSchwartz_tsupport r B g hB hg hn c χ hχ n i).trans hχS)).trans ?_
  rintro _ ⟨x, ⟨p, hp, rfl⟩, rfl⟩
  rwa [c.chart.left_inv (hSc hp)]

theorem originalCovariantSymmetricJetTest_halfDensity (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (n : ℕ) (i : JetSlot) :
    symmetricJetHalfDensity B c (originalCovariantSymmetricJetTest r B g hB hg hn c χ hχ n).val i =
      (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i : E → ℂ) :=
  symmetricJetHalfDensity_originalCovariantChartLift r B g hB hg hn hsB hsG c χ hχ n i

end Burnett.Microlocal.Overlap
