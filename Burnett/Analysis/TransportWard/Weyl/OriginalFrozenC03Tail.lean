import Burnett.Analysis.TransportWard.Weyl.OriginalFrozenC03TailRates

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 22000000

noncomputable section

namespace Burnett.V03.Palatini

open Filter Metric MeasureTheory Set Matrix Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open UnitNullCompactness CotangentAngularExtension
open Burnett.A02.FrequencySplit Burnett.C02 Burnett.C03 Burnett.C04 Burnett.Fourier Burnett.V06
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.Analysis.ProjectiveNullCaps (descendingProfile descendingProfile_contDiff descendingProfile_range
  descendingProfile_eq_zero descendingProfile_eq_one)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix metricDensity)
open Burnett.C01 (patchCenter)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix receivingCutoffFluctuation)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped BigOperators ComplexConjugate ContDiff ENNReal Manifold Matrix Matrix.Norms.Elementwise Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The original C03 tail follows from its rate-specific bound at `p = 4`. -/
theorem hasOriginalFrozenC03Tail_of_originalChartWard
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hSig : HasLorentzSignature B) (hg : ∀ n, IsSmooth (g n))
    (hgSym : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c₀ : M) (f : CotangentBundle M → ℝ) (hfTest : IsDegreeOneTransportTest f) (hfOdd : IsAntipodallyOdd f)
    (S : Set M) (hS : IsCompact S) (hSChart : S ⊆ (chartAt E c₀).source)
    (hSOff : ∀ p ∈ puncturedCotangent, p.proj ∉ S → f p = 0) :
    HasOriginalFrozenC03Tail B g hB hg σ c₀ f := by
  let p : ℝ := 4
  have hp : 3 < p := by norm_num [p]
  have rate := hasOriginalFrozenC03TailAtExponent_of_originalChartWard
    r B g hB hSig hg hgSym hconv hb σ hσ A hA hPair c₀ f hfTest hfOdd S hS hSChart hSOff p hp
  unfold HasOriginalFrozenC03TailAtExponent at rate
  unfold HasOriginalFrozenC03Tail
  intro c a₀ β K V hK hV hKV hConvex hVU e he hE hError Msrc Ccoeff Ccut Cp hMsrc hCcoeff hCcut hCp
  obtain ⟨Cnear, δ₀, hα, hν, hδ₀, bound⟩ :=
    rate K V hK hV hKV hConvex hVU e he hE hError Msrc Ccoeff Ccut Cp hMsrc hCcoeff hCcut hCp
  exact ⟨Cnear, frozenErrorExponent p, 2 * (p - 3) / (p - 2), δ₀, hα, hν, hδ₀, bound⟩

end Burnett.V03.Palatini
