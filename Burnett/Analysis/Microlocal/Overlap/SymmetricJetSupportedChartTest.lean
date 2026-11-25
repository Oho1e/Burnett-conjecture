import Burnett.Analysis.Microlocal.Overlap.SymmetricJetChartCompression
import Burnett.Analysis.Microlocal.Overlap.OriginalSymmetricJetTestSections
import Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol

/-! Genuine lifts of supported chart tests and exact removal of plateau cutoffs. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 360000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient
  (fixedVolumeCovariantGradientSchwartz fixedVolumeCovariantGradientSchwartz_tsupport)
open Burnett.Microlocal.BesselLocalization (coeffMul)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology

open private coeffMul_eq_self_on_support from Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Directly lift a smooth ordered array supported inside a compact chart window. -/
def supportedSymmetricJetChartTest (B : Field (M := M)) (hB : IsSmooth B)
    (hn : IsNondegenerate B) (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target)
    (f : JetSlot → SchwartzMap E ℂ) (hf : ∀ i, tsupport (f i : E → ℂ) ⊆ K) :
    smoothCompactSymmetricJet M :=
  compactSymmetricJetChartTest B hB hn c (fun i => (f i : E → ℂ)) (fun i => (f i).smooth ⊤)
    K hK hKc (fun i => (subset_tsupport _).trans (hf i))

/-- On supported arrays a chart cutoff equal to one cancels exactly. -/
theorem compactSymmetricJetChartTestLinear_eq_supported
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target)
    (ρ : D) (hρ : tsupport (ρ : E → ℝ) ⊆ c.chart.target) (hOne : ∀ x ∈ K, (ρ : E → ℝ) x = 1)
    (f : JetSlot → SchwartzMap E ℂ) (hf : ∀ i, tsupport (f i : E → ℂ) ⊆ K) :
    compactSymmetricJetChartTestLinear B hB hn c ρ hρ f =
      supportedSymmetricJetChartTest B hB hn c K hK hKc f hf := by
  apply Subtype.ext
  have hF (i : JetSlot) : coeffMul ρ (f i) = f i :=
    coeffMul_eq_self_on_support ρ (f i) (fun x hx => hOne x (hf i hx))
  change symmetricJetChartLift B c (fun i => (coeffMul ρ (f i) : E → ℂ)) =
    symmetricJetChartLift B c (fun i => (f i : E → ℂ))
  simp only [hF]

/-- This is the full rapidly decreasing coordinate array of the original
geometric covariant jet, lifted on any larger supported window. -/
theorem supportedSymmetricJetChartTest_original
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKc : K ⊆ c.chart.target)
    (η : D) (hη : tsupport (η : E → ℝ) ⊆ K) (n : ℕ) :
    supportedSymmetricJetChartTest B hB hn c K hK hKc
      (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η (hη.trans hKc) n)
      (fun i => (fixedVolumeCovariantGradientSchwartz_tsupport r B g hB hg hn c η
        (hη.trans hKc) n i).trans hη) =
      originalCovariantSymmetricJetTest r B g hB hg hn c η (hη.trans hKc) n := by
  apply Subtype.ext
  rfl

end Burnett.Microlocal.Overlap
