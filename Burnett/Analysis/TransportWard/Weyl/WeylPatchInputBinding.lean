import Burnett.Analysis.TransportWard.Weyl.LocalizedWeylGradientInput
import Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousReceivingBridge

set_option autoImplicit false

noncomputable section

namespace Burnett.V03

open Set Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric
open ManifoldMetricSequence MaximalChart Burnett.RicciSymbol
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold

local notation "E₀" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M]

/-- The unprojected input in the actual Weyl pairing is the receiving-chart
fluctuation used in the cubic partition, with exactly the same cutoff. -/
theorem fixedWeylPerturbationSchwartz_eq_receivingCutoffFluctuation
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M)
    (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target) (n : ℕ) (i j : Index) :
    fixedWeylPerturbationSchwartz B g hB hg c χ hχ n (i,j) =
      Burnett.P01.receivingCutoffFluctuation B g hB hg c χ hχ n i j := by
  ext x
  rfl

end Burnett.V03
