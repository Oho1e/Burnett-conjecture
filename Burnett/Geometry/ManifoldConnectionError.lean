import Burnett.Geometry.ManifoldMetric
import Burnett.Geometry.MixedConnectionError

/-! The physical error consumer in the chart of a genuine smooth auxiliary
Riemannian metric. The remaining metric sequence and derivative data are
explicit coordinate fields; intrinsic connection naturality and global
volume identification are not assumed or claimed here. -/

noncomputable section

namespace Burnett.Geometry.ManifoldConnectionError

open Filter MeasureTheory
open scoped Topology ENNReal Manifold
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ConnectionError
open Burnett.Geometry.AuxiliaryConnection
open Burnett.Geometry.CovariantTensorNorm
open Burnett.Geometry.MixedTensorNorm
open Burnett.Geometry.ManifoldMetric

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model (↑(⊤ : ℕ∞)) M]

/-- Chart positivity and C1 regularity of the auxiliary metric are proved
from the actual smooth bundle metric, rather than supplied by the caller.
The physical derivative bound has the same local compact-set quantifiers. -/
theorem physicalError_in_chart_uniform_and_LInfinity
    (r : Metric (M := M)) (c : M) (K : Set CoordinateSpace)
    (hKU : K ⊆ (chartAt CoordinateSpace c).target) (hK : IsCompact K)
    (g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate)
    (hn : ∀ n x, x ∈ K → (g n x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm)
    (hs : ∀ n x, x ∈ K → ∀ᶠ y in 𝓝 x, (g n y).IsSymm)
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b)
      (chartAt CoordinateSpace c).target)
    (hc : ∀ n a b, ContDiffOn ℝ 1 (fun y => metricComponents (g n) y a b)
      (chartAt CoordinateSpace c).target)
    (hb : ∀ S : Set CoordinateSpace, IsCompact S → S ⊆ (chartAt CoordinateSpace c).target →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ n, eLpNorm
        (fun x => norm3 (metricComponents (coordinateMetric r c) x)
          (auxiliaryPerturbationJet (coordinateMetric r c) g₀ (g n) x))
        ∞ ((RiemannianVolume.metricMeasure (coordinateMetric r c)).restrict S) ≤ ENNReal.ofReal D)
    (hconv : TendstoUniformlyOn (fun n => metricComponents (g n)) (metricComponents g₀) atTop K) :
    (TendstoUniformlyOn (fun n x => mixedNorm (metricComponents (coordinateMetric r c) x)
      (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n) x)) (fun _ => 0) atTop K) ∧
    ∃ hf : ∀ n, MemLp (fun x => mixedNorm (metricComponents (coordinateMetric r c) x)
        (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n) x)) ∞
        ((RiemannianVolume.metricMeasure (coordinateMetric r c)).restrict K),
      Tendsto (fun n => (hf n).toLp (fun x => mixedNorm (metricComponents (coordinateMetric r c) x)
        (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n) x))) atTop (𝓝 0) := by
  exact MixedConnectionError.physicalError_uniform_and_LInfinity
    (chartAt CoordinateSpace c).target K (chartAt CoordinateSpace c).open_target hKU hK
    (coordinateMetric r c) g₀ g (contDiffOn_metricComponents_one r c)
    (fun x hx => coordinateMetric_posDef r c hx) hn₀ hn hs₀ hs hc₀ hc hb hconv

end Burnett.Geometry.ManifoldConnectionError
