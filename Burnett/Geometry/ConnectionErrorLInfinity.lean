import Burnett.Geometry.AuxiliaryConnection
import Burnett.Analysis.UniformLInfinity
import Burnett.Analysis.LocalAeBound

/-! Continuity and the actual restricted L-infinity model for the coordinate
connection error. This file does not identify a manifold volume density or a
mixed physical auxiliary tensor norm. -/

noncomputable section

namespace Burnett.Geometry.ConnectionErrorLInfinity

open Filter MeasureTheory
open scoped Topology ENNReal
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ConnectionError
open Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.InverseField
open Burnett.Geometry.AuxiliaryConnection

def computedError
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) : Connection :=
  (computedConnection g₁ x - computedConnection g₀ x) -
    christoffel (matrixInverse (metricComponents g₀ x))
      (auxiliaryPerturbationJet g₀ g₀ g₁ x)

theorem computedError_eq_metricConnectionError
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hn₀ : (g₀ x).Nondegenerate) (hn₁ : (g₁ x).Nondegenerate)
    (hs₀ : (g₀ x).IsSymm) (hs₁ : (g₁ x).IsSymm) :
    computedError g₀ g₁ x = metricConnectionError g₀ g₁ x hn₀ hn₁ := by
  simp only [computedError, metricConnectionError, auxiliaryPerturbationJet,
    perturbationCovariantJet, computedConnection_eq_metricConnection _ _ hn₀ hs₀,
    computedConnection_eq_metricConnection _ _ hn₁ hs₁]
  rw [metricInverse, metricComponents,
    matrixInverse_covariant (g₀ x) hn₀ hs₀ coordinateBasis]

theorem continuousOn_computedError
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U)
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate) (hn₁ : ∀ x ∈ K, (g₁ x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, (g₀ x).IsSymm) (hs₁ : ∀ x ∈ K, (g₁ x).IsSymm)
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b) U)
    (hc₁ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₁ y a b) U) :
    ContinuousOn (computedError g₀ g₁) K := by
  have hΓ₀ := continuousOn_computedConnection g₀ U K hU hKU hc₀ hn₀ hs₀
  have hΓ₁ := continuousOn_computedConnection g₁ U K hU hKU hc₁ hn₁ hs₁
  have hi := continuousOn_inverseMetric g₀ coordinateBasis K
    ((continuousOn_components_of_contDiffOn _ U hc₀).mono hKU) hn₀ hs₀
  have hJ := continuousOn_auxiliaryPerturbationJet U K hU hKU g₀ g₀ g₁
    hc₀ hn₀ hs₀ hc₀ hc₁
  exact (hΓ₁.sub hΓ₀).sub (continuousOn_christoffel _ _ K hi hJ)

theorem continuousOn_metricConnectionErrorOn
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U)
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate) (hn₁ : ∀ x ∈ K, (g₁ x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, (g₀ x).IsSymm) (hs₁ : ∀ x ∈ K, (g₁ x).IsSymm)
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b) U)
    (hc₁ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₁ y a b) U) :
    ContinuousOn (metricConnectionErrorOn K g₀ g₁ hn₀ hn₁) K := by
  apply (continuousOn_computedError U K hU hKU g₀ g₁ hn₀ hn₁ hs₀ hs₁ hc₀ hc₁).congr
  intro x hx
  rw [metricConnectionErrorOn_of_mem _ _ _ _ _ hx]
  exact (computedError_eq_metricConnectionError g₀ g₁ x (hn₀ x hx) (hn₁ x hx)
    (hs₀ x hx) (hs₁ x hx)).symm

/-- Measurability and actual L-infinity membership of the represented
connection error follow from its real compact-range continuity. -/
theorem metricConnectionError_memLp_top
    (μ : Measure CoordinateSpace)
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate) (hn₁ : ∀ x ∈ K, (g₁ x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, (g₀ x).IsSymm) (hs₁ : ∀ x ∈ K, (g₁ x).IsSymm)
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b) U)
    (hc₁ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₁ y a b) U) :
    MemLp (metricConnectionErrorOn K g₀ g₁ hn₀ hn₁) ∞ (μ.restrict K) :=
  Burnett.Analysis.LocalAeBound.memLp_top_restrict_of_continuousOn_isCompact μ hK hK.measurableSet
    (continuousOn_metricConnectionErrorOn U K hU hKU g₀ g₁ hn₀ hn₁ hs₀ hs₁ hc₀ hc₁)

/-- The actual error representatives are constructed internally in L∞,
and uniform convergence implies their norm convergence. No MemLp premise
or choice of representatives is supplied by the caller. -/
theorem metricConnectionError_exists_tendstoLp
    (μ : Measure CoordinateSpace)
    (U K : Set CoordinateSpace) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate)
    (hn : ∀ n x, x ∈ K → (g n x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, (g₀ x).IsSymm) (hs : ∀ n x, x ∈ K → (g n x).IsSymm)
    (hc₀ : ∀ a b, ContDiffOn ℝ 1 (fun y => metricComponents g₀ y a b) U)
    (hc : ∀ n a b, ContDiffOn ℝ 1 (fun y => metricComponents (g n) y a b) U)
    (hu : TendstoUniformlyOn (fun n => metricConnectionErrorOn K g₀ (g n) hn₀ (hn n))
      (fun _ => 0) atTop K) :
    ∃ hf : ∀ n, MemLp (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n)) ∞ (μ.restrict K),
      Tendsto (fun n => (hf n).toLp (metricConnectionErrorOn K g₀ (g n) hn₀ (hn n)))
        atTop (𝓝 0) := by
  let hf := fun n => metricConnectionError_memLp_top μ U K hU hKU hK g₀ (g n)
    hn₀ (hn n) hs₀ (hs n) hc₀ (hc n)
  exact ⟨hf, Burnett.Analysis.tendsto_toLp_top_of_uniformlyOn_zero hK.measurableSet _ hf hu⟩

end Burnett.Geometry.ConnectionErrorLInfinity
