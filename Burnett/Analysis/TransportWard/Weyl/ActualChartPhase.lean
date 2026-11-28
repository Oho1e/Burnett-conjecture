import Burnett.Analysis.TransportWard.Weyl.OffNullPhaseCompression
import Burnett.Geometry.ManifoldLorentzSignature
import Burnett.Geometry.ManifoldVolumeRegularity

/-! Identify the coordinate phase inputs with the genuine manifold metric. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.V02

open Set Bundle Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open UnitNullCompactness
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Bianchi.RayIdentification (coordinateHamiltonian canonicalBracket)
open scoped BigOperators ComplexConjugate ContDiff Manifold

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The original lower metric components, with the actual chart frame. -/
def chartLowerMetric (B : Field (M := M)) (c : M) : E → Mat :=
  metricComponents (coordinateBilinear B c)

theorem chartLowerMetric_phase_inputs (B : Field (M := M)) (hB : IsSmooth B)
    (hn : IsNondegenerate B) (hs : IsSymmetric B) (c : M) :
    let U := (chartAt E c).target
    (∀ i j, ContDiffOn ℝ ∞ (fun x => chartLowerMetric B c x i j) U) ∧
      (∀ x ∈ U, Matrix.det (chartLowerMetric B c x) ≠ 0) ∧
      ∀ x ∈ U, IsSymmetricTensor (chartLowerMetric B c x) := by
  exact ⟨contDiffOn_metricComponents B hB c,
    fun _ hx => ManifoldVolumeRegularity.coordinate_det_ne_zero B hn c hx,
    fun x _ => FiberMetric.covariant_symmetric _
      (coordinateBilinear_symmetric B hs c x) coordinateBasis⟩

/-- The coordinate Hamiltonian uses one half of the actual contravariant
cotangent energy before any unit-section restriction. -/
theorem phaseHamiltonian_chartLowerMetric_eq_dualEnergy
    (B : Field (M := M)) (hn : IsNondegenerate B) (hs : IsSymmetric B)
    (c : M) (p : CotangentBundle M) (hp : p.proj ∈ (chartAt E c).source) :
    phaseHamiltonian (chartLowerMetric B c) (chartAt E c p.proj, cotangentCoords c p) =
      dualEnergy B hn p / 2 := by
  rw [dualEnergy_chart B hn hs c p hp]
  rfl

/-- The symbol weight is the same square root of the absolute determinant
used to define the geometric base volume in the chart. -/
theorem phaseDensity_chartLowerMetric_eq_coordinateDensity
    (B : Field (M := M)) (c : M) (z : Phase) :
    ENNReal.ofReal (phaseDensity (chartLowerMetric B c) z) =
      LorentzVolume.density (chartLowerMetric B c) z.1 := rfl

/-- At an actual nonzero cotangent point of the smooth Lorentz metric,
the same mixed bracket has its physical null value and vanishes off the cone. -/
theorem phaseEinsteinPoissonBracket_actualChart_RicciKernel
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : M) (p : CotangentBundle M) (hp : p.proj ∈ (chartAt E c).source)
    (hξ : cotangentCoords c p ≠ 0) (k l : ComplexTensor2) (hl : IsSymmetricComplexTensor l)
    (hkR : ∀ i j, complexRicciSymbol
      (phaseInverse (chartLowerMetric B c) (chartAt E c p.proj, cotangentCoords c p))
      (cotangentCoords c p) k i j = 0)
    (hlR : ∀ i j, complexRicciSymbol
      (phaseInverse (chartLowerMetric B c) (chartAt E c p.proj, cotangentCoords c p))
      (cotangentCoords c p) l i j = 0)
    (a : E → Covector → ℝ) :
    let g := chartLowerMetric B c
    let z : Phase := (chartAt E c p.proj, cotangentCoords c p)
    (∑ i, ∑ j, phaseEinsteinPoissonBracket g k a z i j * conj (l i j)) =
      if dualEnergy B hSig.isNondegenerate p = 0 then
        4 * (phaseDensity g z : ℂ) * (canonicalBracket (coordinateHamiltonian g) a z.1 z.2 : ℂ) *
          physicalForm (phaseInverse g z) k l
      else 0 := by
  intro g z
  let e := chartAt E c
  have hz : z.1 ∈ e.target := e.mapsTo hp
  obtain ⟨hG, hDet, hS⟩ := chartLowerMetric_phase_inputs B hB hSig.isNondegenerate hSig.isSymmetric c
  have hEnergy : symbolNorm (phaseInverse g z) z.2 = dualEnergy B hSig.isNondegenerate p :=
    (dualEnergy_chart B hSig.isNondegenerate hSig.isSymmetric c p hp).symm
  by_cases hNull : dualEnergy B hSig.isNondegenerate p = 0
  · rw [if_pos hNull]
    exact phaseEinsteinPoissonBracket_nullRicciKernel g e.target e.open_target hG hDet hS
      z hz hξ (hEnergy.trans hNull) k l hl hkR hlR a
  · rw [if_neg hNull]
    exact phaseEinsteinPoissonBracket_offNullRicciKernel g e.target e.open_target hG hDet hS
      z hz (fun h => hNull (hEnergy.symm.trans h)) k l hkR hlR a

end Burnett.V02
