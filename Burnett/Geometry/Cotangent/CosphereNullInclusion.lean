import Burnett.Geometry.Cotangent.CosphereMeasure
import Burnett.Geometry.Cotangent.WeightedMomentumTransport

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.Geometry.ActualTestLift

open MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

attribute [local instance] unitNullMeasurable unitNullBorel

/-- The inclusion into the same auxiliary cosphere forgets only the nullity proof. -/
def unitNullIntoCosphere (r : Metric (M := M)) (g : Field (M := M)) (hn : IsNondegenerate g) :
    cotangentUnitNull r g hn → Cosphere r := Set.inclusion (fun _ hp => hp.1)

theorem unitNullIntoCosphere_range (r : Metric (M := M)) (g : Field (M := M)) (hn : IsNondegenerate g) :
    range (unitNullIntoCosphere r g hn) = {p : Cosphere r | hamiltonian g hn p = 0} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change dualEnergy g hn q.val / 2 = 0
    rw [q.property.2, zero_div]
  · intro hp
    have hnul : dualEnergy g hn p.val = 0 := (div_eq_zero_iff.mp hp).resolve_right (by norm_num)
    exact ⟨⟨p.val, p.property, hnul⟩, Subtype.ext rfl⟩

theorem unitNullIntoCosphere_isClosedEmbedding
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) :
    Topology.IsClosedEmbedding (unitNullIntoCosphere r g hn) := by
  exact Topology.IsClosedEmbedding.inclusion (fun _ hp => hp.1)
    ((isClosed_cotangentUnitNull r g hg hn hs).preimage continuous_subtype_val)

/-- Regard the original cosphere measure as a measure on its null support. -/
def unitNullMeasureOfCosphere (r : Metric (M := M)) (g : Field (M := M))
    (hn : IsNondegenerate g) (μ : Measure (Cosphere r)) : Measure (cotangentUnitNull r g hn) :=
  μ.comap (unitNullIntoCosphere r g hn)

theorem unitNullMeasureOfCosphere_map
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (μ : Measure (Cosphere r))
    (hNull : μ {p | hamiltonian g hn p ≠ 0} = 0) :
    (unitNullMeasureOfCosphere r g hn μ).map (unitNullIntoCosphere r g hn) = μ := by
  have hEmb := (unitNullIntoCosphere_isClosedEmbedding r g hg hn hs).measurableEmbedding
  rw [unitNullMeasureOfCosphere, hEmb.map_comap, unitNullIntoCosphere_range]
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hNull)

theorem unitNullMeasureOfCosphere_locallyFinite
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (μ : Measure (Cosphere r))
    [IsLocallyFiniteMeasure μ] : IsLocallyFiniteMeasure (unitNullMeasureOfCosphere r g hn μ) := by
  let L := unitNullIntoCosphere r g hn
  have h := unitNullIntoCosphere_isClosedEmbedding r g hg hn hs
  refine ⟨fun p => ?_⟩
  obtain ⟨U, hp, hU, hfin⟩ := μ.exists_isOpen_measure_lt_top (L p)
  refine ⟨L ⁻¹' U, (hU.preimage h.continuous).mem_nhds hp, ?_⟩
  rw [unitNullMeasureOfCosphere, h.measurableEmbedding.comap_apply]
  exact (measure_mono (image_preimage_subset _ _)).trans_lt hfin

/-- The same ordinary Hamilton integral agrees with the unit-null version
for every test. No extra measure is selected. -/
theorem unitNullMeasureOfCosphere_hamilton_integral
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (μ : Measure (Cosphere r))
    (hNull : μ {p | hamiltonian g hn p ≠ 0} = 0) (a : CotangentBundle M → ℝ) :
    (∫ p : cotangentUnitNull r g hn, actualHamiltonDerivative g a p.val ∂unitNullMeasureOfCosphere r g hn μ) =
      ∫ p : Cosphere r, actualHamiltonDerivative g a p.val ∂μ := by
  let F := fun p : Cosphere r => actualHamiltonDerivative g a p.val
  have hEmb := (unitNullIntoCosphere_isClosedEmbedding r g hg hn hs).measurableEmbedding
  have hI := hEmb.integral_map (μ := unitNullMeasureOfCosphere r g hn μ) F
  rw [unitNullMeasureOfCosphere_map r g hg hn hs μ hNull] at hI
  exact hI.symm

/-- Transport of the original cosphere measure supplies the exact null-section
transport input to the Cauchy lift. -/
theorem unitNullMeasureOfCosphere_hasActualUnitTransport
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (μ : Measure (Cosphere r))
    (hNull : μ {p | hamiltonian g hn p ≠ 0} = 0)
    (ht : ∀ a : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent →
      (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) →
      (∃ K : Set M, IsCompact K ∧ tsupport a ⊆ (fun p => p.1) ⁻¹' K) →
      (∫ p : Cosphere r, actualHamiltonDerivative g a p.val ∂μ) = 0) :
    HasActualUnitTransport r g hn (unitNullMeasureOfCosphere r g hn μ) := by
  intro a ha hhom hK
  rw [unitNullMeasureOfCosphere_hamilton_integral r g hg hn hs μ hNull a]
  exact ht a ha hhom hK

end Burnett.Geometry.ActualTestLift
