import Burnett.Geometry.Cotangent.SmoothExtension
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Maps.Proper.Basic

/-! The unit cosphere and the measure induced by a concentrated ambient measure. -/

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.UnitCosphere

open MeasureTheory Set Topology
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric
open Burnett.Geometry.UnitNullCompactness (CotangentBundle dualEnergy cotangentUnitNull
  continuous_cotangent_projection)
open Burnett.Geometry.CotangentAngularExtension (contMDiff_dualEnergy)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The full auxiliary unit section of the actual cotangent bundle. -/
def unitCosphere (r : Metric (M := M)) : Set (CotangentBundle M) :=
  {p | dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p = 1}

abbrev Cosphere (r : Metric (M := M)) := ↥(unitCosphere r)

instance cosphereMeasurableSpace (r : Metric (M := M)) : MeasurableSpace (Cosphere r) := borel _

instance cosphereBorelSpace (r : Metric (M := M)) : BorelSpace (Cosphere r) := ⟨rfl⟩

def projection {r : Metric (M := M)} (p : Cosphere r) : M := p.val.proj

theorem continuous_projection (r : Metric (M := M)) : Continuous (projection (r := r)) :=
  continuous_cotangent_projection.comp continuous_subtype_val

theorem isClosed_unitCosphere (r : Metric (M := M)) : IsClosed (unitCosphere r) :=
  isClosed_eq ((contMDiff_dualEnergy r.inner (isSmooth_inner r)
    (GlobalLeviCivita.inner_nondegenerate r) r.symm).continuous) continuous_const

/-- The background null Hamiltonian, evaluated on the unit section. -/
def hamiltonian {r : Metric (M := M)} (B : Field (M := M)) (hn : IsNondegenerate B)
    (p : Cosphere r) : ℝ :=
  dualEnergy B hn p.val / 2

variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

theorem measurableEmbedding_coe (r : Metric (M := M)) :
    MeasurableEmbedding (Subtype.val : Cosphere r → CotangentBundle M) := by
  have hspace : cosphereMeasurableSpace r =
      (inferInstance : MeasurableSpace (CotangentBundle M)).comap
        (Subtype.val : Cosphere r → CotangentBundle M) := by
    change borel (Cosphere r) = _
    rw [BorelSpace.measurable_eq (α := CotangentBundle M)]
    exact borel_comap
  change @MeasurableEmbedding (Cosphere r) (CotangentBundle M)
    (cosphereMeasurableSpace r) _ Subtype.val
  rw [hspace]
  exact MeasurableEmbedding.subtype_coe (isClosed_unitCosphere r).measurableSet

/-- Pull back the ambient measure along the unit-section inclusion. -/
def fromAmbient (r : Metric (M := M)) (μ : Measure (CotangentBundle M)) : Measure (Cosphere r) :=
  μ.comap Subtype.val

theorem map_fromAmbient (r : Metric (M := M)) (μ : Measure (CotangentBundle M)) :
    (fromAmbient r μ).map Subtype.val = μ.restrict (unitCosphere r) := by
  rw [fromAmbient, (measurableEmbedding_coe r).map_comap, Subtype.range_coe]

theorem map_fromAmbient_eq_of_unitNull (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (μ : Measure (CotangentBundle M))
    (hμ : μ (cotangentUnitNull r B hn)ᶜ = 0) :
    (fromAmbient r μ).map Subtype.val = μ := by
  rw [map_fromAmbient]
  apply Measure.restrict_eq_self_of_ae_mem
  have hsubset : cotangentUnitNull r B hn ⊆ unitCosphere r := fun _ hp => hp.1
  exact ae_iff.mpr (measure_mono_null (compl_subset_compl.mpr hsubset) hμ)

theorem fromAmbient_locallyFinite (r : Metric (M := M)) (μ : Measure (CotangentBundle M))
    [IsLocallyFiniteMeasure μ] : IsLocallyFiniteMeasure (fromAmbient r μ) := by
  refine ⟨fun p => ?_⟩
  obtain ⟨U, hp, hU, hfinite⟩ := μ.exists_isOpen_measure_lt_top p.val
  refine ⟨Subtype.val ⁻¹' U, (hU.preimage continuous_subtype_val).mem_nhds hp, ?_⟩
  rw [fromAmbient, (measurableEmbedding_coe r).comap_apply]
  exact (measure_mono (image_preimage_subset _ _)).trans_lt hfinite

/-- Regularity passes through the closed inclusion when its image carries the ambient measure. -/
theorem fromAmbient_regular (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (μ : Measure (CotangentBundle M)) [μ.Regular]
    (hμ : μ (cotangentUnitNull r B hn)ᶜ = 0) : (fromAmbient r μ).Regular := by
  have hclosed : IsClosedEmbedding (Subtype.val : Cosphere r → CotangentBundle M) :=
    (isClosed_unitCosphere r).isClosedEmbedding_subtypeVal
  have hme := measurableEmbedding_coe r
  have happly (V : Set (CotangentBundle M)) : fromAmbient r μ (Subtype.val ⁻¹' V) = μ V := by
    rw [← hme.map_apply, map_fromAmbient_eq_of_unitNull r B hn μ hμ]
  letI : (fromAmbient r μ).OuterRegular := Measure.OuterRegular.comap' μ hclosed.continuous hme
  letI : IsFiniteMeasureOnCompacts (fromAmbient r μ) :=
    IsFiniteMeasureOnCompacts.comap' μ hclosed.continuous hme
  refine ⟨?_⟩
  intro U hU t ht
  obtain ⟨V, hV, hVU⟩ := hclosed.isInducing.isOpen_iff.mp hU
  have htV : t < μ V := by rwa [← hVU, happly] at ht
  obtain ⟨K, hKV, hK, htK⟩ := hV.exists_lt_isCompact htV
  refine ⟨Subtype.val ⁻¹' K, hVU ▸ preimage_mono hKV, hclosed.isProperMap.isCompact_preimage hK, ?_⟩
  rwa [happly]

theorem fromAmbient_finiteOnCompactBase (r : Metric (M := M)) (μ : Measure (CotangentBundle M))
    (hfinite : ∀ K : Set M, IsCompact K → μ ((fun p : CotangentBundle M => p.proj) ⁻¹' K) < ⊤)
    (K : Set M) (hK : IsCompact K) : fromAmbient r μ (projection ⁻¹' K) < ⊤ := by
  rw [fromAmbient, (measurableEmbedding_coe r).comap_apply]
  refine (measure_mono ?_).trans_lt (hfinite K hK)
  rintro _ ⟨p, hp, rfl⟩
  exact hp

theorem fromAmbient_offNull (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (μ : Measure (CotangentBundle M))
    (hμ : μ (cotangentUnitNull r B hn)ᶜ = 0) :
    fromAmbient r μ {p | hamiltonian B hn p ≠ 0} = 0 := by
  rw [fromAmbient, (measurableEmbedding_coe r).comap_apply]
  refine measure_mono_null ?_ hμ
  rintro _ ⟨p, hp, rfl⟩ hNull
  exact hp (by simp [hamiltonian, hNull.2])

end Burnett.Geometry.UnitCosphere
