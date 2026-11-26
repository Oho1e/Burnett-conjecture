import Burnett.Geometry.Cotangent.OpenRegion.Hamilton
import Burnett.Geometry.Cotangent.OpenRegion.CotangentHomeomorph
import Burnett.Geometry.Cotangent.CosphereMeasure

set_option autoImplicit false
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set MeasureTheory
open TopologicalSpace (Opens)
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian continuous_projection)
open Burnett.Geometry.ActualTestLift

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem dualEnergy_restrictRiemannian (U : Opens M) (r : Metric (M := M)) (p : CotangentBundle U) :
    dualEnergy (restrictRiemannian U r).inner (Burnett.Geometry.GlobalLeviCivita.inner_nondegenerate _) p =
      dualEnergy r.inner (Burnett.Geometry.GlobalLeviCivita.inner_nondegenerate r) (cotangentOpenVal U p) :=
  dualEnergy_openSubtype U r.inner (Burnett.Geometry.GlobalLeviCivita.inner_nondegenerate r) r.symm p

/-- The auxiliary unit section restricts using unchanged covectors and norm. -/
def cosphereOpenVal (U : Opens M) (r : Metric (M := M)) : Cosphere (restrictRiemannian U r) → Cosphere r :=
  fun p => ⟨cotangentOpenVal U p.val, (dualEnergy_restrictRiemannian U r p.val).symm.trans p.property⟩

theorem cosphereOpenVal_range (U : Opens M) (r : Metric (M := M)) :
    range (cosphereOpenVal U r) = (projection (r := r)) ⁻¹' (U : Set M) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.val.1.property
  · intro hp
    let e := cotangentOpenHomeomorph U
    let q := e.symm ⟨p.val, hp⟩
    have hq : cotangentOpenVal U q = p.val :=
      congrArg (fun z : cotangentOver U => z.val) (e.apply_symm_apply ⟨p.val, hp⟩)
    have hz : q ∈ Burnett.Geometry.UnitCosphere.unitCosphere (restrictRiemannian U r) := by
      change dualEnergy (restrictRiemannian U r).inner (Burnett.Geometry.GlobalLeviCivita.inner_nondegenerate _) q = 1
      rw [dualEnergy_restrictRiemannian U r q, hq]
      exact p.property
    exact ⟨⟨q, hz⟩, Subtype.ext hq⟩

theorem cosphereOpenVal_isOpenEmbedding (U : Opens M) (r : Metric (M := M)) :
    Topology.IsOpenEmbedding (cosphereOpenVal U r) := by
  have hcont : Continuous (cosphereOpenVal U r) :=
    ((contMDiff_cotangentOpenVal U).continuous.comp continuous_subtype_val).subtype_mk _
  refine ⟨Topology.IsEmbedding.of_comp hcont continuous_subtype_val ?_, ?_⟩
  · exact (cotangentOpenVal_isOpenEmbedding U).isEmbedding.comp Topology.IsEmbedding.subtypeVal
  · rw [cosphereOpenVal_range]
    exact U.isOpen.preimage (continuous_projection r)

/-- The open-region measure is the pullback of the original cosphere measure
along the actual unit-section inclusion. -/
def cosphereMeasureOfOpen (U : Opens M) (r : Metric (M := M)) (μ : Measure (Cosphere r)) :
    Measure (Cosphere (restrictRiemannian U r)) := μ.comap (cosphereOpenVal U r)

theorem cosphereMeasureOfOpen_map (U : Opens M) (r : Metric (M := M)) (μ : Measure (Cosphere r)) :
    (cosphereMeasureOfOpen U r μ).map (cosphereOpenVal U r) = μ.restrict (projection ⁻¹' (U : Set M)) := by
  rw [cosphereMeasureOfOpen, (cosphereOpenVal_isOpenEmbedding U r).measurableEmbedding.map_comap,
    cosphereOpenVal_range]

theorem cosphereMeasureOfOpen_locallyFinite (U : Opens M) (r : Metric (M := M)) (μ : Measure (Cosphere r))
    [IsLocallyFiniteMeasure μ] : IsLocallyFiniteMeasure (cosphereMeasureOfOpen U r μ) := by
  let L := cosphereOpenVal U r
  have h := cosphereOpenVal_isOpenEmbedding U r
  refine ⟨fun p => ?_⟩
  obtain ⟨V, hp, hV, hfin⟩ := μ.exists_isOpen_measure_lt_top (L p)
  refine ⟨L ⁻¹' V, (hV.preimage h.continuous).mem_nhds hp, ?_⟩
  rw [cosphereMeasureOfOpen, h.measurableEmbedding.comap_apply]
  exact (measure_mono (image_preimage_subset _ _)).trans_lt hfin

theorem cosphereMeasureOfOpen_offNull (U : Opens M) (r : Metric (M := M))
    (g : Field (M := M)) (hn : IsNondegenerate g) (hs : IsSymmetric g) (μ : Measure (Cosphere r))
    (hNull : μ {p | hamiltonian g hn p ≠ 0} = 0) :
    cosphereMeasureOfOpen U r μ {p | hamiltonian (restrictBilinear U g) (fun x => hn x.val) p ≠ 0} = 0 := by
  rw [cosphereMeasureOfOpen, (cosphereOpenVal_isOpenEmbedding U r).measurableEmbedding.comap_apply]
  apply measure_mono_null _ hNull
  rintro _ ⟨p, hp, rfl⟩
  change dualEnergy g hn (cotangentOpenVal U p.val) / 2 ≠ 0
  rw [← dualEnergy_openSubtype U g hn hs p.val]
  exact hp

/-- The Hamilton integral against the restricted cosphere measure is exactly
the original integral over the region for each ambient test. -/
theorem cosphereMeasureOfOpen_hamilton_integral (U : Opens M) (r : Metric (M := M))
    (g : Field (M := M)) (μ : Measure (Cosphere r)) (a : CotangentBundle M → ℝ) :
    (∫ p : Cosphere (restrictRiemannian U r),
        actualHamiltonDerivative (restrictBilinear U g) (a ∘ cotangentOpenVal U) p.val
          ∂cosphereMeasureOfOpen U r μ) =
      ∫ p in projection ⁻¹' (U : Set M), actualHamiltonDerivative g a p.val ∂μ := by
  let F := fun p : Cosphere r => actualHamiltonDerivative g a p.val
  have hEmb := (cosphereOpenVal_isOpenEmbedding U r).measurableEmbedding
  have hI := hEmb.integral_map (μ := cosphereMeasureOfOpen U r μ) F
  rw [cosphereMeasureOfOpen_map U r μ] at hI
  simp_rw [actualHamiltonDerivative_openSubtype]
  exact hI.symm

end Burnett.Geometry.OpenRegion
