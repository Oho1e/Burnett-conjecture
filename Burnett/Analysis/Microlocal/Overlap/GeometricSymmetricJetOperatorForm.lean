import Burnett.Analysis.Microlocal.Overlap.SymmetricJetKernelGram
import Burnett.Analysis.Microlocal.Overlap.SymmetricJetSeparatedChartPairing
import Burnett.Analysis.Microlocal.Overlap.ReceivingJetOperatorEntries

/-! Physical-volume pairing of a single linear operator on true bundle tests. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 6500000
set_option synthInstance.maxHeartbeats 410000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Filter Matrix MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped BigOperators ComplexConjugate ContDiff Manifold Matrix Kronecker Topology

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- The entries of the intrinsic Gram in any fixed receiving chart. -/
theorem continuousOn_atlasJetGram_entry (r : Metric (M := M)) (c : AtlasChart M) (i j : JetSlot) :
    ContinuousOn (fun p => atlasJetGram r c p i j) c.chart.source := by
  change ContinuousOn (fun p => atlasCovectorGram r c p i.1 j.1 *
    (atlasCovectorGram r c p i.2.1 j.2.1 * atlasCovectorGram r c p i.2.2 j.2.2)) c.chart.source
  exact (continuousOn_atlasCovectorGram_entry r c i.1 j.1).mul
    ((continuousOn_atlasCovectorGram_entry r c i.2.1 j.2.1).mul
      (continuousOn_atlasCovectorGram_entry r c i.2.2 j.2.2))

omit [SecondCountableTopology M] in
theorem symmetricJetFiberGram_section_eq_components (r : Metric (M := M)) (c : AtlasChart M)
    (v u : SymmetricJetSection M) (p : M) (hp : p ∈ c.chart.source) :
    symmetricJetFiberGram r p (v p) (u p) =
      ∑ i, conj (symmetricJetComponent c v i p) *
        (∑ j, atlasJetGram r c p i j * symmetricJetComponent c u j p) := by
  rw [symmetricJetFiberGram_in_chart r p c hp]
  simp only [symmetricJetComponent_of_mem c _ _ p hp, Matrix.mulVec, dotProduct, Pi.star_apply, Complex.star_def]

/-- The intrinsic pointwise scalar pairing of smooth sections is continuous,
even though the preferred frame used in its definition varies with the point. -/
theorem continuous_symmetricJetFiberGram_sections (r : Metric (M := M))
    (v u : SymmetricJetSection M) (hv : IsSmoothSymmetricJetSection v) (hu : IsSmoothSymmetricJetSection u) :
    Continuous (fun p => symmetricJetFiberGram r p (v p) (u p)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let c := AtlasChart.atPoint p
  have hp : p ∈ c.chart.source := mem_chart_source E p
  have hC : ContinuousOn (fun x => ∑ i, conj (symmetricJetComponent c v i x) *
      (∑ j, atlasJetGram r c x i j * symmetricJetComponent c u j x)) c.chart.source := by
    refine continuousOn_finset_sum _ fun i _ => ?_
    refine (Complex.continuous_conj.comp_continuousOn
      (continuousOn_symmetricJetComponent c v hv i)).mul ?_
    exact continuousOn_finset_sum _ fun j _ => (continuousOn_atlasJetGram_entry r c i j).mul
      (continuousOn_symmetricJetComponent c u hu j)
  exact (hC.congr fun x hx => symmetricJetFiberGram_section_eq_components r c v u x hx).continuousAt
    (c.chart.open_source.mem_nhds hp)

variable [T2Space M] [MeasurableSpace M] [BorelSpace M]

theorem integrable_symmetricJetFiberGram_compactLeft (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (v : smoothCompactSymmetricJet M) (u : SymmetricJetSection M)
    (hu : IsSmoothSymmetricJetSection u) :
    Integrable (fun p => symmetricJetFiberGram r p (v.val p) (u p))
      (ManifoldVolume.geometricMeasure B) := by
  let μ := ManifoldVolume.geometricMeasure B
  letI : IsLocallyFiniteMeasure μ := ManifoldVolumeRegularity.geometricMeasure_isLocallyFiniteMeasure B hB
  let f (p : M) := symmetricJetFiberGram r p (v.val p) (u p)
  obtain ⟨S, hS, hv⟩ := v.property.2
  have hSupp : support f ⊆ S := by
    intro p hp
    apply hv
    intro hZero
    exact hp (by simp [f, hZero])
  have hCompact : HasCompactSupport f :=
    hS.of_isClosed_subset isClosed_closure (closure_minimal hSupp hS.isClosed)
  exact (continuous_symmetricJetFiberGram_sections r v.val u v.property.1 hu).integrable_of_hasCompactSupport hCompact

/-- The global form is the actual integral of the metric pairing against
the output of the given operator. Only the left test has to give compact
support to the integrand. -/
def geometricSymmetricJetOperatorForm (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (A : smoothCompactSymmetricJet M →ₗ[ℂ] SymmetricJetSection M)
    (hA : ∀ u, IsSmoothSymmetricJetSection (A u)) : SymmetricJetGlobalForm M := by
  let F (v u : smoothCompactSymmetricJet M) (p : M) := symmetricJetFiberGram r p (v.val p) (A u p)
  have hInt (v u : smoothCompactSymmetricJet M) : Integrable (F v u) (ManifoldVolume.geometricMeasure B) :=
    integrable_symmetricJetFiberGram_compactLeft r B hB v (A u) (hA u)
  refine {
    toFun := fun v => {
      toFun := fun u => ∫ p, F v u p ∂ManifoldVolume.geometricMeasure B
      map_add' := fun u w => ?_
      map_smul' := fun a u => ?_ }
    map_add' := fun v w => ?_
    map_smul' := fun a v => ?_ }
  · rw [← integral_add (hInt v u) (hInt v w)]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by simp only [F, map_add, Pi.add_apply]
  · simp only [F, map_smul, Pi.smul_apply, integral_smul, RingHom.id_apply]
  · ext u
    change (∫ p, F (v + w) u p ∂ManifoldVolume.geometricMeasure B) =
      (∫ p, F v u p ∂ManifoldVolume.geometricMeasure B) + ∫ p, F w u p ∂ManifoldVolume.geometricMeasure B
    rw [← integral_add (hInt v u) (hInt w u)]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by simp only [F, Submodule.coe_add, Pi.add_apply, map_add, LinearMap.add_apply]
  · ext u
    change (∫ p, F (a • v) u p ∂ManifoldVolume.geometricMeasure B) =
      starRingEnd ℂ a • ∫ p, F v u p ∂ManifoldVolume.geometricMeasure B
    simp only [F, Submodule.coe_smul, Pi.smul_apply, map_smulₛₗ, LinearMap.smul_apply, integral_smul]

/-- A pointwise off-diagonal kernel formula suffices for the exact integrated
separated-support identity of the actual operator form. -/
theorem geometricSymmetricJetOperatorForm_hasSeparatedKernel
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B)
    (A : smoothCompactSymmetricJet M →ₗ[ℂ] SymmetricJetSection M) (hA : ∀ u, IsSmoothSymmetricJetSection (A u))
    (K : SymmetricJetLinearKernel M)
    (hKernel : ∀ (T : Set M), IsCompact T → ∀ (u : smoothCompactSymmetricJet M),
      symmetricJetSectionSupport u.val ⊆ T → ∀ p ∉ T, ∀ v : SymmetricJetFiber M p,
        symmetricJetFiberGram r p v (A u p) =
          ∫ q in T, pairSymmetricJetLinearKernel r K p q v (u.val q) ∂ManifoldVolume.geometricMeasure B) :
    HasSeparatedSymmetricJetKernel (ManifoldVolume.geometricMeasure B)
      (geometricSymmetricJetOperatorForm r B hB A hA) (pairSymmetricJetLinearKernel r K) := by
  intro S T hS hT hST v u hv hu
  let μ := ManifoldVolume.geometricMeasure B
  let f (p : M) := symmetricJetFiberGram r p (v.val p) (A u p)
  change (∫ p, f p ∂μ) = ∫ p in S, ∫ q in T, pairSymmetricJetLinearKernel r K p q (v.val p) (u.val q) ∂μ ∂μ
  have hSupp : support f ⊆ S := by
    intro p hp
    apply hv
    intro hZero
    exact hp (by simp [f, hZero])
  calc
    _ = ∫ p in S, f p ∂μ := by
      rw [← integral_indicator hS.measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        by_cases hp : p ∈ S
        · rw [indicator_of_mem hp]
        · rw [indicator_of_notMem hp, notMem_support.mp (fun h => hp (hSupp h))]
    _ = _ := setIntegral_congr_fun hS.measurableSet fun p hp =>
      hKernel T hT u hu p (fun h => (Set.disjoint_left.mp hST) hp h) (v.val p)

end Burnett.Microlocal.Overlap
