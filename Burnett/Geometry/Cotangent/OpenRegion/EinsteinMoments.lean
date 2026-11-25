import Burnett.Geometry.Cotangent.OpenRegion.Curvature
import Burnett.Geometry.Cotangent.OpenRegion.LorentzVolume
import Burnett.Geometry.Cotangent.OpenRegion.TensorTests
import Burnett.Geometry.Cotangent.OpenRegion.CosphereMeasure
import Burnett.Analysis.Microlocal.Overlap.CosphereEinsteinMoments

set_option autoImplicit false
set_option maxHeartbeats 5300000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set MeasureTheory
open TopologicalSpace (Opens)
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.ContravariantTensor Burnett.Geometry.IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)

private theorem integrable_integral_of_restrict_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {e : X → Y} (he : MeasurableEmbedding e) {μ : Measure X} {ν : Measure Y} {V : Set Y}
    (hV : MeasurableSet V) (hMap : μ.map e = ν.restrict V) {f : Y → ℝ}
    (hi : Integrable f ν) (hz : ∀ p ∉ V, f p = 0) :
    Integrable (f ∘ e) μ ∧ (∫ p, f (e p) ∂μ) = ∫ p, f p ∂ν := by
  have hI := he.integral_map (μ := μ) f
  rw [hMap] at hI
  have hind : V.indicator f = f := by
    funext p
    by_cases hp : p ∈ V
    · exact indicator_of_mem hp f
    · rw [indicator_of_notMem hp, hz p hp]
  have hRest : Integrable f (μ.map e) := hMap.symm ▸ hi.mono_measure Measure.restrict_le_self
  refine ⟨he.integrable_map_iff.mp hRest, hI.symm.trans ?_⟩
  rw [← integral_indicator hV, hind]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- All Einstein tensor tests on an open submanifold are supplied by the
global moment identity for the same restricted ray measure. -/
theorem hasCosphereEinsteinMoments_openSubtype (U : Opens M) (r : Metric (M := M))
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (μ : Measure (Cosphere r)) (hMom : HasCosphereEinsteinMoments r g hn μ) :
    HasCosphereEinsteinMoments (restrictRiemannian U r) (restrictBilinear U g)
      (fun x => hn x.val) (cosphereMeasureOfOpen U r μ) := by
  intro Q hQ
  let Q₀ := extendContravariantTest U Q
  obtain ⟨hiBase, hiPhase, hPair⟩ := hMom Q₀ (extendContravariantTest_isTensorTest U Q hQ)
  let F := einsteinPair g hn Q₀
  let Ψ := fun p : Cosphere r => intrinsicTensorPhase Q₀ p.val
  let V : Set (Cosphere r) := projection ⁻¹' (U : Set M)
  have hV : MeasurableSet V := (U.isOpen.preimage (continuous_projection r)).measurableSet
  have hFzero (x : M) (hx : x ∉ U) : F x = 0 := by
    let b := tensorTangentBasis x x (mem_chart_source CoordinateSpace x)
    change contractAt x (Q₀ x) (intrinsicEinstein g hn x) = 0
    rw [show Q₀ x = 0 from dif_neg hx, contractAt_eq_sum x b]
    simp
  have hΨzero (p : Cosphere r) (hp : p ∉ V) : Ψ p = 0 := by
    change Q₀ p.val.1 p.val.2.toLinearMap p.val.2.toLinearMap = 0
    rw [show Q₀ p.val.1 = 0 from dif_neg hp]
    simp
  have hF (x : U) : F x.val = einsteinPair (restrictBilinear U g) (fun z => hn z.val) Q x := by
    change contractAt x.val (Q₀ x.val) (intrinsicEinstein g hn x.val) =
      contractAt x (Q x) (intrinsicEinstein (restrictBilinear U g) (fun z => hn z.val) x)
    have hQx : Q₀ x.val = Q x := extendContravariantTest_in_region U Q x
    rw [hQx]
    exact congrArg (contractAt x.val (Q x)) (intrinsicEinstein_openSubtype U g hg hn hs x).symm
  have hΨ (p : Cosphere (restrictRiemannian U r)) :
      Ψ (cosphereOpenVal U r p) = intrinsicTensorPhase Q p.val := by
    change intrinsicTensorPhase Q₀ (cotangentOpenVal U p.val) = _
    rw [intrinsicTensorPhase_extendContravariantTest U Q, extendCotangentTest_on_region]
  have e : MeasurableEmbedding (Subtype.val : U → M) := U.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  obtain ⟨hiF, hIF⟩ := integrable_integral_of_restrict_map e U.isOpen.measurableSet
    (geometricMeasure_openSubtype_map U g) hiBase hFzero
  obtain ⟨hiΨ, hIΨ⟩ := integrable_integral_of_restrict_map (cosphereOpenVal_isOpenEmbedding U r).measurableEmbedding
    hV (cosphereMeasureOfOpen_map U r μ) hiPhase hΨzero
  change Integrable (fun x : U => F x.val) _ at hiF
  change Integrable (fun p => Ψ (cosphereOpenVal U r p)) _ at hiΨ
  change (∫ x : U, F x.val ∂_) = _ at hIF
  change (∫ p : Cosphere (restrictRiemannian U r), Ψ (cosphereOpenVal U r p) ∂_) = _ at hIΨ
  simp_rw [hF] at hiF hIF
  simp_rw [hΨ] at hiΨ hIΨ
  exact ⟨hiF, hiΨ, hIF.trans (hPair.trans hIΨ.symm)⟩

end Burnett.Geometry.OpenRegion
