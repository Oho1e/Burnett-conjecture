import Burnett.Geometry.Cotangent.OpenRegion.CosphereMeasure
import Burnett.Geometry.Cotangent.OpenRegion.TestExtension
import Burnett.Geometry.Cotangent.CosphereNullInclusion

set_option autoImplicit false
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set MeasureTheory
open TopologicalSpace (Opens)
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.ActualTestLift
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian continuous_projection)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

attribute [local instance] unitNullMeasurable unitNullBorel

/-- Restrict the original unit-cosphere transport equation to every test
on an open submanifold using extension by zero. -/
theorem cosphereMeasureOfOpen_transport (U : Opens M) (r : Metric (M := M))
    (g : Field (M := M)) (μ : Measure (Cosphere r))
    (ht : ∀ a : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent →
      (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) →
      (∃ K : Set M, IsCompact K ∧ tsupport a ⊆ (fun p => p.1) ⁻¹' K) →
      (∫ p : Cosphere r, actualHamiltonDerivative g a p.val ∂μ) = 0)
    (a : CotangentBundle U → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    (hhom : ∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p)
    (hK : ∃ K : Set U, IsCompact K ∧ tsupport a ⊆ (fun p => p.1) ⁻¹' K) :
    (∫ p : Cosphere (restrictRiemannian U r),
      actualHamiltonDerivative (restrictBilinear U g) a p.val ∂cosphereMeasureOfOpen U r μ) = 0 := by
  obtain ⟨K, hK, hSupport⟩ := hK
  let A := extendCotangentTest U a
  let V : Set (Cosphere r) := projection ⁻¹' (U : Set M)
  let J := fun p : Cosphere r => actualHamiltonDerivative g A p.val
  have hEq : A ∘ cotangentOpenVal U = a := funext (extendCotangentTest_on_region U a)
  have hV : MeasurableSet V := (U.isOpen.preimage (continuous_projection r)).measurableSet
  have hCompact : IsCompact (Subtype.val '' K : Set M) := hK.image continuous_subtype_val
  have hSupp : tsupport A ⊆ (fun p => p.1) ⁻¹' (Subtype.val '' K : Set M) :=
    extendCotangentTest_support U a hK hSupport
  have hIndicator : V.indicator J = J := by
    funext p
    by_cases hp : p ∈ V
    · exact indicator_of_mem hp J
    · rw [indicator_of_notMem hp]
      apply (actualHamiltonDerivative_zero_off_closed_base g A hCompact.isClosed hSupp ?_).symm
      rintro ⟨x, _, hx⟩
      apply hp
      change p.val.1 ∈ U
      rw [← hx]
      exact x.property
  calc
    _ = ∫ p : Cosphere (restrictRiemannian U r),
        actualHamiltonDerivative (restrictBilinear U g) (A ∘ cotangentOpenVal U) p.val
          ∂cosphereMeasureOfOpen U r μ := by rw [hEq]
    _ = ∫ p in V, J p ∂μ := cosphereMeasureOfOpen_hamilton_integral U r g μ A
    _ = ∫ p, J p ∂μ := by rw [← integral_indicator hV, hIndicator]
    _ = 0 := ht A (extendCotangentTest_smooth U a ha hK hSupport)
      (extendCotangentTest_degreeOne U a hhom) ⟨_, hCompact, hSupp⟩

/-- The restricted unit-null input is transported and its pushforward back
to the ambient cosphere is exactly the restriction of the original measure. -/
theorem unitNullMeasureOfOpen_transport (U : Opens M) (r : Metric (M := M))
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (μ : Measure (Cosphere r)) [IsLocallyFiniteMeasure μ]
    (hNull : μ {p | hamiltonian g hn p ≠ 0} = 0)
    (ht : ∀ a : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent →
      (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) →
      (∃ K : Set M, IsCompact K ∧ tsupport a ⊆ (fun p => p.1) ⁻¹' K) →
      (∫ p : Cosphere r, actualHamiltonDerivative g a p.val ∂μ) = 0) :
    let rU := restrictRiemannian U r
    let gU := restrictBilinear U g
    let hnU : IsNondegenerate gU := fun p => hn p.val
    let μU := unitNullMeasureOfCosphere rU gU hnU (cosphereMeasureOfOpen U r μ)
    HasActualUnitTransport rU gU hnU μU ∧ IsLocallyFiniteMeasure μU ∧
      (μU.map (unitNullIntoCosphere rU gU hnU)).map (cosphereOpenVal U r) =
        μ.restrict (projection ⁻¹' (U : Set M)) := by
  intro rU gU hnU μU
  have hgU : IsSmooth gU := isSmooth_restrictBilinear U g hg
  have hsU : IsSymmetric gU := fun p => hs p.val
  have hNullU := cosphereMeasureOfOpen_offNull U r g hn hs μ hNull
  letI := cosphereMeasureOfOpen_locallyFinite U r μ
  refine ⟨unitNullMeasureOfCosphere_hasActualUnitTransport rU gU hgU hnU hsU
    (cosphereMeasureOfOpen U r μ) hNullU (fun a => cosphereMeasureOfOpen_transport U r g μ ht a),
    unitNullMeasureOfCosphere_locallyFinite rU gU hgU hnU hsU (cosphereMeasureOfOpen U r μ), ?_⟩
  change ((unitNullMeasureOfCosphere rU gU hnU (cosphereMeasureOfOpen U r μ)).map
    (unitNullIntoCosphere rU gU hnU)).map _ = _
  rw [unitNullMeasureOfCosphere_map rU gU hgU hnU hsU (cosphereMeasureOfOpen U r μ) hNullU,
    cosphereMeasureOfOpen_map U r μ]

end Burnett.Geometry.OpenRegion
