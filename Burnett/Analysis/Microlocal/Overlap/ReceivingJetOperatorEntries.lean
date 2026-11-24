import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetAmplitudeMeasure
import Burnett.Analysis.Microlocal.Overlap.UnitCosphereJetGram

/-! Local integrability of the original jet covariance as an operator. -/
set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 1500000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Geometry.IntrinsicScalarEinstein (covariantForm)
open Burnett.Geometry.InverseField (matrixInverse continuousOn_matrixInverse)
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection)
open Burnett.Geometry.FixedCotangentChart (inverseFrame)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity chartTangentBasis
  chartTangentBasis_apply)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold Matrix Kronecker

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- The inverse auxiliary metric in the fixed coordinate basis. -/
def atlasCovectorGram (r : Metric (M := M)) (c : AtlasChart M) (x : M) : Matrix Index Index ℂ :=
  Complex.ofRealHom.mapMatrix (matrixInverse (metricComponents (fixedForm r.inner c) (c.chart x)))

omit [SecondCountableTopology M] in
theorem atlasCovectorGram_in_fiber (r : Metric (M := M)) (c : AtlasChart M) (p : Cosphere r)
    (hp : projection p ∈ c.chart.source) :
    atlasCovectorGram r c (projection p) =
      unitCosphereCovectorGram r p (chartTangentBasis c (projection p) hp) := by
  let x := projection p
  have hMatrix : metricComponents (fixedForm r.inner c) (c.chart x) =
      FiberMetric.covariant (covariantForm r.inner x) (chartTangentBasis c x hp) := by
    funext i j
    have hx : x ∈ c.chart.source := hp
    simp only [metricComponents, FiberMetric.covariant, chartTangentBasis_apply, covariantForm,
      fixedForm, LinearMap.mk₂_apply, fixedCoordinateBilinear, inverseFrame]
    exact congrArg (fun y => r.inner y
      (mfderiv Model Model c.chart.symm (c.chart x) (coordinateBasis i))
      (mfderiv Model Model c.chart.symm (c.chart x) (coordinateBasis j))) (c.chart.left_inv hx)
  unfold atlasCovectorGram unitCosphereCovectorGram
  exact congrArg (fun H : Tensor2 => Complex.ofRealHom.mapMatrix (matrixInverse H)) hMatrix

theorem continuousOn_atlasCovectorGram_entry (r : Metric (M := M)) (c : AtlasChart M) (i j : Index) :
    ContinuousOn (fun x => atlasCovectorGram r c x i j) c.chart.source := by
  let H := metricComponents (fixedForm r.inner c)
  have hH : ContinuousOn H c.chart.target :=
    continuousOn_pi.mpr fun a => continuousOn_pi.mpr fun b =>
      (fixedForm_components_smooth r.inner (isSmooth_inner r) c a b).continuousOn
  have hInv := continuousOn_matrixInverse H c.chart.target hH
    (fun x hx => fixedForm_det_ne_zero r.inner (GlobalLeviCivita.inner_nondegenerate r) c hx)
  have hEntry := continuousOn_pi.mp (continuousOn_pi.mp hInv i) j
  exact (Complex.continuous_ofReal.comp_continuousOn hEntry).comp c.chart.continuousOn c.chart.mapsTo

/-- The chart entries of the density after raising its input indices with
the actual auxiliary Gram on the ordered jet slots. -/
def atlasJetCovarianceOperator {r : Metric (M := M)} (c : AtlasChart M)
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r) : Matrix JetSlot JetSlot ℂ :=
  let R := atlasCovectorGram r c (projection p)
  let C : Matrix JetSlot JetSlot ℂ := fun i j => atlasIntrinsicJetComponent c A p i j
  C * (R ⊗ₖ (R ⊗ₖ R))

omit [SecondCountableTopology M] in
theorem atlasJetCovarianceOperator_in_fiber {r : Metric (M := M)} (c : AtlasChart M)
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r) (hp : projection p ∈ c.chart.source) :
    let b := chartTangentBasis c (projection p) hp
    let R := unitCosphereCovectorGram r p b
    atlasJetCovarianceOperator c A p = jetAmplitudeComponents b (intrinsicJetAmplitude A p) * (R ⊗ₖ (R ⊗ₖ R)) := by
  intro b R
  simp only [atlasJetCovarianceOperator, atlasCovectorGram_in_fiber r c p hp]
  have hMatrix : ((fun i j => atlasIntrinsicJetComponent c A p i j) : Matrix JetSlot JetSlot ℂ) =
      jetAmplitudeComponents b (intrinsicJetAmplitude A p) := by
    ext i j
    rw [atlasIntrinsicJetComponent, dif_pos hp]
  rw [hMatrix]

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- Raising the input indices preserves local integrability of each jet
entry on every compact base window in the fixed chart. -/
theorem integrable_atlasJetCovarianceOperator_on_compact {r : Metric (M := M)}
    (c : AtlasChart M) (A : AmplitudeCovarianceDensity r) (μ : Measure (Cosphere r))
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ c.chart.source)
    (hA : ∀ i j : JetSlot, IntegrableOn (fun p => atlasIntrinsicJetComponent c A p i j)
      (amplitudeCosphereWindow r K) μ) (i j : JetSlot) :
    IntegrableOn (fun p => atlasJetCovarianceOperator c A p i j) (amplitudeCosphereWindow r K) μ := by
  let W := amplitudeCosphereWindow r K
  let H (x : M) : Matrix JetSlot JetSlot ℂ :=
    let R := atlasCovectorGram r c x
    R ⊗ₖ (R ⊗ₖ R)
  have hW : MeasurableSet W := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  change Integrable (fun p => atlasJetCovarianceOperator c A p i j) (μ.restrict W)
  simp only [atlasJetCovarianceOperator, Matrix.mul_apply]
  apply integrable_finset_sum
  intro k _
  have hC : ContinuousOn (fun x => H x k j) K := by
    change ContinuousOn (fun x => atlasCovectorGram r c x k.1 j.1 *
      (atlasCovectorGram r c x k.2.1 j.2.1 * atlasCovectorGram r c x k.2.2 j.2.2)) K
    exact ((continuousOn_atlasCovectorGram_entry r c k.1 j.1).mul
      ((continuousOn_atlasCovectorGram_entry r c k.2.1 j.2.1).mul
        (continuousOn_atlasCovectorGram_entry r c k.2.2 j.2.2))).mono hSub
  have hProj : ContinuousOn (fun p => H (projection p) k j) W :=
    hC.comp (continuous_projection r).continuousOn (fun _ hp => hp)
  obtain ⟨C, hCbound⟩ := (hK.image_of_continuousOn hC).isBounded.exists_norm_le
  have hBound : ∀ᵐ p ∂μ.restrict W, ‖H (projection p) k j‖ ≤ C :=
    (ae_restrict_mem (μ := μ) hW).mono fun p hp => hCbound _ (mem_image_of_mem _ hp)
  change Integrable (fun p : Cosphere r => atlasIntrinsicJetComponent c A p i k * H (projection p) k j)
    (μ.restrict W)
  exact ((hA i k).bdd_mul' (hProj.aemeasurable hW).aestronglyMeasurable hBound).congr
    (Filter.Eventually.of_forall fun p => mul_comm (H (projection p) k j) (atlasIntrinsicJetComponent c A p i k))

/-- On a compact chart window the original jet covariance endomorphisms
give one matrix-valued measure with all ordered entries on the same control. -/
theorem original_atlasJetCovarianceOperator_matrixMeasure_on_compact
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) {K : Set M} (hK : IsCompact K) (hSub : K ⊆ c.chart.source) :
    ∃ ν : VectorMeasure (Cosphere r) (JetSlot → JetSlot → ℂ),
      ∀ U : Set (Cosphere r), MeasurableSet U → ∀ i j : JetSlot,
        ν U i j = ∫ p in U, atlasJetCovarianceOperator c A.density p i j
          ∂(A.control.restrict (amplitudeCosphereWindow r K)) := by
  let ρ := A.control.restrict (amplitudeCosphereWindow r K)
  let F : Cosphere r → JetSlot → JetSlot → ℂ := atlasJetCovarianceOperator c A.density
  have hCov := (original_intrinsicJetAmplitude_positive_and_integrable r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA).2 c hK hSub
  have hEntries (i j : JetSlot) : Integrable (fun p => F p i j) ρ :=
    integrable_atlasJetCovarianceOperator_on_compact c A.density A.control hK hSub hCov i j
  let row (i : JetSlot) := ContinuousLinearMap.single ℝ (fun _ : JetSlot => JetSlot → ℂ) i
  let col (j : JetSlot) := ContinuousLinearMap.single ℝ (fun _ : JetSlot => ℂ) j
  have hF : Integrable F ρ := by
    have hSum : F = fun p => ∑ i : JetSlot, ∑ j : JetSlot, row i (col j (F p i j)) := by
      funext p
      symm
      calc
        _ = ∑ i : JetSlot, row i (F p i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact ContinuousLinearMap.sum_comp_single ℝ (fun _ : JetSlot => ℂ) (row i) (F p i)
        _ = F p := ContinuousLinearMap.sum_comp_single ℝ (fun _ : JetSlot => JetSlot → ℂ)
          (ContinuousLinearMap.id ℝ (JetSlot → JetSlot → ℂ)) (F p)
    rw [hSum]
    apply integrable_finset_sum
    intro i _
    apply integrable_finset_sum
    intro j _
    exact ((row i).comp (col j)).integrable_comp (hEntries i j)
  refine ⟨ρ.withDensityᵥ F, ?_⟩
  intro U hU i j
  rw [withDensityᵥ_apply hF hU]
  let evalCol : (JetSlot → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj j
  let evalRow : (JetSlot → JetSlot → ℂ) →L[ℝ] (JetSlot → ℂ) := ContinuousLinearMap.proj i
  let eval := evalCol.comp evalRow
  exact (eval.integral_comp_comm (μ := ρ.restrict U) hF.integrableOn).symm

end Burnett.Microlocal.Overlap
