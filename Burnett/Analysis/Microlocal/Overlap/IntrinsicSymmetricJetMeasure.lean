import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetSymmetricProjection
import Burnett.Analysis.Microlocal.Overlap.ReceivingJetTraceMeasure
import Burnett.Analysis.Microlocal.Overlap.AtlasJetOperatorMeasureNaturality

/-! One intrinsic symmetric jet density and its locally finite measure. -/
set_option autoImplicit false
set_option maxRecDepth 4700
set_option maxHeartbeats 3200000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Module Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity chartTangentBasis components)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ComplexOrder ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- A section of the symmetric jet endomorphisms over the auxiliary unit cosphere. -/
abbrev SymmetricJetEndomorphismField (r : Metric (M := M)) :=
  ∀ p : Cosphere r, End ℂ (complexSymmetricJet (TangentSpace Model (projection p)))

/-- Local entries use the symmetric endomorphism extended by the canonical
projection on ordered jets. These entries incorporate the off-diagonal multiplicities. -/
def atlasSymmetricJetEntries {r : Metric (M := M)} (c : AtlasChart M)
    (D : SymmetricJetEndomorphismField r) (p : Cosphere r) : Matrix JetSlot JetSlot ℂ := by
  classical
  exact if hp : projection p ∈ c.chart.source then
    let V := TangentSpace Model (projection p)
    let W := jetFiberCoordinates (chartTangentBasis c (projection p) hp)
    LinearMap.toMatrix' (W.toLinearMap.comp ((complexSymmetricJet V).subtype.comp
      ((D p).comp ((projectComplexSymmetricJet V).comp W.symm.toLinearMap))))
  else 0

theorem atlasSymmetricJetEntries_original {r : Metric (M := M)} {B : Field (M := M)} {hn : IsNondegenerate B}
    {A : AmplitudeCovarianceDensity r} {p : Cosphere r} (c : AtlasChart M) (hc : projection p ∈ c.chart.source)
    (hR : HasIntrinsicAmplitudeRicciKernel r B hn A p)
    (hP : ∀ b : Basis Index ℝ (TangentSpace Model (projection p)), (components b (A p)).PosSemidef) :
    atlasSymmetricJetEntries c (intrinsicSymmetricJetCovariance A) p = atlasJetCovarianceOperator c A p := by
  rw [atlasSymmetricJetEntries, dif_pos hc]
  let V := TangentSpace Model (projection p)
  let W := jetFiberCoordinates (chartTangentBasis c (projection p) hc)
  have hMap : W.toLinearMap.comp ((complexSymmetricJet V).subtype.comp
      ((intrinsicSymmetricJetCovariance A p).comp ((projectComplexSymmetricJet V).comp W.symm.toLinearMap))) =
      Matrix.mulVecLin (atlasJetCovarianceOperator c A p) := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    calc
      _ = W (intrinsicJetCovarianceEndomorphism A p (W.symm z)) :=
        congrArg W (intrinsicSymmetricJetCovariance_extension hR hP (W.symm z))
      _ = atlasJetCovarianceOperator c A p *ᵥ z := by
        have he := intrinsicJetCovarianceEndomorphism_coordinates A p c hc (W.symm z)
        change W (intrinsicJetCovarianceEndomorphism A p (W.symm z)) = _ at he
        rw [he, W.apply_symm_apply]
  exact (congrArg LinearMap.toMatrix' hMap).trans (LinearMap.toMatrix'_toLin' _)

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [SecondCountableTopology M]

/-- A positive Hermitian bundle-valued measure is represented by one Radon
control and a section of the actual symmetric endomorphism fibers. Over each
compact chart window the section is entrywise integrable and yields a countably
additive matrix measure, with the same scalar trace on every Borel set. -/
def HasIntrinsicSymmetricJetMeasure {r : Metric (M := M)} (τ : Measure (Cosphere r))
    (D : SymmetricJetEndomorphismField r) : Prop :=
  IsLocallyFiniteMeasure τ ∧ τ.Regular ∧ (∀ K : Set M, IsCompact K → τ (projection ⁻¹' K) < ⊤) ∧
  ∀ (c : AtlasChart M) {K : Set M}, IsCompact K → K ⊆ c.chart.source →
    let ρ := τ.restrict (amplitudeCosphereWindow r K)
    (∀ i j : JetSlot, Integrable (fun p => atlasSymmetricJetEntries c D p i j) ρ) ∧
    (∀ᵐ p ∂ρ,
      let H := atlasJetGram r c (projection p)
      let O := atlasSymmetricJetEntries c D p
      (H * O).PosSemidef ∧ Oᴴ * H = H * O ∧ O.trace.re = 1) ∧
    ∃ ν : VectorMeasure (Cosphere r) (JetSlot → JetSlot → ℂ),
      ∀ U : Set (Cosphere r), MeasurableSet U →
        (∀ i j : JetSlot, ν U i j = ∫ p in U, atlasSymmetricJetEntries c D p i j ∂ρ) ∧
        (Matrix.trace (ν U : Matrix JetSlot JetSlot ℂ)).re = ρ.real U

omit [SecondCountableTopology M] in
theorem ae_atlasSymmetricJetEntries_original_on_compact
    {r : Metric (M := M)} {B : Field (M := M)} {g : ℕ → Field (M := M)}
    {hB : IsSmooth B} {hg : ∀ n, IsSmooth (g n)} {hn : IsNondegenerate B}
    {σ : ℕ → ℕ} {A : IntrinsicAmplitudeCovariance r}
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hn σ A)
    (c : AtlasChart M) {K : Set M} (hK : IsCompact K) (hKc : K ⊆ c.chart.source) :
    atlasSymmetricJetEntries c (intrinsicSymmetricJetCovariance A.density) =ᵐ[A.control.restrict
      (amplitudeCosphereWindow r K)] atlasJetCovarianceOperator c A.density := by
  have hW := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  filter_upwards [ae_restrict_of_ae hA.2.2.2.2.2, ae_restrict_mem (μ := A.control) hW] with p hp hLoc
  exact atlasSymmetricJetEntries_original c (hKc hLoc) hp.2.2 hp.2.1

theorem original_hasIntrinsicSymmetricJetMeasure
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A) :
    HasIntrinsicSymmetricJetMeasure A.control (intrinsicSymmetricJetCovariance A.density) := by
  refine ⟨hA.2.1, hA.2.2.1, hA.2.2.2.1, ?_⟩
  intro c K hK hKc ρ
  have hEq := ae_atlasSymmetricJetEntries_original_on_compact hA c hK hKc
  have hCov := (original_intrinsicJetAmplitude_positive_and_integrable r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA).2 c hK hKc
  refine ⟨fun i j => (integrable_atlasJetCovarianceOperator_on_compact c A.density A.control hK hKc hCov i j).congr
    (hEq.symm.mono fun _ hp => congrFun (congrFun hp i) j), ?_, ?_⟩
  · filter_upwards [hEq, ae_original_atlasJetCovarianceOperator_gramPositive_unitTrace r B g hB hg hnB σ A hA c hK hKc]
      with p hp hPositive
    simpa only [hp] using hPositive
  · obtain ⟨ν, hν⟩ := original_atlasJetCovarianceOperator_matrixMeasure_trace r B g hB hg hsB hsG
      hnB hnG hconv hb hv σ hσ A hA c hK hKc
    refine ⟨ν, fun U hU => ⟨fun i j => (hν U hU).1 i j |>.trans ?_, (hν U hU).2⟩⟩
    apply integral_congr_ae
    exact ae_restrict_of_ae (hEq.symm.mono fun _ hp => congrFun (congrFun hp i) j)

theorem original_atlasSymmetricJetEntries_overlap
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c d : AtlasChart M) {K : Set M} (hK : IsCompact K) (hKcd : K ⊆ c.chart.source ∩ d.chart.source)
    (U : Set (Cosphere r)) (i j : JetSlot) :
    let ρ := A.control.restrict (amplitudeCosphereWindow r K)
    let D := intrinsicSymmetricJetCovariance A.density
    (∫ p in U, atlasSymmetricJetEntries d D p i j ∂ρ) = ∑ l : JetSlot, ∑ k : JetSlot, ∫ p in U,
      atlasJetOperatorTransitionWeight c d (projection p) i j k l * atlasSymmetricJetEntries c D p k l ∂ρ := by
  intro ρ D
  have hc := hKcd.trans inter_subset_left
  have hd := hKcd.trans inter_subset_right
  have hEqc := ae_atlasSymmetricJetEntries_original_on_compact hA c hK hc
  have hEqd := ae_atlasSymmetricJetEntries_original_on_compact hA d hK hd
  have hCov := (original_intrinsicJetAmplitude_positive_and_integrable r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA).2 c hK hc
  have hI := integrable_atlasJetCovarianceOperator_on_compact c A.density A.control hK hc hCov
  calc
    _ = ∫ p in U, atlasJetCovarianceOperator d A.density p i j ∂ρ :=
      integral_congr_ae (ae_restrict_of_ae (hEqd.mono fun _ hp => congrFun (congrFun hp i) j))
    _ = ∑ l : JetSlot, ∑ k : JetSlot, ∫ p in U,
        atlasJetOperatorTransitionWeight c d (projection p) i j k l * atlasJetCovarianceOperator c A.density p k l ∂ρ :=
      integral_atlasJetCovarianceOperator_change_on_compact c d A.density A.control hK hKcd hI U i j
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      exact integral_congr_ae (ae_restrict_of_ae (hEqc.symm.mono fun p hp => congrArg
        (atlasJetOperatorTransitionWeight c d (projection p) i j k l * ·) (congrFun (congrFun hp k) l)))

end Burnett.Microlocal.Overlap
