import Burnett.Analysis.Microlocal.Overlap.ReceivingJetGramPositiveTrace

/-! The global auxiliary control is the trace measure in each actual frame. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1800000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Matrix Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped BigOperators ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- The original matrix-valued covariance measure on a compact chart window
has the original positive control as its real trace on every Borel set. -/
theorem original_atlasJetCovarianceOperator_matrixMeasure_trace
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) {K : Set M} (hK : IsCompact K) (hSub : K ⊆ c.chart.source) :
    let ρ := A.control.restrict (amplitudeCosphereWindow r K)
    ∃ ν : VectorMeasure (Cosphere r) (JetSlot → JetSlot → ℂ),
      ∀ U : Set (Cosphere r), MeasurableSet U →
        (∀ i j : JetSlot, ν U i j = ∫ p in U, atlasJetCovarianceOperator c A.density p i j ∂ρ) ∧
        (Matrix.trace (ν U : Matrix JetSlot JetSlot ℂ)).re = ρ.real U := by
  intro ρ
  let O := atlasJetCovarianceOperator c A.density
  obtain ⟨ν, hν⟩ := original_atlasJetCovarianceOperator_matrixMeasure_on_compact r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA c hK hSub
  have hCov := (original_intrinsicJetAmplitude_positive_and_integrable r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA).2 c hK hSub
  have hI (i : JetSlot) : Integrable (fun p => O p i i) ρ :=
    integrable_atlasJetCovarianceOperator_on_compact c A.density A.control hK hSub hCov i i
  have hTrace : ∀ᵐ p ∂ρ, (O p).trace.re = 1 :=
    (ae_original_atlasJetCovarianceOperator_gramPositive_unitTrace r B g hB hg hnB σ A hA c hK hSub).mono
      (fun _ hp => hp.2.2)
  refine ⟨ν, fun U hU => ⟨hν U hU, ?_⟩⟩
  have hTraceI : Integrable (fun p => (O p).trace) (ρ.restrict U) := by
    simp only [Matrix.trace, Matrix.diag]
    exact integrable_finset_sum _ (fun i _ => (hI i).integrableOn)
  calc
    _ = (∑ i : JetSlot, ∫ p in U, O p i i ∂ρ).re := by
      simp only [Matrix.trace, Matrix.diag, hν U hU, O, ρ]
    _ = (∫ p in U, (O p).trace ∂ρ).re := by
      simp only [Matrix.trace, Matrix.diag, integral_finset_sum _ (fun i _ => (hI i).integrableOn)]
    _ = ∫ p in U, (O p).trace.re ∂ρ := (integral_re hTraceI).symm
    _ = ∫ _ in U, (1 : ℝ) ∂ρ := integral_congr_ae (ae_restrict_of_ae hTrace)
    _ = _ := by rw [integral_const, smul_eq_mul, mul_one, measureReal_def, measureReal_def, Measure.restrict_apply_univ]

end Burnett.Microlocal.Overlap
