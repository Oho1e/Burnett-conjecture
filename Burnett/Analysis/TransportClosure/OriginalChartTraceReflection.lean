import Burnett.Analysis.TransportClosure.OriginalChartEntryReflection
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! The original trace and its normalized covariance under angular reflection. -/
set_option autoImplicit false
set_option maxRecDepth 3900
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (entryMeasure traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density integrable_density_entry)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open scoped BigOperators ComplexConjugate ContDiff ENNReal Manifold

def compactChartAntipodalHomeomorph (K : BallData) : Chart K ≃ₜ Chart K where
  toFun := compactChartAntipodal K
  invFun := compactChartAntipodal K
  left_inv := compactChartAntipodal_involutive K
  right_inv := compactChartAntipodal_involutive K
  continuous_toFun := continuous_compactChartAntipodal K
  continuous_invFun := continuous_compactChartAntipodal K

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Reflection preserves the original trace measure and conjugates its full
normalized density on one common conull set. -/
theorem originalVolume_chartTrace_and_density_antipodal
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (q : CompactChartInput M) (σ : ℕ → ℕ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf) :
    let φ := compactChartAntipodal q.ball
    let τ := traceMeasure ν
    MeasurePreserving φ τ τ ∧ ∀ᵐ z ∂τ, ∀ i j,
      density ν hf (φ z) i j = conj (density ν hf z i j) := by
  intro φ τ
  have hE : MeasurableEmbedding φ := (compactChartAntipodalHomeomorph q.ball).measurableEmbedding
  have hInv : Involutive φ := compactChartAntipodal_involutive q.ball
  let D := density ν hf
  have hFin : IsFiniteMeasure τ := hRep.2.1
  letI := hFin
  have hI (i j : JetSlot) : Integrable (fun z => D z i j) τ := integrable_density_entry ν hf i j
  have hSet (S : Set (Chart q.ball)) (hS : MeasurableSet S) (i j : JetSlot) :
      (∫ p in S, D p i j ∂τ) = entryMeasure ν hf i j S := hRep.2.2.2.2.1 S hS i j
  have hDiag (S : Set (Chart q.ball)) (hS : MeasurableSet S) :
      ∑ i, entryMeasure ν hf i i S = (τ.real S : ℂ) := by
    simp_rw [← hSet S hS]
    rw [← integral_finset_sum _ (fun i _ => (hI i i).integrableOn)]
    change (∫ z in S, (D z).trace ∂τ) = _
    have hOne : (fun z => (D z).trace) =ᵐ[τ.restrict S] (fun _ => (1 : ℂ)) :=
      ae_restrict_of_ae (hRep.2.2.2.2.2.1.mono (fun _ hz => hz.2))
    rw [integral_congr_ae hOne]
    simp [measureReal_def]
  have hBorel (S : Set (Chart q.ball)) (hS : MeasurableSet S) (i j : JetSlot) :
      conj (entryMeasure ν hf i j (φ ⁻¹' S)) = entryMeasure ν hf i j S :=
    originalVolume_chartEntryMeasure_antipodal B g hB hg hn q σ ν hf hRep S hS i j
  have hMap : τ.map φ = τ := by
    ext S hS
    rw [hE.map_apply]
    apply (ENNReal.toReal_eq_toReal (measure_ne_top τ _) (measure_ne_top τ _)).mp
    apply Complex.ofReal_injective
    change (τ.real (φ ⁻¹' S) : ℂ) = (τ.real S : ℂ)
    calc
      _ = conj ((τ.real (φ ⁻¹' S) : ℂ)) := (Complex.conj_ofReal _).symm
      _ = conj (∑ i, entryMeasure ν hf i i (φ ⁻¹' S)) := congrArg _ (hDiag _ (hE.measurable hS)).symm
      _ = ∑ i, entryMeasure ν hf i i S := by simp only [map_sum, hBorel S hS]
      _ = _ := hDiag S hS
  have hMP : MeasurePreserving φ τ τ := ⟨hE.measurable, hMap⟩
  refine ⟨hMP, ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ?_⟩
  let f (z : Chart q.ball) := D z i j
  have hFC : Integrable (fun z => f (φ z)) τ := hMP.integrable_comp_of_integrable (hI i j)
  have hC : Integrable (fun z => conj (f z)) τ :=
    (hI i j).norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable (hI i j).aestronglyMeasurable)
      (Eventually.of_forall fun z => by rw [Complex.norm_conj])
  refine hFC.ae_eq_of_forall_setIntegral_eq _ _ hC (fun S hS _ => ?_)
  have hPre : φ ⁻¹' (φ ⁻¹' S) = S := by
    ext z
    change φ (φ z) ∈ S ↔ z ∈ S
    rw [hInv z]
  have hMapR : (τ.restrict S).map φ = τ.restrict (φ ⁻¹' S) := by
    conv_rhs => rw [← hMap]
    rw [Measure.restrict_map hE.measurable (hE.measurable hS), hPre]
  have hMPR : MeasurePreserving φ (τ.restrict S) (τ.restrict (φ ⁻¹' S)) := ⟨hE.measurable, hMapR⟩
  change (∫ z in S, f (φ z) ∂τ) = ∫ z in S, conj (f z) ∂τ
  rw [hMPR.integral_comp hE f, integral_conj, hSet _ (hE.measurable hS) i j, hSet S hS i j]
  rw [← hBorel S hS i j, starRingEnd_self_apply]

end Burnett.Microlocal.Overlap
