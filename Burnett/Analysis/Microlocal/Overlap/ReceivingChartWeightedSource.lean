import Burnett.Analysis.Microlocal.Overlap.ReceivingChartUnregularizedSource
import Burnett.Analysis.Microlocal.Overlap.OriginalAngularDefectConsumer
import Burnett.Analysis.Microlocal.Overlap.OriginalWeakInput

/-! Read the bilaterally weighted source action directly from the same
original covariance, with the ordered entry in the second-linear pairing. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped ComplexConjugate ContDiff InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The two real source multipliers may include the reciprocal of the
actual represented cutoff and each ordered inverse-chart jet coefficient. -/
theorem tendsto_originalVolume_bilateralSourceAngular_to_rawDensity
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (p : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hSupport : ∀ ξ, tsupport (fun x => p x ξ) ⊆ S)
    (hJoint : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => p x 0)) (hDegree : ∀ x, DegreeZero (p x))
    (a b : D) (i j : JetSlot) :
    let f := originalVolumeAngularInput B g hB hg hn q
    Tendsto (fun n => ∫ x, conj (coeffMul a (f (σ n) i) x) *
      firstOrderAction p (coeffMul b (f (σ n) j)) x) atTop
      (𝓝 (∫ z : Chart q.ball,
        ((physicalCoefficient a z.1 * physicalCoefficient b z.1) * p z.1 z.2) *
          density ν hfin z i j ∂traceMeasure ν)) := by
  intro f
  obtain ⟨F, C, hC, hEq, hSupp, hBound, hWeak⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hn hconv hb q
  have hIdent (n : ℕ) (s : JetSlot) : F n s = f n s :=
    SchwartzMap.injective_toLp 2 volume (hEq n s)
  let p' (x ξ : E) := (physicalCoefficient a x * physicalCoefficient b x) * p x ξ
  have hc (c : D) : ContDiff ℝ ∞ (physicalCoefficient c : E → ℂ) :=
    Complex.ofRealCLM.contDiff.comp (test_smooth c)
  have hP : ContDiffOn ℝ ∞ (uncurry p') (univ ×ˢ ({0}ᶜ : Set E)) :=
    (((hc a).mul (hc b)).comp contDiff_fst).contDiffOn.mul hJoint
  have hP0 : ContDiff ℝ ∞ (fun x => p' x 0) := ((hc a).mul (hc b)).mul hZero
  have hPS (ξ : E) : tsupport (fun x => p' x ξ) ⊆ S := tsupport_mul_subset_right.trans (hSupport ξ)
  have hPD (x : E) : DegreeZero (p' x) := fun t ht ξ => by simp only [p', hDegree x t ht ξ]
  have hF : RepresentsCompactJetPairings q.ball (fun n k => (F n k).toLp 2 volume) σ ν hfin := by
    simpa only [hEq] using hRep
  have hLimit := tendsto_compactAngularAction_pairings_of_matrixDensity q.ball F σ ν hfin hF
    p' S hS hPS hP hP0 hPD i j (C * C)
    (fun n => mul_le_mul (hBound (σ n) i) (hBound (σ n) j) (norm_nonneg _) hC)
  have hPair := tendsto_angularPrincipal_twoCutoff_difference p S hS hSupport hJoint hZero hDegree a b
    (fun n => F (σ n) i) (fun n => F (σ n) j) q.ball.closedBall (isCompact_closedBall _ _)
    (fun n => hSupp (σ n) j) C C hC (fun n => hBound (σ n) i) (fun n => hBound (σ n) j)
    (fun w => (hWeak j w).comp hσ.tendsto_atTop)
  simpa only [p', sub_add_cancel, zero_add, hIdent] using hPair.add hLimit

end Burnett.Microlocal.Overlap
