import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetAmplitudeTensor
import Burnett.Analysis.Microlocal.Overlap.GlobalReceivingChartJetMeasure
import Burnett.Analysis.Microlocal.Overlap.OriginalVacuumIntrinsicAmplitude

/-! Positive and locally integrable components of the actual global jet covariance. -/

set_option autoImplicit false
set_option maxHeartbeats 1650000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity chartTangentBasis)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ComplexOrder ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Within a chart this function gives the actual jet covariance entries in
that tangent basis, extended by zero off its source. -/
def atlasIntrinsicJetComponent {r : Metric (M := M)} (c : AtlasChart M)
    (H : AmplitudeCovarianceDensity r) (p : Cosphere r) (i j : JetSlot) : ℂ := by
  classical
  exact if hp : projection p ∈ c.chart.source then
    jetAmplitudeComponents (chartTangentBasis c (projection p) hp) (intrinsicJetAmplitude H p) i j
  else 0

theorem atlasIntrinsicJetComponent_eq_ordered {r : Metric (M := M)} (c : AtlasChart M)
    (H : AmplitudeCovarianceDensity r) (p : Cosphere r) (hp : projection p ∈ c.chart.source) (i j : JetSlot) :
    atlasIntrinsicJetComponent c H p i j = atlasOrderedJetEntry c H p j i := by
  rw [atlasIntrinsicJetComponent, dif_pos hp, atlasOrderedJetEntry_eq_intrinsicJetComponents c H p hp]

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- The jet covariance uses the original global control. Its actual fiber
matrix is positive in every basis and its chart entries are integrable on
every compact base window of that chart. -/
theorem original_intrinsicJetAmplitude_positive_and_integrable
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A) :
    (∀ᵐ p ∂A.control, ∀ b : Module.Basis Index ℝ (TangentSpace Model (projection p)),
      (jetAmplitudeComponents b (intrinsicJetAmplitude A.density p)).PosSemidef) ∧
    ∀ (c : AtlasChart M) {K : Set M}, IsCompact K → K ⊆ c.chart.source → ∀ i j : JetSlot,
      IntegrableOn (fun p => atlasIntrinsicJetComponent c A.density p i j)
        (amplitudeCosphereWindow r K) A.control := by
  obtain ⟨hCover, _, _, _, hLaws, hAlmost⟩ := hA
  refine ⟨?_, ?_⟩
  · filter_upwards [hAlmost] with p hp
    intro b
    exact jetAmplitudeComponents_posSemidef b p.val.2.toLinearMap (A.density p) (hp.2.1 b)
  · intro c K hK hKc i j
    by_cases hm : Nonempty M
    · obtain ⟨q, hWhole, ν, hf, hRep⟩ := hCover hm
      have hI := original_globalAmplitude_integrable_receivingAtlasJet_on_compact r B g hB hg hsB hsG
        hnB hnG hconv hb hv σ hσ q hWhole ν hf (fun n => (hRep n).1) A hLaws c hK hKc j i
      refine hI.congr ?_
      have hMeas := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
      filter_upwards [ae_restrict_mem (μ := A.control) hMeas] with p hp
      exact (atlasIntrinsicJetComponent_eq_ordered c A.density p (hKc hp) i j).symm
    · have hEmpty : K = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun x _ => hm ⟨x⟩)
      simp [hEmpty, amplitudeCosphereWindow]

end Burnett.Microlocal.Overlap
