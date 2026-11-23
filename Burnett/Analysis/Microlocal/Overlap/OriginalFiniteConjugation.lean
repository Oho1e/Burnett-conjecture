import Burnett.Analysis.Microlocal.Overlap.FiniteConjugationWeakLimit
import Burnett.Analysis.Microlocal.Overlap.OriginalWeakInput

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The two finite Fourier actions on the actual localized metric gradient
have L² differences whose shell limit tends to zero along the original sequence. -/
theorem exists_originalVolume_overlap_fourierDifference_limit
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (d : M)
    (hKU : q.ball.closedBall ⊆ (chartTransition q.center d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) :
    ∃ f : ℕ → JetSlot → SchwartzMap E ℂ,
      (∀ n i, (f n i).toLp 2 volume = originalGradient_volumeWeightedL2 B g hB hg hnB
        q.center q.cutoff (q.cutoff_support.trans q.ball_in_chart) n i) ∧
      ∀ i, ∃ F : ℕ → ℕ → ComplexL2 E, ∃ R : ℕ → ComplexL2 E,
        (∀ n N, F n N =ᵐ[volume]
          localizedPartialAngularDifference q.center d q.ball.closedBall hKU m N (f n i)) ∧
        (∀ n, Tendsto (F n) atTop (𝓝 (R n))) ∧ Tendsto R atTop (𝓝 0) := by
  obtain ⟨f, C, _, hIdent, _, hC, hw⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hnB hconv hb q
  refine ⟨f, hIdent, fun i => ?_⟩
  exact exists_localizedPartialAngularDifference_limit B hB hnB q.center d q.ball.closedBall
    (isCompact_closedBall _ _) hKU (convex_closedBall _ _) m hm hd (fun n => f n i)
    C (fun n => hC n i) (hw i)

end Burnett.Microlocal.Overlap
