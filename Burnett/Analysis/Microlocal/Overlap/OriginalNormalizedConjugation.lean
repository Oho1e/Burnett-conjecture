import Burnett.Analysis.Microlocal.Overlap.NormalizedConjugationWeakLimit
import Burnett.Analysis.Microlocal.Overlap.OriginalWeakInput
import Burnett.Analysis.Microlocal.Overlap.TransportedHalfDensitySchwartz

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
open Burnett.Microlocal.OverlapKernel
open scoped ContDiff FourierTransform Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The actual normalized overlap Fourier difference vanishes strongly on
each ordered component of the localized, volume-weighted original gradient. -/
theorem exists_originalVolume_overlap_normalizedFourierDifference_zero
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
      ∀ i, ∃ R : ℕ → ComplexL2 E,
        (∀ n, R n =ᵐ[volume]
          localizedNormalizedAngularDifference q.center d q.ball.closedBall hKU m (f n i)) ∧
        Tendsto R atTop (𝓝 0) := by
  obtain ⟨f, C, _, hIdent, hS, hC, hw⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hnB hconv hb q
  let K := q.ball.closedBall
  have hK : IsCompact K := isCompact_closedBall _ _
  refine ⟨f, hIdent, fun i => ?_⟩
  have hSource (n : ℕ) : Integrable (𝓕 (K.indicator (f n i : E → ℂ))) := by
    have hValue : K.indicator (f n i : E → ℂ) = f n i := by
      funext x
      by_cases hx : x ∈ K
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx]
        exact (image_eq_zero_of_notMem_tsupport (fun h => hx (hS n i h))).symm
    rw [hValue]
    exact (SchwartzMap.fourierTransformCLM ℂ (f n i)).integrable
  have hTarget (n : ℕ) : Integrable (𝓕 (transportedHalfDensity q.center d K (f n i))) := by
    let u := transportedHalfDensitySchwartz q.center d K hK hKU (f n i) (hS n i)
    change Integrable (𝓕 (u : E → ℂ))
    exact (SchwartzMap.fourierTransformCLM ℂ u).integrable
  exact exists_localizedNormalizedAngularDifference_strongZero B hB hnB q.center d K
    hK hKU (convex_closedBall _ _) m hm hd (fun n => f n i) hSource hTarget C (fun n => hC n i) (hw i)

end Burnett.Microlocal.Overlap
