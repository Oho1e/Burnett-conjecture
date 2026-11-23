import Burnett.Analysis.Microlocal.Overlap.OriginalWeakInput
import Burnett.Analysis.Microlocal.Overlap.TransportedSeparablePairing

set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapKernel (movingChartAngularSymbol transportedHalfDensitySchwartz)
open Burnett.Microlocal.SeparablePositive (separableOperator)
open scoped ComplexConjugate ContDiff InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- On every represented subsequence, the transported tests of the actual
volume-weighted coordinate gradient read the same source chart measure. -/
theorem exists_originalVolume_transportedAngularPairings_of_matrixDensity
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (d : M)
    (hKU : q.ball.closedBall ⊆ (chartTransition q.center d).source) :
    let w := originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
      (q.cutoff_support.trans q.ball_in_chart)
    ∃ f : ℕ → JetSlot → SchwartzMap E ℂ,
      (∀ n i, (f n i).toLp 2 volume = w n i) ∧
      ∀ (σ : ℕ → ℕ) (_ : StrictMono σ) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
        (hfin : ∀ v, IsFiniteMeasure (ν v)) (_ : RepresentsCompactJetPairings q.ball w σ ν hfin)
        (a m : BoundedSymbol E) (_ : ContDiff ℝ ∞ (a : E → ℂ))
        (_ : tsupport (a : E → ℂ) ⊆ q.ball.closedBall)
        (_ : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (_ : DegreeZero (m : E → ℂ))
        (i j : JetSlot),
        Tendsto (fun n => ∫ x, conj (f (σ n) i x) *
          (a x * localizedTransportedAngularAction q.center d q.ball.closedBall m (f (σ n) j) x))
          atTop (𝓝 (∫ x : Chart q.ball, movingChartAngularSymbol q.center d a m (x.1,x.2) *
            density ν hfin x i j ∂traceMeasure ν)) := by
  intro w
  obtain ⟨f, C, _, hIdent, hS, hC, hw⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hnB hconv hb q
  refine ⟨f, hIdent, ?_⟩
  intro σ hσ ν hfin hRep a m ha haS hm hd i j
  have hEq : (fun n j => (f n j).toLp 2 volume) = w := funext fun n => funext (hIdent n)
  have hRepf : RepresentsCompactJetPairings q.ball (fun n i => (f n i).toLp 2 volume) σ ν hfin := by
    rw [hEq]
    exact hRep
  exact tendsto_transportedAngularPairings_of_matrixDensity B hB hnB q.center d q.ball hKU
    a m ha haS hm hd f hS C hC hw σ hσ ν hfin hRepf i j

/-- On the already represented original subsequence, the actual target
operator on the transported original gradients reads the source density. -/
theorem exists_originalVolume_targetSeparablePairings_of_sourceMatrixDensity
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (d : M)
    (hKU : q.ball.closedBall ⊆ (chartTransition q.center d).source) :
    let w := originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
      (q.cutoff_support.trans q.ball_in_chart)
    ∃ (f : ℕ → JetSlot → SchwartzMap E ℂ) (hS : ∀ n i, tsupport (f n i : E → ℂ) ⊆ q.ball.closedBall),
      (∀ n i, (f n i).toLp 2 volume = w n i) ∧
      ∀ (σ : ℕ → ℕ) (_ : StrictMono σ) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
        (hfin : ∀ v, IsFiniteMeasure (ν v)) (_ : RepresentsCompactJetPairings q.ball w σ ν hfin)
        (a b m : BoundedSymbol E) (_ : ContDiff ℝ ∞ (a : E → ℂ))
        (_ : tsupport (a : E → ℂ) ⊆ q.ball.closedBall)
        (_ : ∀ x ∈ q.ball.closedBall, a x = b (chartTransition q.center d x))
        (_ : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (_ : DegreeZero (m : E → ℂ))
        (i j : JetSlot),
        let F (n : ℕ) (k : JetSlot) := transportedHalfDensitySchwartz q.center d q.ball.closedBall
          (isCompact_closedBall _ _) hKU (f (σ n) k) (hS (σ n) k)
        Tendsto (fun n => inner ℂ ((F n i).toLp 2 volume)
          (separableOperator b (normalizedAngularSymbol m) ((F n j).toLp 2 volume)))
          atTop (𝓝 (∫ x : Chart q.ball, movingChartAngularSymbol q.center d a m (x.1,x.2) *
            density ν hfin x i j ∂traceMeasure ν)) := by
  intro w
  obtain ⟨f, C, _, hIdent, hS, hC, hw⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hnB hconv hb q
  refine ⟨f, hS, hIdent, ?_⟩
  intro σ hσ ν hfin hRep a b m ha haS hPull hm hd i j
  have hEq : (fun n k => (f n k).toLp 2 volume) = w := funext fun n => funext (hIdent n)
  have hRepf : RepresentsCompactJetPairings q.ball (fun n k => (f n k).toLp 2 volume) σ ν hfin := by
    rw [hEq]
    exact hRep
  exact tendsto_targetSeparablePairings_of_sourceMatrixDensity B hB hnB q.center d q.ball hKU
    a b m ha haS hPull hm hd f hS C hC hw σ hσ ν hfin hRepf i j

end Burnett.Microlocal.Overlap
