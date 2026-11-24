import Burnett.Analysis.Microlocal.Overlap.LocalCutoffGradient
import Burnett.Analysis.Microlocal.Overlap.TargetSlotDensity

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedSubsequenceSeparableExtension (finiteSmoothRestriction finiteSmoothRestriction_apply)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.SeparablePositive (finiteSeparableOperator separableOperator)
open Burnett.Microlocal.SmoothBaseTests
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ComplexConjugate ContDiff InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- On the same chart and subsequence, multiplying the cutoff reweights
each tested entry by the square of the real multiplier. The two compact
balls need only contain their respective cutoff supports. -/
theorem sameChart_cutoffMul_density_integral_eq
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hbnd : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (L : BallData)
    (hL : L.closedBall ⊆ (chartAt CoordinateSpace q.center).target)
    (χ' θ : D) (hχ' : tsupport (χ' : E → ℝ) ⊆ L.closedBall)
    (hCut : ∀ x : E, (χ' : E → ℝ) x = (θ : E → ℝ) x * (q.cutoff : E → ℝ) x)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (ν' : (JetSlot → ℂ) → Measure (Chart L)) (hfin' : ∀ v, IsFiniteMeasure (ν' v))
    (hR : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (hR' : RepresentsCompactJetPairings L
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center χ' (hχ'.trans hL)) σ ν' hfin')
    (b m : BoundedSymbol E) (hb : Continuous (b : E → ℂ))
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ))
    (i j : JetSlot) :
    (∫ p : Chart L, b p.1 * m p.2 * density ν' hfin' p i j ∂traceMeasure ν') =
      ∫ p : Chart q.ball, b p.1 * ↑((θ : E → ℝ) p.1 ^ 2) * m p.2 *
        density ν hfin p i j ∂traceMeasure ν := by
  let w := originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
    (q.cutoff_support.trans q.ball_in_chart)
  let w' := originalGradient_volumeWeightedL2 B g hB hg hnB q.center χ' (hχ'.trans hL)
  let a := physicalCoefficient θ
  have hA : ContDiff ℝ ∞ (a : E → ℂ) := Complex.ofRealCLM.contDiff.comp (test_smooth θ)
  have hAS : HasCompactSupport (a : E → ℂ) := (test_compactSupport θ).comp_left Complex.ofReal_zero
  have hInput (n : ℕ) (k : JetSlot) : w' n k = symbolCLM a (w n k) :=
    originalGradient_volumeWeightedL2_of_cutoff_mul B g hB hg hnB q.center q.cutoff χ' θ
      (q.cutoff_support.trans q.ball_in_chart) (hχ'.trans hL) hCut n k
  have hTest (p : Chart L) :
      finiteSmoothRestriction L (fun _ : Unit => b) (fun _ : Unit => m)
        (fun _ => hb) (fun _ => hm) p = b p.1 * m p.2 := by
    rcases p with ⟨x, ξ⟩
    rw [finiteSmoothRestriction_apply]
    simp
  have hUnweighted : Tendsto (fun n => inner ℂ (w' (σ n) i) (separableOperator b m (w' (σ n) j)))
      atTop (𝓝 (∫ p : Chart L, b p.1 * m p.2 * density ν' hfin' p i j ∂traceMeasure ν')) := by
    have h := hR'.2.2.2.2.2.2 Unit (fun _ => b) (fun _ => m) (fun _ => hb) (fun _ => hm) (fun _ => hd) i j
    simpa [w', finiteSeparableOperator, hTest] using h
  obtain ⟨f, C, hC, hF, hS, hBound, hWeak⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hnB hconv hbnd q
  have hW (n : ℕ) (k : JetSlot) : (f n k).toLp 2 volume = w n k := hF n k
  have hWeighted := weightedTargetSlots_tendsto_density q.ball w σ hσ ν hfin hR f hW hS C hC
    (fun n k => by simpa only [hW] using hBound n k)
    (fun k v => by simpa only [hW] using hWeak k v)
    b m m hb hm hd 0 (fun _ _ => rfl)
    (fun _ : Unit => a) (fun _ : Unit => a) (fun _ => hA.continuous) (fun _ => hA) (fun _ => hAS)
    (fun _ => i) (fun _ => j)
  have hSquare (p : Chart q.ball) :
      b p.1 * conj (a p.1) * a p.1 * m p.2 * density ν hfin p i j =
        b p.1 * ↑((θ : E → ℝ) p.1 ^ 2) * m p.2 * density ν hfin p i j := by
    change b p.1 * conj ((θ : E → ℝ) p.1 : ℂ) * ((θ : E → ℝ) p.1 : ℂ) * m p.2 * _ = _
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  have hWeighted' : Tendsto
      (fun n => inner ℂ (symbolCLM a (w (σ n) i)) (separableOperator b m (symbolCLM a (w (σ n) j))))
      atTop (𝓝 (∫ p : Chart q.ball, b p.1 * conj (a p.1) * a p.1 * m p.2 *
        density ν hfin p i j ∂traceMeasure ν)) := by
    simpa only [Fintype.sum_unique] using hWeighted
  have hPair (n : ℕ) :
      inner ℂ (symbolCLM a (w (σ n) i)) (separableOperator b m (symbolCLM a (w (σ n) j))) =
        inner ℂ (w' (σ n) i) (separableOperator b m (w' (σ n) j)) := by
    simp only [hInput]
  have hSame := hWeighted'.congr hPair
  exact (tendsto_nhds_unique hUnweighted hSame).trans
    (integral_congr_ae (Eventually.of_forall hSquare))

end Burnett.Microlocal.Overlap
