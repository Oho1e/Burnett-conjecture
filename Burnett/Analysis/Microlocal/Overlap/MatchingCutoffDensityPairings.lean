import Burnett.Analysis.Microlocal.Overlap.OriginalTransportedAngularPairing
import Burnett.Analysis.Microlocal.Overlap.OverlapBaseTestPullback
import Burnett.Analysis.Microlocal.Overlap.PairingReplacement
import Burnett.Analysis.Microlocal.Overlap.TargetSlotDensity
import Burnett.Analysis.Microlocal.Overlap.TransportedGradientMultiplier

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.F05.ChartVolumeAmplitude Burnett.F05.OverlapCovariantGradient
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapKernel
open Burnett.Microlocal.SeparablePositive (separableOperator)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- For matching cutoffs and a common represented subsequence, the two
actual chart densities give identical transported angular test values,
with the tensor coefficients acting in both ordered slots. -/
theorem exists_matchingCutoff_overlap_densityPairings
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q d : CompactChartInput M)
    (hKU : q.ball.closedBall ⊆ (chartTransition q.center d.center).source)
    (hηK : tsupport (d.cutoff : E → ℝ) ⊆ chartTransition q.center d.center '' q.ball.closedBall)
    (hCut : ∀ x ∈ (chartTransition q.center d.center).source,
      (d.cutoff : E → ℝ) (chartTransition q.center d.center x) = (q.cutoff : E → ℝ) x)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (hRq : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq)
    (hRd : RepresentsCompactJetPairings d.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB d.center d.cutoff
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd) :
    ∃ w : JetSlot → JetSlot → D,
      (∀ i k, EqOn (w i k : E → ℝ) (overlapJetCoefficient q.center d.center i k)
        (chartTransition q.center d.center '' q.ball.closedBall)) ∧
      ∀ (b m : BoundedSymbol E) (_ : ContDiff ℝ ∞ (b : E → ℂ))
        (_ : tsupport (b : E → ℂ) ⊆ chartTransition q.center d.center '' q.ball.closedBall)
        (_ : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (_ : DegreeZero (m : E → ℂ)),
      ∃ a : BoundedSymbol E, ContDiff ℝ ∞ (a : E → ℂ) ∧ tsupport (a : E → ℂ) ⊆ q.ball.closedBall ∧
        (∀ x ∈ q.ball.closedBall, a x = b (chartTransition q.center d.center x)) ∧
        ∀ i j : JetSlot,
          (∫ p : Chart q.ball, movingChartAngularSymbol q.center d.center a m (p.1,p.2) *
            density νq hfq p i j ∂traceMeasure νq) =
          ∑ k : JetSlot, ∑ l : JetSlot, ∫ p : Chart d.ball,
            b p.1 * conj (physicalCoefficient (w i k) p.1) * physicalCoefficient (w j l) p.1 * m p.2 *
              density νd hfd p k l ∂traceMeasure νd := by
  let K := q.ball.closedBall
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨_, w, _, _, _, hw⟩ := exists_overlapJetCoefficient_tests q.center d.center K hK hKU
  refine ⟨w, hw, ?_⟩
  intro b m hb₁ hbs hm hd
  obtain ⟨a, ha, haS, _, haOn⟩ := exists_overlapBaseTest_pullback q.center d.center K hK hKU b hb₁ hbs
  have hPull : ∀ x ∈ K, a x = b (chartTransition q.center d.center x) :=
    fun x hx => haOn x (hKU hx)
  refine ⟨a, ha, haS, hPull, ?_⟩
  intro i j
  let hc := q.cutoff_support.trans q.ball_in_chart
  let hd' := d.cutoff_support.trans d.ball_in_chart
  let f := originalVolumeGradientSchwartz B g hB hg hnB q.center q.cutoff hc
  have hS (n : ℕ) (k : JetSlot) : tsupport (f n k : E → ℂ) ⊆ K :=
    (originalVolumeGradientSchwartz_tsupport B g hB hg hnB q.center q.cutoff hc n k).trans q.cutoff_support
  obtain ⟨F, C, _, hF, _, hN, hWeak⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hnB hconv hb q
  obtain ⟨G, D₀, _, hG, _, hM, _⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hnB hconv hb d
  have hfEq (n : ℕ) (k : JetSlot) : (f n k).toLp 2 volume = (F n k).toLp 2 volume := (hF n k).symm
  have hfN (n : ℕ) (k : JetSlot) : ‖(f n k).toLp 2 volume‖ ≤ C := by
    rw [hfEq]
    exact hN n k
  have hfW (k : JetSlot) (v : ComplexL2 E) :
      Tendsto (fun n => inner ℂ v ((f n k).toLp 2 volume)) atTop (𝓝 0) := by
    simpa only [hfEq] using hWeak k v
  let A := separableOperator b (normalizedAngularSymbol m)
  let U (n : ℕ) (k : JetSlot) :=
    (transportedOriginalVolumeGradientSchwartz B g hB hg hnB
      q.center d.center K hK hKU q.cutoff q.cutoff_support n k).toLp 2 volume
  let α (k l : JetSlot) := physicalCoefficient (w k l)
  let u (n : ℕ) (k : JetSlot) := originalGradient_volumeWeightedL2 B g hB hg hnB
    d.center d.cutoff hd' n k
  let V (n : ℕ) (k : JetSlot) := ∑ l : JetSlot, symbolCLM (α k l) (u n l)
  have hA (k l : JetSlot) : ContDiff ℝ ∞ (α k l : E → ℂ) :=
    Complex.ofRealCLM.contDiff.comp (test_smooth (w k l))
  have hAc (k l : JetSlot) : HasCompactSupport (α k l : E → ℂ) := by
    apply (test_compactSupport (w k l)).of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    intro hz
    apply hx
    change ((w k l : E → ℝ) x : ℂ) = 0
    rw [hz, Complex.ofReal_zero]
  have hSource := tendsto_targetSeparablePairings_of_sourceMatrixDensity B hB hnB
    q.center d.center q.ball hKU a b m ha haS hPull hm hd f hS C hfN hfW σ hσ νq hfq hRq i j
  have hTarget := originalVolume_weightedTargetSlots_tendsto_density r B g hB hg hnB hconv hb d
    σ hσ νd hfd hRd b m hb₁.continuous hm hd (α i) (α j)
    (fun k => (hA i k).continuous) (hA j) (hAc j) id id
  have hReplace (k : JetSlot) : Tendsto (fun n => U (σ n) k - V (σ n) k) atTop (𝓝 0) :=
    (transportedOriginalVolumeGradient_sub_target_sum_tendsto_zero r B g hB hg hnB hconv
      q.center d.center K hK hKU q.cutoff d.cutoff q.cutoff_support hd' hηK hCut w hw k).comp hσ.tendsto_atTop
  have hU (n : ℕ) : ‖U (σ n) j‖ ≤ C := by
    change ‖(transportedHalfDensitySchwartz q.center d.center K hK hKU
      (f (σ n) j) (hS (σ n) j)).toLp 2 volume‖ ≤ C
    rw [transportedHalfDensitySchwartz_norm_toLp]
    exact hfN (σ n) j
  have hV (n : ℕ) : ‖V (σ n) i‖ ≤ ∑ k, (α i k).bound * D₀ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    change ‖symbolL2 (α i k) (u (σ n) k)‖ ≤ _
    refine (symbolL2_norm_le (α i k) _).trans (mul_le_mul_of_nonneg_left ?_ (α i k).bound_nonneg)
    simpa only [hG] using hM (σ n) k
  have hError := tendsto_orderedPairing_sub_of_strong_replacement A
    (fun n => U (σ n) i) (fun n => U (σ n) j) (fun n => V (σ n) i) (fun n => V (σ n) j)
    C (∑ k, (α i k).bound * D₀) hU hV (hReplace i) (hReplace j)
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique (hSource.sub hTarget) hError

end Burnett.Microlocal.Overlap
