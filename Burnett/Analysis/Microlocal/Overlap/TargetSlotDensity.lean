import Burnett.Analysis.Microlocal.Overlap.TargetSlotPairing
import Burnett.Analysis.Microlocal.Overlap.OriginalWeakInput
import Burnett.Analysis.Microlocal.OriginalVolumeMatrixMeasure

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedSubsequenceSeparableExtension
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.SmoothBaseTests (BallData)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Topology

/-- The weighted target slots use the same density entries and
subsequence as the original separated pairings. -/
theorem weightedTargetSlots_tendsto_density {I J : Type*} [Fintype I] [Fintype J]
    (K : BallData) (w : ℕ → JetSlot → ComplexL2 E) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings K w σ ν hfin)
    (f : ℕ → JetSlot → SchwartzMap E ℂ) (hf : ∀ n j, (f n j).toLp 2 volume = w n j)
    (hfS : ∀ n j, tsupport (f n j : E → ℂ) ⊆ K.closedBall)
    (B : ℝ) (hB : 0 ≤ B) (hN : ∀ n j, ‖w n j‖ ≤ B)
    (hw : ∀ j v, Tendsto (fun n => inner ℂ v (w n j)) atTop (𝓝 0))
    (b m mReg : BoundedSymbol E) (hb : Continuous (b : E → ℂ))
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ))
    (R : ℝ) (hReg : ∀ ξ, ξ ∉ Metric.closedBall (0 : E) R → mReg ξ = m ξ)
    (a : I → BoundedSymbol E) (c : J → BoundedSymbol E) (ha : ∀ i, Continuous (a i : E → ℂ))
    (hc : ∀ j, ContDiff ℝ ∞ (c j : E → ℂ)) (hcs : ∀ j, HasCompactSupport (c j : E → ℂ))
    (leftSlot : I → JetSlot) (rightSlot : J → JetSlot) :
    Tendsto (fun n =>
      inner ℂ (∑ i, symbolCLM (a i) (w (σ n) (leftSlot i)))
        (separableOperator b mReg (∑ j, symbolCLM (c j) (w (σ n) (rightSlot j)))))
      atTop (𝓝 (∑ i, ∑ j, ∫ p : Chart K, b p.1 * conj (a i p.1) * c j p.1 * m p.2 *
        density ν hfin p (leftSlot i) (rightSlot j) ∂traceMeasure ν)) := by
  let U (n : ℕ) (i : I) := w (σ n) (leftSlot i)
  let V (n : ℕ) (j : J) := w (σ n) (rightSlot j)
  let F (n : ℕ) (j : J) := f (σ n) (rightSlot j)
  let A (i : I) (j : J) := weightedSlotBaseSymbol b (a i) (c j)
  let P (n : ℕ) := inner ℂ (∑ i, symbolCLM (a i) (U n i))
    (separableOperator b mReg (∑ j, symbolCLM (c j) (V n j)))
  let P₀ (n : ℕ) := ∑ i, ∑ j, inner ℂ (U n i) (separableOperator (A i j) m (V n j))
  let L (i : I) (j : J) := ∫ p : Chart K, b p.1 * conj (a i p.1) * c j p.1 * m p.2 *
    density ν hfin p (leftSlot i) (rightSlot j) ∂traceMeasure ν
  have hCS : IsCompact K.closedBall := isCompact_closedBall _ _
  have hWeak (j : J) (v : ComplexL2 E) :
      Tendsto (fun n => inner ℂ v ((F n j).toLp 2 volume)) atTop (𝓝 0) := by
    simpa only [F, hf, Function.comp_apply] using (hw (rightSlot j) v).comp hσ.tendsto_atTop
  have hSmall : Tendsto (fun n => P n - P₀ n) atTop (𝓝 0) := by
    have h := weightedSlot_sum_pairing_difference_tendsto_zero b m mReg hm hd R hReg
      a c hc hcs K.closedBall hCS U F (fun n j => hfS (σ n) (rightSlot j))
      B B hB (fun n i => hN (σ n) (leftSlot i))
      (fun n j => by simpa only [F, hf] using hN (σ n) (rightSlot j)) hWeak
    simpa only [F, hf, P, P₀, A, V] using h
  have hOne (i : I) (j : J) :
      Tendsto (fun n => inner ℂ (U n i) (separableOperator (A i j) m (V n j)))
        atTop (𝓝 (L i j)) := by
    have hA : Continuous (A i j : E → ℂ) :=
      weightedSlotBaseSymbol_continuous b (a i) (c j) hb (ha i) (hc j).continuous
    have hRestriction (x : Chart K) : finiteSmoothRestriction K
        (fun _ : Unit => A i j) (fun _ : Unit => m) (fun _ => hA) (fun _ => hm) x =
          b x.1 * conj (a i x.1) * c j x.1 * m x.2 := by
      rcases x with ⟨p, ξ⟩
      rw [finiteSmoothRestriction_apply]
      simp [A, weightedSlotBaseSymbol_apply]
    have h := hRep.2.2.2.2.2.2 Unit (fun _ => A i j) (fun _ => m)
      (fun _ => hA) (fun _ => hm) (fun _ => hd) (leftSlot i) (rightSlot j)
    simpa [U, V, L, finiteSeparableOperator, hRestriction] using h
  have hInner (i : I) : Tendsto
      (fun n => ∑ j, inner ℂ (U n i) (separableOperator (A i j) m (V n j)))
      atTop (𝓝 (∑ j, L i j)) :=
    tendsto_finset_sum Finset.univ (fun j _ => hOne i j)
  have hMain : Tendsto P₀ atTop (𝓝 (∑ i, ∑ j, L i j)) :=
    tendsto_finset_sum Finset.univ (fun i _ => hInner i)
  have ht := hSmall.add hMain
  rw [zero_add] at ht
  exact ht.congr (fun n => sub_add_cancel (P n) (P₀ n))

open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open scoped Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The actual compact-window target gradients may be used in both
weighted slots with the normalized angular multiplier. -/
theorem originalVolume_weightedTargetSlots_tendsto_density {I J : Type*} [Fintype I] [Fintype J]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hbnd : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball (originalGradient_volumeWeightedL2 B g hB hg hnB
      q.center q.cutoff (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (b m : BoundedSymbol E) (hb : Continuous (b : E → ℂ))
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ))
    (a : I → BoundedSymbol E) (c : J → BoundedSymbol E)
    (ha : ∀ i, Continuous (a i : E → ℂ))
    (hc : ∀ j, ContDiff ℝ ∞ (c j : E → ℂ)) (hcs : ∀ j, HasCompactSupport (c j : E → ℂ))
    (leftSlot : I → JetSlot) (rightSlot : J → JetSlot) :
    let w := originalGradient_volumeWeightedL2 B g hB hg hnB
      q.center q.cutoff (q.cutoff_support.trans q.ball_in_chart)
    Tendsto (fun n =>
      inner ℂ (∑ i, symbolCLM (a i) (w (σ n) (leftSlot i)))
        (separableOperator b (normalizedAngularSymbol m)
          (∑ j, symbolCLM (c j) (w (σ n) (rightSlot j)))))
      atTop (𝓝 (∑ i, ∑ j, ∫ p : Chart q.ball, b p.1 * conj (a i p.1) * c j p.1 * m p.2 *
        density ν hfin p (leftSlot i) (rightSlot j) ∂traceMeasure ν)) := by
  intro w
  obtain ⟨f, C, hC, hEq, hS, hN, hWeak⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hnB hconv hbnd q
  have hW (n : ℕ) (j : JetSlot) : (f n j).toLp 2 volume = w n j := hEq n j
  exact weightedTargetSlots_tendsto_density q.ball w σ hσ ν hfin hRep f hW hS C hC
    (fun n j => by simpa only [hW] using hN n j)
    (fun j v => by simpa only [hW] using hWeak j v)
    b m (normalizedAngularSymbol m) hb hm hd 2 (normalizedAngularSymbol_eq_outside_ball m)
    a c ha hc hcs leftSlot rightSlot

end Burnett.Microlocal.Overlap
