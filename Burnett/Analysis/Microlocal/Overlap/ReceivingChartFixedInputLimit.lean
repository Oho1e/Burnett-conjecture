import Burnett.Analysis.Microlocal.Overlap.ReceivingChartAmplitudePairing
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartTwoWindowComparison
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartWeightedSource

/-! The angular limit of a receiving-window pairing from its actual
half-density replacement by finitely many original ordered slots. -/

set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option maxRecDepth 3200

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Filter MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open UnitCosphere (projection)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Microlocal.AtlasOverlapKernel (inverseJetEntry movingChartAngularSymbol receivingFrequency
  contDiffOn_movingChartAngularSymbol movingChartAngularSymbol_degreeZero transportedHalfDensitySchwartz
  tendsto_receivingSeparablePairing_sub_sourceAngularAction)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul coeffMul_toLp)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.SeparablePositive
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

private theorem coeffMul_tsupport_subset (a : D) (f : SchwartzMap E ℂ) :
    tsupport (coeffMul a f : E → ℂ) ⊆ tsupport (a : E → ℝ) := by
  apply closure_mono
  intro x hx
  by_contra h
  have hz : (a : E → ℝ) x = 0 := by simpa only [Function.mem_support, not_not] using h
  exact hx (by
    change ((a : E → ℝ) x : ℂ) * f x = 0
    rw [hz, Complex.ofReal_zero, zero_mul])

/-- The finite source replacement and every angular test use the fixed
original subsequence and its original cutoff and ordered covariance. -/
theorem tendsto_receivingWindow_separablePairing_of_transportedSlots
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (d : AtlasChart M) {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus ∩ d.chart.source)
    (hOuter : q.ball.closedBall ⊆ ((AtlasChart.atPoint q.center).transition d).source)
    (η₀ η₁ : D) (i j : JetSlot) (α β : JetSlot → D)
    (a b m : BoundedSymbol E) (ha : ContDiff ℝ ∞ (a : E → ℂ))
    (haS : tsupport (a : E → ℂ) ⊆ q.ball.closedBall) (hBmeas : Measurable (b : E → ℂ))
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hDegree : DegreeZero (m : E → ℂ))
    (hαS : ∀ k, tsupport (α k : E → ℝ) ⊆ (chartAt E q.center) '' K)
    (hβS : ∀ l, tsupport (β l : E → ℝ) ⊆ (chartAt E q.center) '' K)
    (hPull : ∀ x ∈ (chartAt E q.center) '' K, a x = b ((AtlasChart.atPoint q.center).transition d x))
    (hα : ∀ k x, x ∈ (chartAt E q.center) '' K →
      (α k : E → ℝ) x = (η₀ : E → ℝ) ((AtlasChart.atPoint q.center).transition d x) *
        ((q.cutoff : E → ℝ) x)⁻¹ * inverseJetEntry (.atPoint q.center) d i k x)
    (hβ : ∀ l x, x ∈ (chartAt E q.center) '' K →
      (β l : E → ℝ) x = (η₁ : E → ℝ) ((AtlasChart.atPoint q.center).transition d x) *
        ((q.cutoff : E → ℝ) x)⁻¹ * inverseJetEntry (.atPoint q.center) d j l x)
    (u v : ℕ → ComplexL2 E) :
    let c := AtlasChart.atPoint q.center
    let S := q.ball.closedBall
    let hS : IsCompact S := isCompact_closedBall _ _
    let hKS : c.chart '' K ⊆ S := fun _ ⟨_, hx, he⟩ =>
      he ▸ q.cutoff_support (subset_tsupport _ (hSub hx).1.2)
    let f := originalVolumeAngularInput B g hB hg hnB q
    let F (n : ℕ) (k : JetSlot) := transportedHalfDensitySchwartz c d S hS hOuter
      (coeffMul (α k) (f (σ n) k)) ((coeffMul_tsupport_subset _ _).trans ((hαS k).trans hKS))
    let G (n : ℕ) (l : JetSlot) := transportedHalfDensitySchwartz c d S hS hOuter
      (coeffMul (β l) (f (σ n) l)) ((coeffMul_tsupport_subset _ _).trans ((hβS l).trans hKS))
    let T := separableOperator b (normalizedAngularSymbol m)
    Tendsto (fun n => inner ℂ (u n) (T (v n)) -
      ∑ k : JetSlot, ∑ l : JetSlot, inner ℂ ((F n k).toLp 2 volume) (T ((G n l).toLp 2 volume)))
      atTop (𝓝 0) →
    Tendsto (fun n => inner ℂ (u n) (T (v n))) atTop
      (𝓝 (∫ p,
        let z := atlasAngularPhaseCode d p
        ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * b z.1 * m z.2.val) *
          atlasOrderedJetEntry d A.density p i j ∂A.control.restrict (amplitudeCosphereWindow r K))) := by
  intro c S hS hKS f F G T hReplace
  let p (x ξ : E) := movingChartAngularSymbol c d a m (x, ξ)
  have hpS (ξ : E) : tsupport (fun x => p x ξ) ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro x hx
    by_contra hout
    exact hx (by simp only [p, movingChartAngularSymbol,
      image_eq_zero_of_notMem_tsupport (fun h => hout (haS h)), zero_mul])
  have hpJ : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)) :=
    contDiffOn_movingChartAngularSymbol c d a m ha (haS.trans hOuter) hm
  have hp0 : ContDiff ℝ ∞ (fun x => p x 0) := by
    simpa only [p, movingChartAngularSymbol, map_zero] using ha.mul (contDiff_const (c := m 0))
  have hpD := movingChartAngularSymbol_degreeZero c d a m hDegree
  have hpMeas : Measurable (movingChartAngularSymbol c d a m) :=
    measurable_baseAngularSymbol
      (fun ξ => (contDiff_baseAngularSection p hpJ hp0 ξ).continuous)
      (fun x => hpJ.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hξ => ⟨mem_univ x, hξ⟩))
  obtain ⟨f', C, hC, hIdent, _, hBound, hWeak⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hnB hconv hb q
  have hF (n : ℕ) (k : JetSlot) : f' n k = f n k :=
    SchwartzMap.injective_toLp 2 volume (hIdent n k)
  have hBnd (γ : D) (k : JetSlot) (n : ℕ) :
      ‖(coeffMul γ (f (σ n) k)).toLp 2 volume‖ ≤ (physicalCoefficient γ).bound * C := by
    rw [coeffMul_toLp, ← hF]
    exact (symbolL2_norm_le _ _).trans
      (mul_le_mul_of_nonneg_left (hBound (σ n) k) (physicalCoefficient γ).bound_nonneg)
  have hW (γ : D) (k : JetSlot) (w : ComplexL2 E) :
      Tendsto (fun n => inner ℂ w ((coeffMul γ (f (σ n) k)).toLp 2 volume)) atTop (𝓝 0) := by
    have h := (hWeak k (symbolCLM (conjugateSymbol (physicalCoefficient γ)) w)).comp hσ.tendsto_atTop
    exact h.congr fun n => by
      dsimp only [Function.comp_apply]
      rw [coeffMul_toLp, ← hF, inner_symbolCLM_left, conjugateSymbol_conjugateSymbol]
  have hEach (k l : JetSlot) :=
    (tendsto_receivingSeparablePairing_sub_sourceAngularAction c d S hS hOuter (convex_closedBall _ _)
      a b m ha haS hm hDegree (fun n => coeffMul (α k) (f (σ n) k)) (fun n => coeffMul (β l) (f (σ n) l))
      (fun _ => (coeffMul_tsupport_subset _ _).trans ((hαS k).trans hKS))
      (fun _ => (coeffMul_tsupport_subset _ _).trans ((hβS l).trans hKS))
      (fun _ _ h => hPull _ (hαS k (coeffMul_tsupport_subset _ _ h)))
      _ _ (hBnd (α k) k) (hBnd (β l) l) (hW (β l) l)).add
    (tendsto_originalVolume_bilateralSourceAngular_to_rawDensity r B g hB hg hnB hconv hb q σ hσ ν hf hRep
      p S hS hpS hpJ hp0 hpD (α k) (β l) k l)
  simp only [p, f, sub_add_cancel, zero_add] at hEach
  have hSums := tendsto_finset_sum Finset.univ
    (fun k _ => tendsto_finset_sum Finset.univ (fun l _ => hEach k l))
  have hPhase := receivingWindow_integral_eq_sourceAngularSum r B g hB hg hsB hsG hnB hnG hconv hb hv
    σ hσ A hA q ν hf hRep d hK hSub η₀ η₁ i j α β a b m hBmeas hpMeas hm hDegree hαS hPull hα hβ
  rw [hPhase] at hSums
  change Tendsto (fun n => ∑ k : JetSlot, ∑ l : JetSlot,
    inner ℂ ((F n k).toLp 2 volume) (T ((G n l).toLp 2 volume))) atTop (𝓝 _) at hSums
  simpa only [sub_add_cancel, zero_add] using hReplace.add hSums

end Burnett.Microlocal.Overlap
