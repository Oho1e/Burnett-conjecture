import Burnett.Analysis.Microlocal.Overlap.ReceivingChartFixedInputLimit
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartClassicalExtension
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartBaseModes
import Burnett.Analysis.Microlocal.Overlap.ReceivingOriginalSourceReplacement
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartWeakInputs
import Burnett.Analysis.Microlocal.Overlap.PairingReplacement

/-! The actual given classical operator on two original receiving-chart
inputs has the joint principal limit of the original intrinsic amplitude. -/

set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 3600

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open UnitCosphere (Cosphere)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeGradientSchwartz fixedVolumeGradientSchwartz_tsupport
  fixedVolumeGradient_weak_and_uniform_L2 exists_receivingSourceCutoffs_of_originalVolume)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.SeparablePositive (separableOperator)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped BigOperators ContDiff InnerProduct Manifold Topology

open private coeffMul_tsupport_subset from Burnett.Analysis.Microlocal.Overlap.ReceivingChartFixedInputLimit

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- On one arbitrary receiving overlap, with its two actual compact
cutoffs, the given represented classical operator has the joint angular
limit on the same intrinsic control and the same original subsequence. -/
theorem tendsto_originalVolume_receivingClassicalPairing_on_compact
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
    (a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hAS : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x))
    (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ d.chart '' K)
    (h₁ : tsupport (η₁ : E → ℝ) ⊆ d.chart '' K)
    (h₀d : tsupport (η₀ : E → ℝ) ⊆ d.chart.target)
    (h₁d : tsupport (η₁ : E → ℝ) ⊆ d.chart.target)
    (T : ComplexL2 E →L[ℂ] ComplexL2 E)
    (hT : HasLocalClassicalRepresentation T a (tsupport (η₁ : E → ℝ)))
    (i j : JetSlot) :
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let W (p : Cosphere r) :=
      let z := atlasAngularPhaseCode d p
      ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a z.1 z.2.val) *
        atlasOrderedJetEntry d A.density p i j
    let u := fixedVolumeGradientSchwartz B g hB hg hnB d η₀ h₀d
    let v := fixedVolumeGradientSchwartz B g hB hg hnB d η₁ h₁d
    Integrable W τ ∧
      Tendsto (fun n => inner ℂ ((u (σ n) i).toLp 2 volume) (T ((v (σ n) j).toLp 2 volume)))
        atTop (𝓝 (∫ p, W p ∂τ)) := by
  intro τ W u v
  let c := AtlasChart.atPoint q.center
  let L := c.chart '' K
  let J (p : Cosphere r) := atlasOrderedJetEntry d A.density p i j
  let Θ := atlasAngularPhaseCode (r := r) d
  let base (p : Cosphere r) := (Θ p).1
  let ξ (p : Cosphere r) := (Θ p).2.val
  let w (p : Cosphere r) := physicalCoefficient η₀ (base p) * physicalCoefficient η₁ (base p)
  let ρ (p : Cosphere r) := w p * J p
  have hCc : K ⊆ c.chart.source := fun _ hx => (hSub hx).1.1
  have hLc : IsCompact L := hK.image_of_continuousOn (c.chart.continuousOn.mono hCc)
  have hOpen : IsOpen {x : E | (q.cutoff : E → ℝ) x ≠ 0} :=
    (isClosed_eq (test_smooth q.cutoff).continuous continuous_const).isOpen_compl
  have hCut : {x : E | (q.cutoff : E → ℝ) x ≠ 0} ⊆ q.ball.closedBall :=
    fun x hx => q.cutoff_support (subset_tsupport _ hx)
  have hLI : L ⊆ interior q.ball.closedBall := by
    apply (show L ⊆ {x : E | (q.cutoff : E → ℝ) x ≠ 0} from ?_).trans (interior_maximal hCut hOpen)
    rintro _ ⟨x, hx, rfl⟩
    exact (hSub hx).1.2
  obtain ⟨C, _, hU, _⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hnB hconv hb d η₀ h₀d
  obtain ⟨Cright, _, hV, hWeak⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hnB hconv hb d η₁ h₁d
  obtain ⟨α, hαS, hα, hαApprox⟩ := exists_receivingSourceCutoffs_of_originalVolume r B g hB hg hnB hconv
    q d hOuter hK hSub η₀ h₀ h₀d i
  obtain ⟨β, hβS, hβ, hβApprox⟩ := exists_receivingSourceCutoffs_of_originalVolume r B g hB hg hnB hconv
    q d hOuter hK hSub η₁ h₁ h₁d j
  have hControl := (hA q ν hf hRep K hK (hSub.trans inter_subset_left)).1
  letI : IsFiniteMeasure τ := ⟨by
    change (A.control.restrict (amplitudeCosphereWindow r K)) univ < ⊤
    rw [hControl, Measure.restrict_apply_univ]
    exact chartAmplitudeTraceControl_lt_top_on_compact r q ν hf hK (hSub.trans inter_subset_left)⟩
  have hJ : Integrable J τ :=
    (original_receivingAtlasJetEntry_angularMeasure_on_compact r B g hB hg hsB hsG hnB hnG hconv hb hv
      σ hσ A hA q ν hf hRep d hK hSub i j).1
  have hΘ := atlasAngularPhaseCode_measurable r d
  have hξ : Measurable ξ := measurable_subtype_coe.comp hΘ.snd
  have hη (η : D) : Continuous (physicalCoefficient η : E → ℂ) :=
    (Complex.ofRealCLM.contDiff.comp (test_smooth η)).continuous
  have hw : Measurable w :=
    (((hη η₀).measurable.comp hΘ.fst).mul ((hη η₁).measurable.comp hΘ.fst))
  let A₀ := (physicalCoefficient η₀).bound
  let A₁ := (physicalCoefficient η₁).bound
  have hwB (p : Cosphere r) : ‖w p‖ ≤ A₀ * A₁ := by
    rw [show w p = physicalCoefficient η₀ (base p) * physicalCoefficient η₁ (base p) from rfl, norm_mul]
    exact mul_le_mul ((physicalCoefficient η₀).norm_le _) ((physicalCoefficient η₁).norm_le _)
      (norm_nonneg _) (physicalCoefficient η₀).bound_nonneg
  have hρ : Integrable ρ τ := hJ.bdd_mul hw.aestronglyMeasurable ⟨A₀ * A₁, hwB⟩
  have haMeas : Measurable (uncurry a) :=
    measurable_baseAngularSymbol (fun ξ => (contDiff_baseAngularSection a hJoint hZero ξ).continuous)
      (fun x => hJoint.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hx => ⟨mem_univ x, hx⟩))
  obtain ⟨A₂, hA₂, hAB⟩ := exists_uniform_baseDerivative_of_homogeneousAngular a S hS hAS hJoint hZero hDegree 0
  have haB (x ξ : E) : ‖a x ξ‖ ≤ A₂ := by simpa only [norm_iteratedFDeriv_zero] using hAB x ξ
  have hInt : Integrable (fun p => a (base p) (ξ p) * ρ p) τ :=
    hρ.bdd_mul (haMeas.comp (hΘ.fst.prodMk hξ)).aestronglyMeasurable ⟨A₂, fun p => haB (base p) (ξ p)⟩
  have hSep (k : E) (m : BoundedSymbol E)
      (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ)) :
      Tendsto (fun n => inner ℂ ((u (σ n) i).toLp 2 volume)
        (separableOperator (baseFourierPhaseSymbol k) (normalizedAngularSymbol m) ((v (σ n) j).toLp 2 volume)))
        atTop (𝓝 (∫ p, baseFourierPhase k (base p) * m (ξ p) * ρ p ∂τ)) := by
    let b := baseFourierPhaseSymbol k
    let U (n : ℕ) := (u (σ n) i).toLp 2 volume
    let V (n : ℕ) := (v (σ n) j).toLp 2 volume
    let P := separableOperator b (normalizedAngularSymbol m)
    obtain ⟨b', hb', hb'S, _, hpull⟩ := exists_receivingBaseMode_pullback c d L
      q.ball.closedBall hLc hLI hOuter b (contDiff_baseFourierPhaseSymbol k)
    have hLim := tendsto_receivingWindow_separablePairing_of_transportedSlots r B g hB hg hsB hsG hnB hnG hconv hb hv
      σ hσ A hA q ν hf hRep d hK hSub hOuter η₀ η₁ i j α β b' b m hb' hb'S
      (contDiff_baseFourierPhaseSymbol k).continuous.measurable hm hd hαS hβS hpull hα hβ U V
    dsimp only at hLim
    have hApprox := hLim (by
      let S₀ := q.ball.closedBall
      let hS₀ : IsCompact S₀ := isCompact_closedBall _ _
      let hKS : c.chart '' K ⊆ S₀ := fun _ ⟨_, hx, he⟩ =>
        he ▸ q.cutoff_support (subset_tsupport _ (hSub hx).1.2)
      let f := originalVolumeAngularInput B g hB hg hnB q
      let F (n : ℕ) (k : JetSlot) := AtlasOverlapKernel.transportedHalfDensitySchwartz c d S₀ hS₀ hOuter
        (coeffMul (α k) (f (σ n) k))
        ((coeffMul_tsupport_subset _ _).trans ((hαS k).trans hKS))
      let G (n : ℕ) (l : JetSlot) := AtlasOverlapKernel.transportedHalfDensitySchwartz c d S₀ hS₀ hOuter
        (coeffMul (β l) (f (σ n) l))
        ((coeffMul_tsupport_subset _ _).trans ((hβS l).trans hKS))
      let U' (n : ℕ) : ComplexL2 E := ∑ k : JetSlot, (F n k).toLp 2 volume
      let V' (n : ℕ) : ComplexL2 E := ∑ l : JetSlot, (G n l).toLp 2 volume
      have hErr : Tendsto (fun n => U n - U' n) atTop (𝓝 0) := hαApprox.comp hσ.tendsto_atTop
      have hErr' : Tendsto (fun n => V n - V' n) atTop (𝓝 0) := hβApprox.comp hσ.tendsto_atTop
      obtain ⟨H, _, hh⟩ := (Metric.isBounded_range_of_tendsto _ hErr).exists_pos_norm_le
      have hU' (n : ℕ) : ‖U' n‖ ≤ H + C := by
        have hE : ‖U' n - U n‖ ≤ H := by
          rw [norm_sub_rev]
          exact hh _ (mem_range_self n)
        exact (norm_le_norm_sub_add (U' n) (U n)).trans (add_le_add hE (hU (σ n) i))
      have hReplacement := tendsto_orderedPairing_sub_of_strong_replacement P U V U' V' Cright (H + C)
        (fun n => hV (σ n) j) hU' hErr hErr'
      have hFinite (n : ℕ) : inner ℂ (U' n) (P (V' n)) =
          ∑ k : JetSlot, ∑ l : JetSlot, inner ℂ ((F n k).toLp 2 volume) (P ((G n l).toLp 2 volume)) := by
        unfold U' V'
        rw [sum_inner]
        exact Finset.sum_congr rfl (fun k _ => by rw [map_sum, inner_sum])
      exact hReplacement.congr (fun n => congrArg (fun z => inner ℂ (U n) (P (V n)) - z) (hFinite n)))
    have hEq : (∫ p, ((physicalCoefficient η₀ (base p) * physicalCoefficient η₁ (base p)) *
        b (base p) * m (ξ p)) * J p ∂τ) =
        ∫ p, baseFourierPhase k (base p) * m (ξ p) * ρ p ∂τ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        dsimp only [ρ, w, b, baseFourierPhaseSymbol]
        ring
    exact hEq ▸ hApprox
  have hLim := tendsto_receivingClassicalPairing_of_separated τ base ξ hΘ.fst hξ ρ hρ
    a S hS hAS hJoint hZero hDegree (fun n => u (σ n) i) (fun n => v (σ n) j)
    (tsupport (η₁ : E → ℝ)) (fun n => fixedVolumeGradientSchwartz_tsupport B g hB hg hnB d η₁ h₁d (σ n) j)
    C Cright (fun n => hU (σ n) i) (fun n => hV (σ n) j)
    (fun w => (hWeak j w).comp hσ.tendsto_atTop) hSep T hT
  have hW (p : Cosphere r) : W p = a (base p) (ξ p) * ρ p := by
    dsimp [W, ρ, w, J, base, ξ]
    ring
  exact ⟨hInt.congr (Eventually.of_forall (fun p => (hW p).symm)), by simpa only [hW] using hLim⟩

end Burnett.Microlocal.Overlap
