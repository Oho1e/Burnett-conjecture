import Burnett.Analysis.Microlocal.Overlap.OriginalCutoffRefinement
import Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal
import Burnett.Analysis.Microlocal.Overlap.OriginalGlobalAngularConsumer
import Burnett.Analysis.Microlocal.Overlap.OriginalWeakInput
import Burnett.Analysis.Microlocal.Overlap.LocalCutoffGradient
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact

/-! A given locally represented classical test on the actual two cutoff gradients. -/

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2300000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.UnitNullCompactness (cotangentCoords)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul coeffMul_toLp)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.SeparablePositive (inner_symbolCLM_left conjugateSymbol conjugateSymbol_conjugateSymbol)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ComplexConjugate ContDiff InnerProduct Manifold Topology

local notation "E" => CoordinateSpace

/-- A test operator in geometric half-density coordinates with actual fixed infrared
quantization of its principal symbol and a compact lower-order operator. Equality
is required on every Schwartz input supported in the specified right window. -/
def HasLocalClassicalRepresentation (T : ComplexL2 E →L[ℂ] ComplexL2 E)
    (a : E → E → ℂ) (L : Set E) : Prop :=
  ∃ R : ComplexL2 E →L[ℂ] ComplexL2 E, IsCompactOperator R ∧
    ∀ f v : SchwartzMap E ℂ, tsupport (v : E → ℂ) ⊆ L →
      inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) =
        (∫ x, conj (f x) * firstOrderAction (infraredAngularPrincipal a) v x) +
          inner ℂ (f.toLp 2 volume) (R (v.toLp 2 volume))

private theorem compactOperator_tendsto_zero_of_weakL2
    (R : ComplexL2 E →L[ℂ] ComplexL2 E) (hR : IsCompactOperator R)
    (v : ℕ → ComplexL2 E) (C : ℝ) (hC : ∀ n, ‖v n‖ ≤ C)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w (v n)) atTop (𝓝 0)) :
    Tendsto (fun n => R (v n)) atTop (𝓝 0) := by
  by_contra ht
  rw [Metric.tendsto_nhds] at ht
  push_neg at ht
  obtain ⟨ε, hε, hfreq⟩ := ht
  let S := closure (R '' Metric.closedBall 0 C)
  let W : Set (ComplexL2 E) := {z | ε ≤ ‖z‖}
  have hS : IsCompact S := hR.isCompact_closure_image_closedBall C
  have hW : IsClosed W := isClosed_le continuous_const continuous_norm
  have hInside (n : ℕ) : R (v n) ∈ S :=
    subset_closure ⟨v n, by simpa only [Metric.mem_closedBall, dist_zero_right] using hC n, rfl⟩
  have hDist : ∃ᶠ n in atTop, ε ≤ dist (R (v n)) 0 := by
    change ¬ ∀ᶠ n in atTop, ¬ ε ≤ dist (R (v n)) 0
    simpa only [not_le] using hfreq
  have hOften : ∃ᶠ n in atTop, R (v n) ∈ S ∩ W := hDist.mono fun n hn =>
    ⟨hInside n, by simpa only [W, mem_setOf_eq, dist_zero_right] using hn⟩
  obtain ⟨x, hx, s, hs, hLim⟩ := (hS.inter_right hW).isSeqCompact.subseq_of_frequently_in hOften
  have hNorm : Tendsto (fun n => inner ℂ x (R (v (s n)))) atTop (𝓝 (inner ℂ x x)) :=
    (continuous_const.inner continuous_id).continuousAt.tendsto.comp hLim
  have hWeak : Tendsto (fun n => inner ℂ x (R (v (s n)))) atTop (𝓝 0) := by
    simpa only [ContinuousLinearMap.adjoint_inner_left] using (hw (R.adjoint x)).comp hs.tendsto_atTop
  have hx0 : x = 0 := inner_self_eq_zero.mp (tendsto_nhds_unique hNorm hWeak)
  have hε' : ε ≤ ‖x‖ := hx.2
  rw [hx0, norm_zero] at hε'
  exact hε.not_ge hε'

private theorem inner_tendsto_zero_of_bounded_of_tendsto_zero
    (u v : ℕ → ComplexL2 E) (B : ℝ) (hu : ∀ n, ‖u n‖ ≤ B)
    (hv : Tendsto v atTop (𝓝 0)) : Tendsto (fun n => inner ℂ (u n) (v n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hNorm : Tendsto (fun n => B * ‖v n‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hv.norm.const_mul B
  apply squeeze_zero (fun _ => norm_nonneg _) _ hNorm
  intro n
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg _))

private theorem tsupport_physicalCoefficient_subset (η : D) :
    tsupport (physicalCoefficient η : E → ℂ) ⊆ tsupport (η : E → ℝ) := by
  apply closure_mono
  intro x hx
  exact fun hzero => hx (show ((η : E → ℝ) x : ℂ) = 0 by rw [hzero, Complex.ofReal_zero])

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- Keep the preferred chart and ball fixed and replace its original test cutoff. -/
def compactChartWithCutoff (q : CompactChartInput M) (η : D)
    (hη : tsupport (η : E → ℝ) ⊆ q.ball.closedBall) : CompactChartInput M :=
  {q with cutoff := η, cutoff_support := hη}

private theorem coeffMul_originalVolumeAngularInput (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B) (q : CompactChartInput M)
    (η : D) (hη : tsupport (η : E → ℝ) ⊆ q.ball.closedBall)
    (hNZ : ∀ x ∈ tsupport (η : E → ℝ), (q.cutoff : E → ℝ) x ≠ 0) (n : ℕ) (i : JetSlot) :
    coeffMul (cutoffQuotient η q.cutoff hNZ) (originalVolumeAngularInput B g hB hg hnB q n i) =
      originalVolumeAngularInput B g hB hg hnB (compactChartWithCutoff q η hη) n i := by
  apply SchwartzMap.injective_toLp 2 volume
  dsimp only
  rw [coeffMul_toLp]
  exact (originalGradient_volumeWeightedL2_of_cutoff_mul B g hB hg hnB q.center q.cutoff η
    (cutoffQuotient η q.cutoff hNZ) (q.cutoff_support.trans q.ball_in_chart) (hη.trans q.ball_in_chart)
    (cutoffQuotient_mul η q.cutoff hNZ) n i).symm

variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The given represented classical operator gives the expected two-cutoff integral
on the same global control and amplitude as the original compact chart tests. -/
theorem tendsto_originalVolume_classicalPairing_globalAmplitudeOn
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (K : Set M) (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus)
    (a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hSupport : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x))
    (η₀ η₁ : D) (hη₀ : tsupport (η₀ : E → ℝ) ⊆ (chartAt E q.center) '' K)
    (hη₁ : tsupport (η₁ : E → ℝ) ⊆ (chartAt E q.center) '' K)
    (T : ComplexL2 E →L[ℂ] ComplexL2 E)
    (hT : HasLocalClassicalRepresentation T a (tsupport (η₁ : E → ℝ))) (i j : JetSlot) :
    let hBall : (chartAt E q.center) '' K ⊆ q.ball.closedBall := fun _ ⟨_, hx, he⟩ =>
      he ▸ q.cutoff_support (subset_tsupport _ (hSub hx).2)
    let f₀ := originalVolumeAngularInput B g hB hg hnB (compactChartWithCutoff q η₀ (hη₀.trans hBall))
    let f₁ := originalVolumeAngularInput B g hB hg hnB (compactChartWithCutoff q η₁ (hη₁.trans hBall))
    let fA (p : Cosphere r) :=
      let x := chartAt E q.center (projection p)
      let ξ := cotangentCoords q.center p.val
      (((physicalCoefficient η₀ x * physicalCoefficient η₁ x) * a x (WithLp.toLp 2 ξ)) *
        (ξ i.1 : ℂ) * (ξ j.1 : ℂ)) * intrinsicAmplitudeMatrix q.center A.density p j.2 i.2
    Integrable fA (A.control.restrict (amplitudeCosphereWindow r K)) ∧
      Tendsto (fun n => inner ℂ ((f₀ (σ n) i).toLp 2 volume) (T ((f₁ (σ n) j).toLp 2 volume)))
        atTop (𝓝 (∫ p in amplitudeCosphereWindow r K, fA p ∂A.control)) := by
  intro hBall f₀ f₁ fA
  let f := originalVolumeAngularInput B g hB hg hnB q
  let S₀ := chartAt E q.center '' K
  have hNonzero (x : E) (hx : x ∈ S₀) : (q.cutoff : E → ℝ) x ≠ 0 := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact (hSub hy).2
  let c := cutoffQuotient η₀ q.cutoff (fun x hx => hNonzero x (hη₀ hx))
  let d := cutoffQuotient η₁ q.cutoff (fun x hx => hNonzero x (hη₁ hx))
  have h₀ (n : ℕ) : coeffMul c (f (σ n) i) = f₀ (σ n) i :=
    coeffMul_originalVolumeAngularInput B g hB hg hnB q η₀ (hη₀.trans hBall) _ (σ n) i
  have h₁ (n : ℕ) : coeffMul d (f (σ n) j) = f₁ (σ n) j :=
    coeffMul_originalVolumeAngularInput B g hB hg hnB q η₁ (hη₁.trans hBall) _ (σ n) j
  obtain ⟨F, C, hC, hFEq, hFS, hCB, hFW⟩ := exists_originalVolume_weakL2_representatives
    r B g hB hg hnB hconv hb q
  have hEq (n : ℕ) (k : JetSlot) : F n k = f n k :=
    SchwartzMap.injective_toLp 2 volume (hFEq n k)
  have hBound (n : ℕ) (k : JetSlot) : ‖(f n k).toLp 2 volume‖ ≤ C := by rw [← hEq]; exact hCB n k
  have hSupp (n : ℕ) : tsupport (f (σ n) j : E → ℂ) ⊆ q.ball.closedBall := by
    rw [← hEq]
    exact hFS (σ n) j
  have hWeak (w : ComplexL2 E) : Tendsto (fun n => inner ℂ w ((f (σ n) j).toLp 2 volume)) atTop (𝓝 0) :=
    ((hFW j w).comp hσ.tendsto_atTop).congr (fun n => by rw [Function.comp_apply, hEq])
  have hDiff := tendsto_infraredAngularPrincipal_twoCutoff_difference a S hS hSupport hJoint hZero hDegree
    c d (fun n => f (σ n) i) (fun n => f (σ n) j) q.ball.closedBall (isCompact_closedBall _ _)
    hSupp C C hC (fun n => hBound (σ n) i) (fun n => hBound (σ n) j) hWeak
  let aw (x ξ : E) := (physicalCoefficient η₀ x * physicalCoefficient η₁ x) * a x ξ
  have haWeighted : (fun x ξ => (physicalCoefficient c x * physicalCoefficient d x) * a x ξ) =
      inverseCutoffAngularSymbol q.cutoff aw := by
    funext x ξ
    change ((((η₀ : E → ℝ) x * ((q.cutoff : E → ℝ) x)⁻¹ : ℝ) : ℂ) *
      (((η₁ : E → ℝ) x * ((q.cutoff : E → ℝ) x)⁻¹ : ℝ) : ℂ)) * a x ξ = _
    unfold inverseCutoffAngularSymbol aw physicalCoefficient
    push_cast
    ring
  have hMw (η : D) : ContDiff ℝ ∞ (fun z : E × E => physicalCoefficient η z.1) :=
    (Complex.ofRealCLM.contDiff.comp (test_smooth η)).comp contDiff_fst
  have hAw : ContDiffOn ℝ ∞ (uncurry aw) (univ ×ˢ ({0}ᶜ : Set E)) :=
    ((hMw η₀).mul (hMw η₁)).contDiffOn.mul hJoint
  have hAw0 : ContDiff ℝ ∞ (fun x => aw x 0) :=
    ((Complex.ofRealCLM.contDiff.comp (test_smooth η₀)).mul
      (Complex.ofRealCLM.contDiff.comp (test_smooth η₁))).mul hZero
  have hAwS (ξ : E) : tsupport (fun x => aw x ξ) ⊆ S₀ :=
    tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans
      ((tsupport_physicalCoefficient_subset η₀).trans hη₀))
  have hAwD (x : E) : DegreeZero (aw x) := fun r hr ξ => by simp only [aw, hDegree x r hr ξ]
  obtain ⟨hIntegrable, hLim⟩ := tendsto_originalVolume_angularAction_globalAmplitudeOn r B g hB hg hsB hsG
    hnB hnG hconv hb hv q σ hσ ν hfin hRep A hA K hK hSub aw hAwS hAw hAw0 hAwD i j
  refine ⟨hIntegrable, ?_⟩
  have hPrincipal : Tendsto (fun n => ∫ x, conj (coeffMul c (f (σ n) i) x) *
      firstOrderAction (infraredAngularPrincipal a) (coeffMul d (f (σ n) j)) x)
      atTop (𝓝 (∫ p in amplitudeCosphereWindow r K, fA p ∂A.control)) := by
    rw [haWeighted] at hDiff
    have h := hDiff.add hLim
    simpa only [sub_add_cancel, zero_add, f] using h
  obtain ⟨R, hR, hRepT⟩ := hT
  let w (n : ℕ) := (coeffMul d (f (σ n) j)).toLp 2 volume
  have hwB (n : ℕ) : ‖w n‖ ≤ (physicalCoefficient d).bound * C := by
    dsimp only [w]
    rw [coeffMul_toLp]
    exact (symbolL2_norm_le _ _).trans (mul_le_mul_of_nonneg_left (hBound (σ n) j)
      (physicalCoefficient d).bound_nonneg)
  have hwWeak (v : ComplexL2 E) : Tendsto (fun n => inner ℂ v (w n)) atTop (𝓝 0) := by
    have hPair (n : ℕ) : inner ℂ v (w n) = inner ℂ
        (symbolCLM (conjugateSymbol (physicalCoefficient d)) v) ((f (σ n) j).toLp 2 volume) := by
      dsimp only [w]
      rw [coeffMul_toLp, inner_symbolCLM_left, conjugateSymbol_conjugateSymbol]
    simpa only [hPair] using hWeak (symbolCLM (conjugateSymbol (physicalCoefficient d)) v)
  have hStrong := compactOperator_tendsto_zero_of_weakL2 R hR w _ hwB hwWeak
  let u (n : ℕ) := (coeffMul c (f (σ n) i)).toLp 2 volume
  have huB (n : ℕ) : ‖u n‖ ≤ (physicalCoefficient c).bound * C := by
    dsimp only [u]
    rw [coeffMul_toLp]
    exact (symbolL2_norm_le _ _).trans (mul_le_mul_of_nonneg_left (hBound (σ n) i)
      (physicalCoefficient c).bound_nonneg)
  have hRPair := inner_tendsto_zero_of_bounded_of_tendsto_zero u (fun n => R (w n)) _ huB hStrong
  have hSum := hPrincipal.add hRPair
  rw [add_zero] at hSum
  apply hSum.congr
  intro n
  have hSup : tsupport (coeffMul d (f (σ n) j) : E → ℂ) ⊆ tsupport (η₁ : E → ℝ) :=
    tsupport_mul_subset_left.trans ((tsupport_physicalCoefficient_subset d).trans tsupport_mul_subset_left)
  rw [← h₀, ← h₁]
  exact (hRepT (coeffMul c (f (σ n) i)) (coeffMul d (f (σ n) j)) hSup).symm

end Burnett.Microlocal.Overlap
