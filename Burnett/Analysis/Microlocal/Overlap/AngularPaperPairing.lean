import Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical

/-! The manuscript's first-slot convention and ordered real principal-symbol tests. -/

set_option autoImplicit false
set_option maxRecDepth 2800
set_option maxHeartbeats 2000000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.UnitNullCompactness (cotangentCoords)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped ComplexConjugate ComplexOrder ContDiff InnerProduct Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

private theorem ae_intrinsicAmplitudeMatrix_posSemidef_on_originalWindow [T2Space M]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q : CompactChartInput M) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hfin)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (K : Set M) (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) :
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K), (intrinsicAmplitudeMatrix q.center A.density p).PosSemidef := by
  obtain ⟨hControl, hField⟩ := hA q ν hfin hRep K hK hSub
  have hPos := (original_compactChart_traceNormalizedAmplitude r B g hB hg hsB hsG hnB hnG
    hconv hb hv σ hσ q ν hfin hRep hK hSub).1
  have hWin := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  rw [hControl]
  filter_upwards [hField, hPos, ae_restrict_mem (μ := chartAmplitudeTraceControl r q ν hfin) hWin] with p hFieldP hPosP hp
  have hx : projection p ∈ (chartAt E q.center).source := (hSub hp).1
  rw [intrinsicAmplitudeMatrix_of_mem q.center A.density p hx, hFieldP,
    ← intrinsicAmplitudeMatrix_of_mem q.center _ p hx,
    intrinsicAmplitudeMatrix_chartNormalized_of_mem r q ν hfin p hx]
  exact hPosP.1

/-- A real principal symbol in the manuscript's first-linear pairing reads the
ordered covariance entry `i.2,j.2` on the unchanged original trace. The equality
of the actual two integrals explicitly records the Hermitian conjugation. -/
theorem tendsto_originalVolume_paperRealClassicalPairing_globalAmplitudeOn [T2Space M]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
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
    (a : E → E → ℝ) (S : Set E) (hS : IsCompact S)
    (hSupport : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => a x 0))
    (hDegree : ∀ x (t : ℝ), 0 < t → ∀ ξ : E, a x (t • ξ) = a x ξ)
    (η₀ η₁ : D) (hη₀ : tsupport (η₀ : E → ℝ) ⊆ (chartAt E q.center) '' K)
    (hη₁ : tsupport (η₁ : E → ℝ) ⊆ (chartAt E q.center) '' K)
    (T : ComplexL2 E →L[ℂ] ComplexL2 E)
    (hT : HasLocalClassicalRepresentation T (fun x ξ => (a x ξ : ℂ)) (tsupport (η₁ : E → ℝ)))
    (i j : JetSlot) :
    let hBall : (chartAt E q.center) '' K ⊆ q.ball.closedBall := fun _ ⟨_, hx, he⟩ =>
      he ▸ q.cutoff_support (subset_tsupport _ (hSub hx).2)
    let f₀ := originalVolumeAngularInput B g hB hg hnB (compactChartWithCutoff q η₀ (hη₀.trans hBall))
    let f₁ := originalVolumeAngularInput B g hB hg hnB (compactChartWithCutoff q η₁ (hη₁.trans hBall))
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let w (p : Cosphere r) : ℂ :=
      let x := chartAt E q.center (projection p)
      let ξ := cotangentCoords q.center p.val
      (((η₀ : E → ℝ) x * (η₁ : E → ℝ) x * a x (WithLp.toLp 2 ξ)) * ξ i.1 * ξ j.1 : ℝ)
    let F (p : Cosphere r) := w p * intrinsicAmplitudeMatrix q.center A.density p j.2 i.2
    let G (p : Cosphere r) := w p * intrinsicAmplitudeMatrix q.center A.density p i.2 j.2
    Integrable G τ ∧ conj (∫ p, F p ∂τ) = ∫ p, G p ∂τ ∧
      Tendsto (fun n => inner ℂ (T ((f₁ (σ n) j).toLp 2 volume)) ((f₀ (σ n) i).toLp 2 volume))
        atTop (𝓝 (∫ p, G p ∂τ)) := by
  intro hBall f₀ f₁ τ w F G
  let aC (x ξ : E) : ℂ := a x ξ
  have hSC (ξ : E) : tsupport (fun x => aC x ξ) ⊆ S := by
    apply (closure_mono _).trans (hSupport ξ)
    intro x hx h
    exact hx (show aC x ξ = 0 by simp only [aC, h, Complex.ofReal_zero])
  have hJC : ContDiffOn ℝ ∞ (uncurry aC) (univ ×ˢ ({0}ᶜ : Set E)) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hJoint
  have hZC : ContDiff ℝ ∞ (fun x => aC x 0) := Complex.ofRealCLM.contDiff.comp hZero
  have hDC (x : E) : Burnett.Microlocal.AngularCommutator.DegreeZero (aC x) := by
    intro t ht ξ
    exact congrArg Complex.ofReal (hDegree x t ht ξ)
  obtain ⟨hI, hLim⟩ := tendsto_originalVolume_classicalPairing_globalAmplitudeOn r B g hB hg hsB hsG hnB hnG
    hconv hb hv q σ hσ ν hfin hRep A hA K hK hSub aC S hS hSC hJC hZC hDC η₀ η₁ hη₀ hη₁ T hT i j
  have hConj : (fun p => conj (F p)) =ᵐ[τ] G := by
    have hPos := ae_intrinsicAmplitudeMatrix_posSemidef_on_originalWindow r B g hB hg hsB hsG hnB hnG
      hconv hb hv q σ hσ ν hfin hRep A hA K hK hSub
    filter_upwards [hPos] with p hp
    have hHerm := hp.isHermitian.apply i.2 j.2
    change conj (intrinsicAmplitudeMatrix q.center A.density p j.2 i.2) = _ at hHerm
    simp only [F, G, map_mul, w, Complex.conj_ofReal, hHerm]
  have hCast : (fun p : Cosphere r =>
      let x := chartAt E q.center (projection p)
      let ξ := cotangentCoords q.center p.val
      (((Burnett.Microlocal.BesselLocalization.physicalCoefficient η₀ x *
          Burnett.Microlocal.BesselLocalization.physicalCoefficient η₁ x) * aC x (WithLp.toLp 2 ξ)) *
        (ξ i.1 : ℂ) * (ξ j.1 : ℂ)) * intrinsicAmplitudeMatrix q.center A.density p j.2 i.2) = F := by
    funext p
    dsimp only [F, w, aC, Burnett.Microlocal.BesselLocalization.physicalCoefficient]
    push_cast
    rfl
  rw [hCast] at hI hLim
  have hIntegral : conj (∫ p, F p ∂τ) = ∫ p, G p ∂τ :=
    integral_conj.symm.trans (integral_congr_ae hConj)
  have hIG : Integrable (fun p => conj (F p)) τ :=
    hI.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hI.aestronglyMeasurable)
      (Eventually.of_forall fun _ => (Complex.norm_conj _).le)
  refine ⟨hIG.congr hConj, hIntegral, ?_⟩
  have h := (Complex.continuous_conj.tendsto (∫ p, F p ∂τ)).comp hLim
  rw [hIntegral] at h
  exact h.congr (fun _ => inner_conj_symm _ _)

end Burnett.Microlocal.Overlap
