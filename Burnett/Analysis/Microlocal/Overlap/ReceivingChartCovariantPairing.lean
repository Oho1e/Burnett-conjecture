import Burnett.Analysis.Microlocal.Overlap.ReceivingChartCovariantGradient
import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingClassicalPairings
import Burnett.Analysis.Microlocal.Overlap.PairingReplacement

/-! The true auxiliary derivatives give the same pairings on the same
subsequence and with the same representing measure. -/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open UnitCosphere (Cosphere)
open FixedCotangentChart (fixedChartPhase)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeGradientSchwartz fixedVolumeGradient_weak_and_uniform_L2
  fixedVolumeCovariantGradientSchwartz fixedVolumeCovariantGradient_sub_partial_tendsto_zero)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff Manifold Topology InnerProduct

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

theorem fixedVolumeCovariantGradient_weak_and_uniform_L2
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) :
    let u := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ
    ∃ C : ℝ, 0 ≤ C ∧ (∀ n i, ‖(u n i).toLp 2 volume‖ ≤ C) ∧
      ∀ i (v : ComplexL2 E), Tendsto (fun n => inner ℂ v ((u n i).toLp 2 volume)) atTop (𝓝 0) := by
  intro u
  let v := fixedVolumeGradientSchwartz B g hB hg hn c χ hχ
  let e (i : JetSlot) (n : ℕ) : ComplexL2 E := (u n i).toLp 2 volume - (v n i).toLp 2 volume
  obtain ⟨C, hC, hBv, hWeak⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hn hconv hb c χ hχ
  have hE (i : JetSlot) : Tendsto (e i) atTop (𝓝 0) :=
    fixedVolumeCovariantGradient_sub_partial_tendsto_zero r B g hB hg hn hconv c χ hχ i
  have hA (i : JetSlot) : ∃ A : ℝ, 0 < A ∧ ∀ n, ‖e i n‖ ≤ A := by
    obtain ⟨A, hA, hB⟩ := (Metric.isBounded_range_of_tendsto (e i) (hE i)).exists_pos_norm_le
    exact ⟨A, hA, fun n => hB _ (mem_range_self n)⟩
  choose A hA hBA using hA
  refine ⟨(∑ i, A i) + C, add_nonneg (Finset.sum_nonneg (fun i _ => (hA i).le)) hC, ?_, ?_⟩
  · intro n i
    have hAi : A i ≤ ∑ j : JetSlot, A j :=
      Finset.single_le_sum (fun j _ => (hA j).le) (Finset.mem_univ i)
    exact (norm_le_norm_sub_add ((u n i).toLp 2 volume) ((v n i).toLp 2 volume)).trans
      (add_le_add ((hBA i n).trans hAi) (hBv n i))
  intro i w
  have hCont : Continuous (fun z : ComplexL2 E => inner ℂ w z) := continuous_const.inner continuous_id
  have hWeakE : Tendsto (fun n => inner ℂ w (e i n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, inner_zero_right] using (hCont.tendsto 0).comp (hE i)
  have hWeakV : Tendsto (fun n => inner ℂ w ((v n i).toLp 2 volume)) atTop (𝓝 0) := hWeak i w
  simpa only [e, inner_sub_right, sub_add_cancel, zero_add] using hWeakE.add hWeakV

/-- Both slots may use the actual auxiliary derivative, with independent
cutoffs and any one fixed bounded operator in the manuscript order. -/
theorem tendsto_fixedVolumeCovariantPaperPairing_sub_partial
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart.target)
    (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart.target)
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (i j : JetSlot) :
    let u₀ n := (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η₀ h₀ n i).toLp 2 volume
    let u₁ n := (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η₁ h₁ n j).toLp 2 volume
    let v₀ n := (fixedVolumeGradientSchwartz B g hB hg hn c η₀ h₀ n i).toLp 2 volume
    let v₁ n := (fixedVolumeGradientSchwartz B g hB hg hn c η₁ h₁ n j).toLp 2 volume
    Tendsto (fun n => inner ℂ (T (u₁ n)) (u₀ n) - inner ℂ (T (v₁ n)) (v₀ n)) atTop (𝓝 0) := by
  intro u₀ u₁ v₀ v₁
  obtain ⟨Cu, _, hU, _⟩ := fixedVolumeCovariantGradient_weak_and_uniform_L2 r B g hB hg hn hconv hb c η₁ h₁
  obtain ⟨Cv, _, hV, _⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hn hconv hb c η₀ h₀
  have hErr := tendsto_orderedPairing_sub_of_strong_replacement T u₀ u₁ v₀ v₁ Cu Cv
    (fun n => hU n j) (fun n => hV n i)
    (fixedVolumeCovariantGradient_sub_partial_tendsto_zero r B g hB hg hn hconv c η₀ h₀ i)
    (fixedVolumeCovariantGradient_sub_partial_tendsto_zero r B g hB hg hn hconv c η₁ h₁ j)
  have hConj := (Complex.continuous_conj.tendsto (0 : ℂ)).comp hErr
  change Tendsto (fun n => conj (inner ℂ (u₀ n) (T (u₁ n)) - inner ℂ (v₀ n) (T (v₁ n))))
    atTop (𝓝 (conj (0 : ℂ))) at hConj
  simpa only [map_sub, inner_conj_symm, map_zero] using hConj

variable [T2Space M]

/-- The represented paper tests on the original (D h_n) in every compatible
chart, with the same symbol evaluated on the actual auxiliary unit cosphere. -/
def HasOriginalReceivingCovariantPaperPairings
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r) : Prop :=
  ∀ (c : AtlasChart M) (K : Set M), IsCompact K → ∀ (hKc : K ⊆ c.chart.source)
    (a : E → E → ℂ) (S : Set E), IsCompact S →
    (∀ ξ, tsupport (fun x => a x ξ) ⊆ S) →
    ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)) →
    ContDiff ℝ ∞ (fun x => a x 0) → (∀ x, DegreeZero (a x)) →
    ∀ (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart '' K)
      (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart '' K) (T : ComplexL2 E →L[ℂ] ComplexL2 E),
    HasLocalClassicalRepresentation T a (tsupport (η₁ : E → ℝ)) → ∀ i j : JetSlot,
      let h₀c := h₀.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
      let h₁c := h₁.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
      let u := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η₀ h₀c
      let v := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η₁ h₁c
      let τ := A.control.restrict (amplitudeCosphereWindow r K)
      let G (p : Cosphere r) :=
        let z := fixedChartPhase c p.val
        conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a z.1 (WithLp.toLp 2 z.2)) *
          atlasOrderedJetEntry c A.density p j i
      Integrable G τ ∧
        Tendsto (fun n => inner ℂ (T ((v (σ n) j).toLp 2 volume)) ((u (σ n) i).toLp 2 volume))
          atTop (𝓝 (∫ p, G p ∂τ))

omit [T2Space M] in
theorem hasOriginalReceivingCovariantPaperPairings_of_partial
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (A : IntrinsicAmplitudeCovariance r)
    (hP : HasOriginalReceivingPaperPairings r B g hB hg hn σ A) :
    HasOriginalReceivingCovariantPaperPairings r B g hB hg hn σ A := by
  intro c K hK hKc a S hS hAS hJoint hZero hDegree η₀ η₁ h₀ h₁ T hT i j h₀c h₁c u v τ G
  obtain ⟨hI, hLim⟩ := hP c K hK hKc a S hS hAS hJoint hZero hDegree η₀ η₁ h₀ h₁ T hT i j
  have hErr := (tendsto_fixedVolumeCovariantPaperPairing_sub_partial r B g hB hg hn hconv hb
    c η₀ η₁ h₀c h₁c T i j).comp hσ.tendsto_atTop
  refine ⟨hI, ?_⟩
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hErr.add hLim

theorem hasOriginalReceivingCovariantPaperPairings_of_intrinsicAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A) :
    HasOriginalReceivingCovariantPaperPairings r B g hB hg hnB σ A :=
  hasOriginalReceivingCovariantPaperPairings_of_partial r B g hB hg hnB hconv hb σ hσ A
    (hasOriginalReceivingPaperPairings_of_intrinsicAmplitude r B g hB hg hsB hsG hnB hnG
      hconv hb hv σ hσ A hA)

end Burnett.Microlocal.Overlap
