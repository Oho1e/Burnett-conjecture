import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingClassicalPairings
import Burnett.Analysis.Microlocal.Overlap.SupportedWeakFourier

/-! Concrete separated angular operators on arbitrary original receiving windows. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2400000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularDyadicKernel (normalizedAngularSymbol boundedRadialCore radialCore
  fourierMultiplier_schwartz_eq_inverse_mul_ae)
open Burnett.Microlocal.AngularCommutator (DegreeZero symbolDifference fourierMultiplier_symbolDifference)
open Burnett.Microlocal.SeparablePositive (separableOperator)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeGradientSchwartz fixedVolumeGradientSchwartz_tsupport
  fixedVolumeGradient_weak_and_uniform_L2)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Manifold Topology

local notation "E" => CoordinateSpace

open private firstOrderAction_mul_base from Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal

theorem infraredSeparable_hasLocalClassicalRepresentation (b m : BoundedSymbol E) (L : Set E) :
    HasLocalClassicalRepresentation (separableOperator b (normalizedAngularSymbol m))
      (fun x ξ => b x * m ξ) L := by
  refine ⟨0, isCompactOperator_zero, ?_⟩
  intro u v _
  simp only [ContinuousLinearMap.zero_apply, inner_zero_right, add_zero]
  have hAction (x : E) : firstOrderAction (infraredAngularPrincipal (fun y ξ => b y * m ξ)) v x =
      b x * (𝓕⁻ (fun ξ => normalizedAngularSymbol m ξ * (𝓕 (v : E → ℂ)) ξ)) x := by
    have hSymbol : infraredAngularPrincipal (fun y ξ => b y * m ξ) =
        fun y ξ => b y * normalizedAngularSymbol m ξ := by
      funext y ξ
      change (1 - (radialCore ξ : ℂ)) * (b y * m ξ) =
        b y * ((1 - (radialCore ((1 : ℝ) • ξ) : ℂ)) * m ξ)
      rw [one_smul]
      ac_rfl
    rw [hSymbol, firstOrderAction_mul_base]
    rfl
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u.coeFn_toLp 2 volume,
      symbolL2_ae b (fourierMultiplier (normalizedAngularSymbol m) (v.toLp 2 volume)),
      fourierMultiplier_schwartz_eq_inverse_mul_ae (normalizedAngularSymbol m) v] with x hx hSym hF
  change inner ℂ ((u.toLp 2 volume : E → ℂ) x)
    ((symbolL2 b (fourierMultiplier (normalizedAngularSymbol m) (v.toLp 2 volume))) x) = _
  rw [RCLike.inner_apply', hx, hSym, hF, hAction]

theorem infraredSeparable_difference_tendsto_zero (b m : BoundedSymbol E)
    (f : ℕ → SchwartzMap E ℂ) (K : Set E) (hK : IsCompact K)
    (hs : ∀ n, tsupport (f n : E → ℂ) ⊆ K) (C : ℝ)
    (hC : ∀ n, ‖(f n).toLp 2 volume‖ ≤ C)
    (hw : ∀ v : ComplexL2 E, Tendsto (fun n => inner ℂ v ((f n).toLp 2 volume)) atTop (𝓝 0)) :
    Tendsto (fun n => separableOperator b (normalizedAngularSymbol m) ((f n).toLp 2 volume) -
      separableOperator b m ((f n).toLp 2 volume)) atTop (𝓝 0) := by
  let q := symbolDifference (normalizedAngularSymbol m) m
  have hSupport (ξ : E) (hξ : ξ ∉ Metric.closedBall (0 : E) 2) : q ξ = 0 :=
    sub_eq_zero.mpr (normalizedAngularSymbol_eq_outside_ball m ξ hξ)
  have hLow := low_frequency_energy_tendsto_zero_of_supported_weakL2 K hK f hs C hC hw 2
  have h := fourierMultiplier_schwartz_tendsto_zero q Metric.isClosed_closedBall.measurableSet hSupport f hLow
  have hL := ((symbolCLM b).continuous.tendsto (0 : ComplexL2 E)).comp h
  change Tendsto (fun n => symbolCLM b (fourierMultiplier q ((f n).toLp 2 volume)))
    atTop (𝓝 (symbolCLM b 0)) at hL
  simpa only [q, fourierMultiplier_symbolDifference, map_sub, map_zero, separableOperator,
    ContinuousLinearMap.comp_apply] using hL

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- On the original receiving sequence the unregularized separated
angular action gives the same ordered jet entries as its classical representative. -/
theorem tendsto_originalVolume_receivingSeparablePairing
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (b m : BoundedSymbol E) (hSmooth : ContDiff ℝ ∞ (b : E → ℂ)) (hSup : HasCompactSupport (b : E → ℂ))
    (hM : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hDeg : DegreeZero (m : E → ℂ))
    (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart '' K)
    (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart '' K) (i j : JetSlot) :
    let h₀c := h₀.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let h₁c := h₁.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u := fixedVolumeGradientSchwartz B g hB hg hnB c η₀ h₀c
    let v := fixedVolumeGradientSchwartz B g hB hg hnB c η₁ h₁c
    let G := receivingClassicalTest c A (fun x ξ => b x * m ξ) η₀ η₁ i j
    IntegrableOn G (amplitudeCosphereWindow r K) A.control ∧
      Tendsto (fun n => inner ℂ ((u (σ n) i).toLp 2 volume)
        (separableOperator b m ((v (σ n) j).toLp 2 volume)))
        atTop (𝓝 (∫ p in amplitudeCosphereWindow r K, G p ∂A.control)) := by
  intro h₀c h₁c u v G
  let a (x ξ : E) := b x * m ξ
  have hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)) :=
    (hSmooth.comp contDiff_fst).contDiffOn.mul (hM.comp contDiff_snd.contDiffOn (fun _ h => h.2))
  have hZero : ContDiff ℝ ∞ (fun x => a x 0) := hSmooth.mul contDiff_const
  have hEqDeg (x : E) : DegreeZero (a x) := fun s hs ξ => congrArg (fun z : ℂ => b x * z) (hDeg s hs ξ)
  have hAS (ξ : E) : tsupport (fun x => a x ξ) ⊆ tsupport (b : E → ℂ) := tsupport_mul_subset_left
  obtain ⟨hI, hLim⟩ := tendsto_originalVolume_receivingClassicalPairing_globalAmplitude r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA c K hK hKc a (tsupport (b : E → ℂ)) hSup hAS hJoint hZero hEqDeg
    η₀ η₁ h₀ h₁ (separableOperator b (normalizedAngularSymbol m))
    (infraredSeparable_hasLocalClassicalRepresentation b m _) i j
  refine ⟨hI, ?_⟩
  obtain ⟨C, _, hU, _⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hnB hconv hb c η₀ h₀c
  obtain ⟨D₁, _, hV, hW⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hnB hconv hb c η₁ h₁c
  have hErr := infraredSeparable_difference_tendsto_zero b m (fun n => v n j) (tsupport (η₁ : E → ℝ))
    (test_compactSupport η₁) (fun n => fixedVolumeGradientSchwartz_tsupport B g hB hg hnB c η₁ h₁c n j)
    D₁ (fun n => hV n j) (hW j)
  let e (n : ℕ) := separableOperator b (normalizedAngularSymbol m) ((v n j).toLp 2 volume) -
    separableOperator b m ((v n j).toLp 2 volume)
  have hPair : Tendsto (fun n => inner ℂ ((u (σ n) i).toLp 2 volume) (e (σ n))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hN : Tendsto (fun n => C * ‖e (σ n)‖) atTop (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using (hErr.comp hσ.tendsto_atTop).norm.const_mul C
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => (norm_inner_le_norm _ _).trans ?_) hN
    exact mul_le_mul_of_nonneg_right (hU (σ n) i) (norm_nonneg _)
  change Tendsto (fun n => inner ℂ ((u (σ n) i).toLp 2 volume)
    (separableOperator b (normalizedAngularSymbol m) ((v (σ n) j).toLp 2 volume)))
    atTop (𝓝 (∫ p in amplitudeCosphereWindow r K, G p ∂A.control)) at hLim
  simpa only [e, inner_sub_right, sub_sub_cancel, sub_zero] using hLim.sub hPair

end Burnett.Microlocal.Overlap
