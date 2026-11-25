import Burnett.Analysis.Microlocal.Overlap.CompactSymmetricJetWindowData
import Burnett.Analysis.Microlocal.Overlap.SymmetricJetActualLocalSymbol

/-! The actual local limit only uses full symbols on its fixed compact window. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 6200000
set_option synthInstance.maxHeartbeats 360000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase fixedChartPhase_of_mem)
open Burnett.Microlocal.AtlasVolumeGradient
  (fixedVolumeCovariantGradientSchwartz fixedVolumeCovariantGradientSchwartz_tsupport)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- For the given actual chart and compact window, the original volume-weighted
symmetric jet tests converge with the specified chart principal. -/
theorem tendsto_originalCovariantSymmetricJetTest_of_compactWindowData
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hLocal : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (Q : SymmetricJetGlobalForm M) (c : AtlasChart M)
    (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (a : JetSlot → JetSlot → E → E → ℂ)
    (W : CompactSymmetricJetWindowData B hB hn Q c a (c.chart '' K)
      (hK.image_of_continuousOn (c.chart.continuousOn.mono hKc))
      (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc)))
    (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart '' K)
    (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart '' K) :
    let hKt := image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc)
    let h₀c := h₀.trans hKt
    let h₁c := h₁.trans hKt
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let G (p : Cosphere r) :=
      let z := fixedChartPhase c p.val
      ∑ i : JetSlot, ∑ j : JetSlot,
        conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) *
          a i j z.1 (WithLp.toLp 2 z.2)) * atlasOrderedJetEntry c A.density p j i
    Integrable G τ ∧
    Tendsto (fun n => conj (Q (originalCovariantSymmetricJetTest r B g hB hg hn c η₀ h₀c (σ n))
      (originalCovariantSymmetricJetTest r B g hB hg hn c η₁ h₁c (σ n)))) atTop (𝓝 (∫ p, G p ∂τ)) := by
  intro hKt h₀c h₁c τ G
  let K' := c.chart '' K
  have hK' : IsCompact K' := hK.image_of_continuousOn (c.chart.continuousOn.mono hKc)
  obtain ⟨J, _, _, hJ, α, hα, hαC, hαS, _, hαK⟩ :=
    FlatRigidity.exists_smooth_cutoff_on_compact_chart hK' c.chart.open_target hKt
  let ρ : D := ⟨α, hα, hαC⟩
  have hρ : tsupport (ρ : E → ℝ) ⊆ c.chart.target := hαS.trans hJ
  have hActual (i j : JetSlot) (f w : SchwartzMap E ℂ)
      (hf : tsupport (f : E → ℂ) ⊆ tsupport (η₀ : E → ℝ))
      (hw : tsupport (w : E → ℂ) ⊆ tsupport (η₁ : E → ℝ)) :
      Q (compactSymmetricJetChartTestLinear B hB hn c ρ hρ (Pi.single i f))
        (compactSymmetricJetChartTestLinear B hB hn c ρ hρ (Pi.single j w)) =
        classicalLeftPairing (W.full i j) f w := by
    rw [compactSymmetricJetChartTestLinear_eq_supported B hB hn c K' hK' hKt ρ hρ hαK
      _ (tsupport_singleSymmetricJetWindow_subset i f (hf.trans h₀)),
      compactSymmetricJetChartTestLinear_eq_supported B hB hn c K' hK' hKt ρ hρ hαK
      _ (tsupport_singleSymmetricJetWindow_subset j w (hw.trans h₁))]
    exact W.action i j f w (hf.trans h₀) (hw.trans h₁)
  have hLarge (i j : JetSlot) (S : Set E) (_ : IsCompact S) (_ : S ⊆ c.chart.target) :
      ∃ R : ℝ, ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ : E, R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ m (fun y => W.full i j y ξ - W.principal i j y ξ) x‖ ≤ C := by
    obtain ⟨R, hR⟩ := W.order_minus_one i j
    refine ⟨R, fun m => ?_⟩
    obtain ⟨C, hC, hRm⟩ := hR m
    exact ⟨C, hC, fun x _ ξ hξ => hRm x ξ hξ⟩
  obtain ⟨hI, hLimit⟩ := tendsto_originalVolume_actualSymmetricJetLocalSymbol r B g hB hg hn σ A hLocal
    Q c K hK hKc η₀ η₁ ρ ρ h₀ h₁ hρ hρ W.full W.principal
    (fun i j => (W.full_smooth i j).contDiffOn)
    (fun i j => (W.principal_smooth i j).mono (Set.prod_mono (subset_univ _) Subset.rfl))
    (fun i j x _ s hs ξ _ => W.principal_degree i j x s hs ξ) hLarge hActual
  let G₀ (p : Cosphere r) :=
    let z := fixedChartPhase c p.val
    ∑ i : JetSlot, ∑ j : JetSlot,
      conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) *
        W.principal i j z.1 (WithLp.toLp 2 z.2)) * atlasOrderedJetEntry c A.density p j i
  have hAE : G₀ =ᵐ[τ] G := by
    filter_upwards [ae_restrict_mem (μ := A.control) (measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet)]
      with p hp
    have hz : (fixedChartPhase c p.val).1 ∈ K' := by
      rw [fixedChartPhase_of_mem c p.val (hKc hp)]
      exact mem_image_of_mem _ hp
    have hξ : WithLp.toLp 2 (fixedChartPhase c p.val).2 ≠ (0 : E) := by
      rw [fixedChartPhase_of_mem c p.val (hKc hp)]
      intro h
      exact atlasChartUnitCovector_ne_zero c p (hKc hp)
        ((funext (atlasChartUnitCovector_of_mem c p (hKc hp))).trans (congrArg (fun z : E => WithLp.ofLp z) h))
    dsimp only [G₀, G]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [W.principal_eq i j _ hz _ hξ]
  change Integrable G₀ τ at hI
  refine ⟨hI.congr hAE, ?_⟩
  rw [← integral_congr_ae hAE]
  refine hLimit.congr fun n => ?_
  have hRead (η : D) (hη : tsupport (η : E → ℝ) ⊆ K') :
      compactSymmetricJetChartTestLinear B hB hn c ρ hρ
          (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η (hη.trans hKt) (σ n)) =
        originalCovariantSymmetricJetTest r B g hB hg hn c η (hη.trans hKt) (σ n) := by
    rw [compactSymmetricJetChartTestLinear_eq_supported B hB hn c K' hK' hKt ρ hρ hαK
      _ (fun i => (fixedVolumeCovariantGradientSchwartz_tsupport r B g hB hg hn c η
        (hη.trans hKt) (σ n) i).trans hη)]
    exact supportedSymmetricJetChartTest_original r B g hB hg hn c K' hK' hKt η hη (σ n)
  rw [hRead η₀ h₀, hRead η₁ h₁]

end Burnett.Microlocal.Overlap
