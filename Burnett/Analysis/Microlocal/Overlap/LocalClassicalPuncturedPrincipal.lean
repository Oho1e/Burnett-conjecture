import Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol

/-! A principal symbol given only on nonzero covectors. -/

set_option autoImplicit false
set_option maxRecDepth 3200
set_option maxHeartbeats 1900000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open UnitCosphere (Cosphere projection)
open FixedCotangentChart (fixedChartPhase)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeGradientSchwartz)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped ComplexConjugate ContDiff InnerProduct Manifold Topology

local notation "E" => CoordinateSpace

private def angularPrincipalZeroExtension (a : E → E → ℂ) (x ξ : E) : ℂ := by
  classical
  exact if ξ = 0 then 0 else a x ξ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [T2Space M] [MeasurableSpace M] [BorelSpace M]

/-- The original pairing uses only the principal symbol on nonzero frequencies.
Assigning zero off that domain leaves every tested limit on the auxiliary cosphere unchanged. -/
theorem tendsto_originalVolume_receivingLocalFullPairing_of_puncturedPrincipal
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hPair : HasOriginalReceivingPaperPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart '' K)
    (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart '' K)
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (b a : E → E → ℂ)
    (hbDiff : ContDiffOn ℝ ∞ (uncurry b) (c.chart.target ×ˢ univ))
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (c.chart.target ×ˢ ({0}ᶜ : Set E)))
    (hDegree : ∀ x ∈ c.chart.target, ∀ (s : ℝ), 0 < s → ∀ ξ : E, ξ ≠ 0 → a x (s • ξ) = a x ξ)
    (hLarge : ∀ S : Set E, IsCompact S → S ⊆ c.chart.target → ∃ R : ℝ,
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ : E, R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C)
    (hAct : ∀ f v : SchwartzMap E ℂ, tsupport (f : E → ℂ) ⊆ c.chart.target →
      tsupport (v : E → ℂ) ⊆ tsupport (η₁ : E → ℝ) →
      inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) = classicalLeftPairing b f v)
    (i j : JetSlot) :
    let h₀c := h₀.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let h₁c := h₁.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u := fixedVolumeGradientSchwartz B g hB hg hn c η₀ h₀c
    let v := fixedVolumeGradientSchwartz B g hB hg hn c η₁ h₁c
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let G (p : Cosphere r) :=
      let z := fixedChartPhase c p.val
      conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a z.1 (WithLp.toLp 2 z.2)) *
        atlasOrderedJetEntry c A.density p j i
    Integrable G τ ∧ Tendsto (fun n => inner ℂ (T ((v (σ n) j).toLp 2 volume))
      ((u (σ n) i).toLp 2 volume)) atTop (𝓝 (∫ p, G p ∂τ)) := by
  intro h₀c h₁c u v τ G
  let a' := angularPrincipalZeroExtension a
  have hDiff : ContDiffOn ℝ ∞ (uncurry a') (c.chart.target ×ˢ ({0}ᶜ : Set E)) := by
    refine haDiff.congr fun z hz => ?_
    have hξ : z.2 ≠ 0 := hz.2
    change a' z.1 z.2 = a z.1 z.2
    simp [a', angularPrincipalZeroExtension, hξ]
  have hZero : ContDiffOn ℝ ∞ (fun x => a' x 0) c.chart.target := by
    simpa only [a', angularPrincipalZeroExtension, if_pos rfl] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) c.chart.target)
  have hD (x : E) (hx : x ∈ c.chart.target) : DegreeZero (a' x) := by
    intro s hs ξ
    by_cases hξ : ξ = 0
    · rw [hξ, smul_zero]
    · have hScale : s • ξ ≠ 0 := smul_ne_zero hs.ne' hξ
      simpa only [a', angularPrincipalZeroExtension, if_neg hScale, if_neg hξ] using hDegree x hx s hs ξ hξ
  have hE (S : Set E) (hS : IsCompact S) (hSU : S ⊆ c.chart.target) : ∃ R : ℝ,
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ : E, R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a' y ξ) x‖ ≤ C := by
    obtain ⟨R, hR⟩ := hLarge S hS hSU
    refine ⟨max 1 R, fun n => ?_⟩
    obtain ⟨C, hC, hD⟩ := hR n
    refine ⟨C, hC, fun x hx ξ hξ => ?_⟩
    have hnz : ξ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hξ))
    simpa only [a', angularPrincipalZeroExtension, if_neg hnz] using hD x hx ξ ((le_max_right _ _).trans hξ)
  obtain ⟨I, H⟩ := tendsto_originalVolume_receivingLocalFullPairing r B g hB hg hn σ A hPair c K hK hKc
    η₀ η₁ h₀ h₁ T b a' hbDiff hDiff hZero hD hE hAct i j
  let G' (p : Cosphere r) :=
    let z := fixedChartPhase c p.val
    conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a' z.1 (WithLp.toLp 2 z.2)) *
      atlasOrderedJetEntry c A.density p j i
  change Integrable G' τ at I
  change Tendsto (fun n => inner ℂ (T ((v (σ n) j).toLp 2 volume)) ((u (σ n) i).toLp 2 volume))
    atTop (𝓝 (∫ p, G' p ∂τ)) at H
  have hAE : G' =ᵐ[τ] G := by
    have hWindow := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
    filter_upwards [ae_restrict_mem (μ := A.control) hWindow] with p hp
    have hξ : WithLp.toLp 2 (fixedChartPhase c p.val).2 ≠ 0 := by
      intro hz
      apply atlasChartUnitCovector_ne_zero c p (hKc hp)
      exact congrArg WithLp.ofLp hz
    simp only [G', G, a', angularPrincipalZeroExtension, if_neg hξ]
  rw [integral_congr_ae hAE] at H
  exact ⟨I.congr hAE, H⟩

end Burnett.Microlocal.Overlap
