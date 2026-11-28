import Burnett.Analysis.TransportWard.Weyl.OriginalChartCubicGeometry
import Burnett.Analysis.TransportWard.Weyl.OriginalWeylRetestedPatchLimit
import Burnett.Analysis.TransportWard.Weyl.OriginalPatchWeylCompleteCubic

set_option autoImplicit false
set_option maxHeartbeats 7500000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Metric Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldBilinear ManifoldMetric MaximalChart
open UnitNullCompactness CotangentAngularExtension Burnett.C04 Burnett.C02
open Burnett.A03 Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped BigOperators ComplexConjugate ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [T2Space M]

/-- Freeze the exact original chart Weyl test and the exact original metric
on the same receiving patch; the frozen matrix is the one defining C03. -/
theorem exists_originalChartWeyl_patch_energy_freeze
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : M) (f : CotangentBundle M → ℝ) (hf : IsDegreeOneTransportTest f) (ho : IsAntipodallyOdd f)
    {S : Set M} (hS : IsCompact S) (hSC : S ⊆ (chartAt E c).source)
    (hOff : ∀ p ∈ puncturedCotangent, p.proj ∉ S → f p = 0)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ (chartAt E c).target)
    (Kplus L : Set E) (hχK : ∀ x ∈ Kplus, (χ : E → ℝ) x = 1)
    (hL : IsCompact L)
    (haOff : ∀ x ∉ L, ∀ ξ : E, originalChartTransportSymbol c f x (WithLp.ofLp ξ) = 0)
    (θ : SchwartzMap E ℝ) (hθc : HasCompactSupport (θ : E → ℝ)) (hθL : ∀ x ∈ L, θ x = 1)
    (R : ℝ) :
    let a (x ξ : E) := originalChartTransportSymbol c f x (WithLp.ofLp ξ)
    let β (x ξ : E) := fixedInfraredSymbol wardFixedTestCutoff 0 (a x) ξ
    let βc (x ξ : E) := (β x ξ : ℂ)
    let b (x : E) (i : OrderedPair) := assembleMetricComponents orthonormalMetricDirection
      (normalizedChartMetric B c x) i.1 i.2
    ∀ hAmp : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ βc) R R,
      let T (u : SchwartzMap E ℂ) (x : E) :=
        (-Complex.I) * firstOrderAction (windowedWeylLeftSymbol θ βc R hAmp) u x
      let C (p q : Index) (i j k : OrderedPair) (x : E) := Complex.ofReal
        (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis b (χ : E → ℝ) p q i j k x)
      ∃ A : ℝ, 0 ≤ A ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∃ Dℓ : ℝ, 0 ≤ Dℓ ∧
        ∀ x₀ ∈ Kplus, ∀ z : RealEnergyField OrderedPair,
          tsupport (fieldValueArray z.val) ⊆ closedBall x₀ (4 * ℓ) →
          let G := metricComponents (fixedForm B (AtlasChart.atPoint c)) x₀
          let F := principalVariationDensity C z.val (fun i => T (z.val i))
          Integrable F ∧
          |(∫ x, (F x).re) - completeCubicEnergy (frozenActionCubicLinear G)
            (frozenActionCubicQuadratic G) (β x₀) z| ≤
            A * ℓ * euclideanFieldGradientL3 z.val ^ 3 +
            Dℓ * euclideanFieldValueL3 z.val * euclideanFieldGradientL3 z.val ^ 2 := by
  intro a β βc b hAmp T C
  obtain ⟨hb, hMat, hNd⟩ := originalChartCubic_metric B hB hSig c
  obtain ⟨_, _, hHom, hOdd, hβ, _, hHigh, hβOdd, hFreq, D, hD, hJets⟩ :=
    originalChartCubic_fixedInfrared_data c f hf ho hS hSC hOff
  change ∀ x t, 0 < t → ∀ ξ, a x (t • ξ) = t * a x ξ at hHom
  change ∀ x ξ, 1 < ‖ξ‖ → β x ξ = a x ξ at hHigh
  have hβc : ContDiff ℝ ∞ (uncurry βc) := Complex.ofRealCLM.contDiff.comp hβ
  have hOffL (x : E) (hx : x ∉ L) (ξ : E) : β x ξ = 0 := by
    have hZero : a x ξ = 0 := haOff x hx ξ
    simp only [β, fixedInfraredSymbol, hZero, mul_zero, fixedRadianProfile,
      SchwartzMap.zero_apply, Complex.zero_re, add_zero]
  have hOffC (x : E) (hx : x ∉ L) (ξ : E) : βc x ξ = 0 := by
    simp only [βc, hOffL x hx ξ, Complex.ofReal_zero]
  have hTail (x ξ : E) (hξ : 1 < ‖ξ‖) (t : ℝ) (ht : 1 ≤ t) : βc x (t • ξ) = t • βc x ξ := by
    have ht₀ : 0 < t := zero_lt_one.trans_le ht
    have hLarge : 1 < ‖t • ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht₀.le]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) (norm_nonneg ξ)]
    change (β x (t • ξ) : ℂ) = t • (β x ξ : ℂ)
    rw [hHigh x _ hLarge, hHigh x ξ hξ, hHom x t ht₀ ξ, Complex.ofReal_mul, Complex.real_smul]
  obtain ⟨R', hR'⟩ := hθc.isCompact.isBounded.subset_closedBall (0 : E)
  have hθoff (x : E) (hx : x ∉ closedBall 0 R') : θ x = 0 := by
    by_contra hn
    exact hx (hR' (subset_tsupport (θ : E → ℝ) hn))
  have hDir := radianOrdinaryDirectionalAmplitudeBounds_of_scaled _ _ _
    (compactWindowedWeylAmplitude_scaled_orderOne θ βc (θ.smooth _) hβc R' hθoff hTail)
  have hNormalized := scaledJointOrderOne_of_compactRadianSymbol βc hβc hL hOffC hTail
  have hWindow (x ξ : E) (hx : βc x ξ ≠ 0) : θ x = 1 :=
    hθL x (by by_contra h; exact hx (hOffC x h ξ))
  obtain ⟨Q, hQ, _, _⟩ := exists_windowedWeylSchwartz_selfAdjoint θ βc R hAmp hDir hWindow
    θ.continuous hθc hNormalized (fun x ξ => Complex.conj_ofReal _)
  let B' (u : SchwartzMap E ℂ) := firstOrderAction (windowedWeylLeftSymbol θ βc R hAmp) u
  have hB' (u : SchwartzMap E ℂ) : ∃ v : SchwartzMap E ℂ, (v : E → ℂ) = B' u :=
    ⟨Q u, funext (hQ u)⟩
  obtain ⟨_, hComp⟩ := originalChartWeyl_cutoff_and_frozen_comparisons a L hL haOff
    (fun t ht x ξ => hHom x t ht ξ) wardFixedTestCutoff wardFixedTestCutoff_real
    wardFixedTestCutoff_profile_one wardFixedTestCutoff_profile_zero hβc θ (θ.smooth _) hθc hθL R hAmp
  obtain ⟨A, hA, hFreeze⟩ := exists_actualWeyl_completeCubic_patch_freezing b χ
    (chartAt E c).open_target hb hNd (test_smooth χ) hχ (test_compactSupport χ) hχK
    a wardFixedTestCutoff wardFixedTestCutoff_real L hL hβ hOffL hHigh hOdd hHom D hD
    (fun x _ => hFreq x) (fun x _ => hJets x) (fun x _ => hβOdd x) B' hB' hComp
  refine ⟨A, hA, ?_⟩
  intro ℓ hℓ hℓ₁
  obtain ⟨Dℓ, hDℓ, hs⟩ := hFreeze ℓ hℓ hℓ₁
  refine ⟨Dℓ, hDℓ, ?_⟩
  intro x hx z hz G F
  have hxU := hχ (subset_tsupport (χ : E → ℝ) (show (χ : E → ℝ) x ≠ 0 by rw [hχK x hx]; exact one_ne_zero))
  have h := hs x hx z hz
  dsimp only at h
  rw [hMat x hxU] at h
  exact h

end Burnett.V03.Palatini
