import Burnett.Analysis.TransportWard.Weyl.OriginalChartPatchFreezing
import Burnett.Analysis.TransportWard.Weyl.OriginalReceivingPatchCubicBudget

set_option autoImplicit false
set_option maxHeartbeats 6300000

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Metric Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open UnitNullCompactness CotangentAngularExtension Burnett.C04 Burnett.C02
open Burnett.A03 Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The freezing error for the actual receiving field has the original
patch volume as its weight. The coefficient of the error is uniform
before choosing the localization size or the receiving cutoff. -/
theorem exists_originalChartWeyl_receiving_freezing_tail
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (c : M) (f : CotangentBundle M → ℝ) (hf : IsDegreeOneTransportTest f) (ho : IsAntipodallyOdd f)
    {S : Set M} (hS : IsCompact S) (hSC : S ⊆ (chartAt E c).source)
    (hOff : ∀ p ∈ puncturedCotangent, p.proj ∉ S → f p = 0)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ (chartAt E c).target)
    (Kplus L : Set E) (hK : IsCompact Kplus) (hKU : Kplus ⊆ (chartAt E c).target)
    (hχK : ∀ x ∈ Kplus, (χ : E → ℝ) x = 1) (hL : IsCompact L)
    (haOff : ∀ x ∉ L, ∀ ξ : E, originalChartTransportSymbol c f x (WithLp.ofLp ξ) = 0)
    (θ : SchwartzMap E ℝ) (hθc : HasCompactSupport (θ : E → ℝ)) (hθL : ∀ x ∈ L, θ x = 1)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (hLim : Tendsto e atTop (𝓝 0))
    (hError : ∀ n x, x ∈ Kplus →
      ‖metricComponents (fixedForm (g n) (AtlasChart.atPoint c)) x -
        metricComponents (fixedForm B (AtlasChart.atPoint c)) x‖ ≤ e n)
    (Ccut : ℕ → ℝ) (hCcut : ∀ k, 0 ≤ Ccut k) (R : ℝ) :
    let a (x ξ : E) := originalChartTransportSymbol c f x (WithLp.ofLp ξ)
    let β (x ξ : E) := fixedInfraredSymbol wardFixedTestCutoff 0 (a x) ξ
    let b (x : E) (i : OrderedPair) := assembleMetricComponents orthonormalMetricDirection
      (normalizedChartMetric B c x) i.1 i.2
    ∀ hAmp : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ (fun x ξ => (β x ξ : ℂ))) R R,
      let T (w : SchwartzMap E ℂ) (x : E) :=
        (-Complex.I) * firstOrderAction (windowedWeylLeftSymbol θ (fun y ξ => (β y ξ : ℂ)) R hAmp) w x
      let C (p q : Index) (i j k : OrderedPair) (x : E) := Complex.ofReal
        (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis b (χ : E → ℝ) p q i j k x)
      ∃ F : ℝ, 0 ≤ F ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ (x₀ : E) (d : D)
        (hd : tsupport (d : E → ℝ) ⊆ (chartAt E c).target),
        tsupport (d : E → ℝ) ⊆ closedBall x₀ (4 * ℓ) → closedBall x₀ (6 * ℓ) ⊆ Kplus →
        (∀ k x, ‖iteratedFDeriv ℝ k (d : E → ℝ) x‖ ≤ Ccut k * ℓ⁻¹ ^ k) →
        let z (n : ℕ) := receivingCubicPatchField B g hB hg (AtlasChart.atPoint c) d hd (σ n)
        let G := metricComponents (fixedForm B (AtlasChart.atPoint c)) x₀
        let E₀ (n : ℕ) := completeCubicEnergy (frozenActionCubicLinear G)
          (frozenActionCubicQuadratic G) (β x₀) (z n)
        ∀ ε > 0, ∀ᶠ n in atTop,
          |(∫ x, (principalVariationDensity C (z n).val (fun i => T ((z n).val i)) x).re) - E₀ n| ≤
            (F * ℓ) * ((volume : Measure E) (closedBall x₀ (6 * ℓ))).toReal + ε := by
  intro a β b hAmp T C
  obtain ⟨A, hA, hFreeze⟩ :=
    exists_originalChartWeyl_patch_energy_freeze B hB hSig c f hf ho hS hSC hOff
      χ hχ Kplus L hχK hL haOff θ hθc hθL R hAmp
  obtain ⟨M, hM, hBudget⟩ := exists_receivingCubicPatch_volume_budget r B g hB hg
    hSig.isNondegenerate hconv hb (AtlasChart.atPoint c) Kplus hK hKU σ hσ e he hLim hError
    (Ccut 0) (Ccut 1) (hCcut 0) (hCcut 1)
  refine ⟨A * M ^ 3, by positivity, ?_⟩
  intro ℓ hℓ hℓ₁ x₀ d hd hdS hIn hJets z G E₀
  obtain ⟨Dℓ, hDℓ, hfrozen⟩ := hFreeze ℓ hℓ hℓ₁
  have hx₀ : x₀ ∈ Kplus := hIn (mem_closedBall_self (mul_nonneg (by norm_num) hℓ.le))
  have hVal (x : E) (_ : x ∈ tsupport (d : E → ℝ)) : ‖(d : E → ℝ) x‖ ≤ Ccut 0 := by
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hJets 0 x
  have hJet (x : E) (_ : x ∈ tsupport (d : E → ℝ)) :
      ‖iteratedFDeriv ℝ 1 (d : E → ℝ) x‖ ≤ Ccut 1 * ℓ⁻¹ := by
    simpa only [pow_one] using hJets 1 x
  obtain ⟨hz, hY, hX⟩ := hBudget ℓ hℓ x₀ d hd hdS hIn hVal hJet
  let err (n : ℕ) :=
    (∫ x, (principalVariationDensity C (z n).val (fun i => T ((z n).val i)) x).re) - E₀ n
  have hPoint (n : ℕ) : |err n| ≤
      A * ℓ * euclideanFieldGradientL3 (z n).val ^ 3 +
      Dℓ * euclideanFieldValueL3 (z n).val * euclideanFieldGradientL3 (z n).val ^ 2 :=
    (hfrozen x₀ hx₀ (z n) (hz n)).2
  exact eventual_cubic_freezing_error_le_patch_volume
    (fun n => (z n).val) err (closedBall x₀ (6 * ℓ)) ℓ A Dℓ M hℓ hA hDℓ hY hX
      (Eventually.of_forall hPoint)

end Burnett.V03.Palatini
