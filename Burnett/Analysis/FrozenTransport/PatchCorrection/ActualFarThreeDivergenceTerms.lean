import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarPatchEnvelope
import Burnett.Analysis.FrozenTransport.PatchCorrection.ExplicitThreeDivergenceTerms

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set Metric MeasureTheory Burnett.A06 Burnett.A07 Burnett.A08 Burnett.P01 Burnett.C02 Burnett.C03 Burnett.V03
open Burnett.Analysis.TransportWardSymbol (Mat inverseMatrix)
open Burnett.Analysis.ProjectiveNullCaps (Vec)
open Burnett.A02.FrequencySplit (E Joint radianFourier)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.V11 (GaugeProfileBound)
open scoped ContDiff ENNReal NNReal BigOperators ComplexConjugate Matrix.Norms.Elementwise

private abbrev Field := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2
private abbrev Index := Fin 4

/-- The full far operator gives all three weak divergence terms on the
same physical low field and arbitrary Schwartz high slots. -/
theorem exists_actualFar_threeDivergenceTerms :
    ∃ (N : ℕ) (K : ℝ), 0 ≤ K ∧
      ∀ (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ), (∀ s : ℝ, 1 ≤ s → ϑ s = 0) →
      ∀ (κ : ℝ), 0 < κ → κ < 1 / 16 → ∀ δ b i o : ℝ,
      ∀ (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ),
      ∀ (k J I : OrderedPair) (M : ℝ), 0 ≤ M → GaugeProfileBound N M
        (actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k J I) →
      ∀ (d : Index → Index → SchwartzMap E ℝ), (∀ r s, d r s = d s r) →
      ∀ D : ℝ, 0 ≤ D → (∀ r s x, |d r s x| ≤ D) →
      ∀ L : ℝ≥0, (∀ r s x, ‖fderiv ℝ (d r s : E → ℝ) x‖ ≤ (L : ℝ)) →
      ∀ z : ProjectionSchwartzMatrix,
      let H := projectionFullSchwartz z k.1 k.2
      let F := actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I
      ∃ (T Tstar : Field → LP2) (A B : Index → Field → LP2),
        (∀ u v : Field, inner ℂ (v.toLp 2 volume) (T u) = radianHighPair F H u v ∧
          inner ℂ (v.toLp 2 volume) (T u) = inner ℂ (Tstar v) (u.toLp 2 volume)) ∧
        (∀ (r : Index) (u v : Field), inner ℂ (v.toLp 2 volume) (A r u) =
          radianHighPair F (coordinateDerivative r H) u v ∧
          inner ℂ (u.toLp 2 volume) (B r v) = conj (radianHighPair F (coordinateDerivative r H) u v)) ∧
        ∀ u v : Field,
        let left (r s : Index) := inner ℂ ((realSchwartzMultiply (d r s) (coordinateDerivative r v)).toLp 2 volume) (A s u)
        let middle (r s : Index) := inner ℂ ((coordinateDerivative r v).toLp 2 volume)
          (coefficientCommutatorOutput (d r s) T (coordinateDerivative s u))
        let right (r s : Index) := inner ℂ (B r v) ((realSchwartzMultiply (d r s) (coordinateDerivative s u)).toLp 2 volume)
        weakDivergenceCommutatorPair d T u v = ∑ r, ∑ s, (left r s + middle r s - right r s) ∧
        ∀ r s,
          ‖left r s‖ ≤ (D * schwartzGradientNorm 2 v) * (K * M * schwartzGradientNorm 4 H * schwartzGradientNorm 4 u) ∧
          ‖middle r s‖ ≤ schwartzGradientNorm 2 v * (K * M * (L : ℝ) * ‖H.toLp 4 volume‖ * schwartzGradientNorm 4 u) ∧
          ‖right r s‖ ≤ (K * M * schwartzGradientNorm 4 H * schwartzGradientNorm 4 v) * (D * schwartzGradientNorm 2 u) := by
  obtain ⟨N, K, hK, all⟩ := Burnett.V11.exists_originalAngular_threeDivergenceTerms
    correctionInputWindow correctionRatioWindow (r := 1 / 2) (ρ := 1 / 4) (R₀ := 1)
    (by norm_num) (by norm_num) (by norm_num) le_rfl correctionInputWindow_smooth
    correctionInputWindow_zero correctionInputWindow_one correctionRatioWindow_smooth correctionRatioWindow_zero
  refine ⟨N, K, hK, ?_⟩
  intro g a ϑ cut κ hκ hs δ b i o hm η hη inn out k J I M hM jets d symm D hD hmag L hL z H F
  obtain ⟨W, hW, sub, smooth, jet⟩ := jets
  obtain ⟨T, Tstar, A, B, pair, der, terms⟩ := all hW sub smooth M hM
    (fun n hn p hp x => jet n hn (p, (x : E)) ⟨hp, x.property⟩) d symm D hD hmag L hL H
  have low (p : E) (hp : ‖p‖ ≤ 1) : radianFourier H p = 0 := by
    simp [H, projectionFullSchwartz_radianFourier, regularizedComplexGaugeProjection, gaugeProjectionInfrared_zero hp]
  have inert := actualFarA08_pair g a ϑ cut κ hκ hs δ b i o hm hη inn out k J I
  refine ⟨T, Tstar, A, B, fun u v => ⟨(pair u v).1.trans (inert H low u v).symm, (pair u v).2⟩, ?_, terms⟩
  intro r u v
  have lowDer (p : E) (hp : ‖p‖ ≤ 1) : radianFourier (coordinateDerivative r H) p = 0 := by
    rw [radianFourier_coordinateDerivative, low p hp, mul_zero]
  have matchPair := inert (coordinateDerivative r H) lowDer u v
  refine ⟨(der r u v).1.trans matchPair.symm, ?_⟩
  rw [(der r v u).2, radianHighPair_highAdjoint, matchPair]

end Burnett.V10.OriginalGaugeCompatibility
