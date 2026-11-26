import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarSelectedGuard
import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarTestedSources

set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option maxRecDepth 4600

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set MeasureTheory Burnett.A06 Burnett.A07 Burnett.A08 Burnett.P01 Burnett.C02 Burnett.C03
open Burnett.Analysis.TransportWardSymbol (Mat inverseMatrix)
open Burnett.Analysis.ProjectiveNullCaps (Vec)
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.V11 (GaugeProfileBound)
open scoped ContDiff ENNReal NNReal BigOperators ComplexConjugate Matrix.Norms.Elementwise

private abbrev Index := Fin 4
private abbrev Field := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2

/-- At one original far entry the transpose representative, the two literal
projected scalar sources, and all three weak terms share one operator and
one initial field. The chosen guard is supplied through its phase identities. -/
theorem exists_actualFar_sharedSourceEntry :
    ∃ (N : ℕ) (K : ℝ), 0 ≤ K ∧
      ∀ (g : Mat) (a : Vec → ℝ), (∀ x : Vec, x ≠ 0 → a (-x) = -a x) →
      ∀ (ϑ : ℝ → ℝ), (∀ s : ℝ, 1 ≤ s → ϑ s = 0) →
      ∀ (κ : ℝ), 0 < κ → κ < 1 / 16 → ∀ δ b i o : ℝ,
      ∀ (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ),
      ActualFarPhaseIdentities g a ϑ κ δ b i o hm hη inn out →
      ∀ (k J I : OrderedPair) (M : ℝ), 0 ≤ M → GaugeProfileBound N M
        (actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k J I) →
      ∀ (d : Index → Index → SchwartzMap E ℝ), (∀ r s, d r s = d s r) →
      ∀ D : ℝ, 0 ≤ D → (∀ r s x, |d r s x| ≤ D) →
      ∀ L : ℝ≥0, (∀ r s x, ‖fderiv ℝ (d r s : E → ℝ) x‖ ≤ (L : ℝ)) →
      ∀ (z : ProjectionSchwartzMatrix), (∀ i j x, conj (z i j x) = z i j x) →
      ∀ (A : ProjectedSourceCoefficients), (∀ r s x, A.entry r s x = ((inverseMatrix g r s + d r s x : ℝ) : ℂ)) →
      let m := inverseMatrix g
      let f := projectionFullSchwartz z
      let H := f k.1 k.2
      let u := f J.1 J.2
      let v := f I.1 I.2
      let F := actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I
      let Fstar := actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k I J
      ∃ (T Tstar : Field → LP2) (Dlow Dstar : Index → Field → LP2),
        (∀ p q : Field, inner ℂ (q.toLp 2 volume) (T p) = radianHighPair F H p q ∧
          inner ℂ (q.toLp 2 volume) (T p) = inner ℂ (Tstar q) (p.toLp 2 volume) ∧
          inner ℂ (q.toLp 2 volume) (Tstar p) = radianHighPair Fstar H p q) ∧
        (∀ (r : Index) (p q : Field), inner ℂ (q.toLp 2 volume) (Dlow r p) =
          radianHighPair F (coordinateDerivative r H) p q ∧
          inner ℂ (p.toLp 2 volume) (Dstar r q) = conj (radianHighPair F (coordinateDerivative r H) p q)) ∧
        let left (r s : Index) :=
          inner ℂ ((realSchwartzMultiply (d r s) (coordinateDerivative r v)).toLp 2 volume) (Dlow s u)
        let middle (r s : Index) := inner ℂ ((coordinateDerivative r v).toLp 2 volume)
          (coefficientCommutatorOutput (d r s) T (coordinateDerivative s u))
        let right (r s : Index) :=
          inner ℂ (Dstar r v) ((realSchwartzMultiply (d r s) (coordinateDerivative s u)).toLp 2 volume)
        Complex.I * (radianHighPair F H u (constantWave m v) - radianHighPair F H (constantWave m u) v) =
          Complex.I * (inner ℂ (projectedSourceDivergenceL2 A f I.1 I.2) (T u) -
            inner ℂ (Tstar v) (projectedSourceDivergenceL2 A f J.1 J.2) -
              ∑ r, ∑ s, (left r s + middle r s - right r s)) ∧
        ∀ r s,
          ‖left r s‖ ≤ (D * schwartzGradientNorm 2 v) * (K * M * schwartzGradientNorm 4 H * schwartzGradientNorm 4 u) ∧
          ‖middle r s‖ ≤ schwartzGradientNorm 2 v * (K * M * (L : ℝ) * ‖H.toLp 4 volume‖ * schwartzGradientNorm 4 u) ∧
          ‖right r s‖ ≤ (K * M * schwartzGradientNorm 4 H * schwartzGradientNorm 4 v) * (D * schwartzGradientNorm 2 u) := by
  obtain ⟨N, K, hK, terms⟩ := exists_actualFar_threeDivergenceTerms
  refine ⟨N, K, hK, ?_⟩
  intro g a odd ϑ cut κ hκ hs δ b i o hm η hη inn out phase k J I M hM jet d symm D hD mag L slope z hz A hA m f H u v F Fstar
  obtain ⟨T, Tstar, Dlow, Dstar, pairs, derivatives, split⟩ :=
    terms g a ϑ cut κ hκ hs δ b i o hm hη inn out k J I M hM jet d symm D hD mag L slope z
  have adj := actualFarRadianKernel_highAdjoint_of_phase g a ϑ κ δ b i o hm hη inn out phase odd k I J
  have transposed (p q : Field) : inner ℂ (q.toLp 2 volume) (Tstar p) = radianHighPair Fstar H p q := by
    calc
      _ = conj (inner ℂ (Tstar p) (q.toLp 2 volume)) := (inner_conj_symm _ _).symm
      _ = conj (radianHighPair F H q p) := by rw [← (pairs q p).2, (pairs q p).1]
      _ = _ := (actualFarProjected_pair_adjoint g a ϑ κ δ b i o hm hη inn out k J I adj z hz q p).symm
  refine ⟨T, Tstar, Dlow, Dstar, fun p q => ⟨(pairs p q).1, (pairs p q).2, transposed p q⟩, derivatives, ?_⟩
  intro left middle right
  obtain ⟨hSplit, hBounds⟩ := split u v
  refine ⟨?_, hBounds⟩
  change _ = Complex.I * (inner ℂ (projectedSourceDivergenceL2 A f I.1 I.2) (T u) -
    inner ℂ (Tstar v) (projectedSourceDivergenceL2 A f J.1 J.2) -
      ∑ r, ∑ s, (left r s + middle r s - right r s))
  rw [← hSplit]
  have source := weakConstantWaveCommutatorPair_eq_mixedSource m d T Tstar (fun p q => (pairs p q).2) u v
  rw [projectedSourceDivergenceL2_eq_constantWave_add_schwartzDivergence A m d hA z I.1 I.2,
    projectedSourceDivergenceL2_eq_constantWave_add_schwartzDivergence A m d hA z J.1 J.2]
  congr 1
  rw [← source]
  rw [weakConstantWaveCommutatorPair, (pairs u (constantWave m v)).1, (pairs (constantWave m u) v).1]

end Burnett.V10.OriginalGaugeCompatibility
