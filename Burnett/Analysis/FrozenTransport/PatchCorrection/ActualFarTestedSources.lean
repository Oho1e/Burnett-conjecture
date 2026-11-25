import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarThreeDivergenceTerms
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalProjectedSourceBridge
import Burnett.Analysis.FrozenTransport.ActualThinSchwartzField

set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxRecDepth 4100

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set MeasureTheory Burnett.A06 Burnett.A07 Burnett.A08 Burnett.P01 Burnett.C02 Burnett.C03
open Burnett.Analysis.TransportWardSymbol (Mat inverseMatrix)
open Burnett.Analysis.ProjectiveNullCaps (Vec)
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.V11 (GaugeProfileBound)
open scoped ContDiff ENNReal NNReal ComplexConjugate Matrix.Norms.Elementwise

private abbrev Index := Fin 4
private abbrev Field := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2

theorem actualFarProjected_pair_adjoint (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ) (κ δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (k J I : OrderedPair)
    (hKernel : ∀ p q : Vec,
      conj (actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I (-p, p + q)) =
        actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k I J (p, q))
    (z : ProjectionSchwartzMatrix) (hz : ∀ i j x, conj (z i j x) = z i j x) (u v : Field) :
    let H := projectionFullSchwartz z k.1 k.2
    radianHighPair (actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k I J) H v u =
      conj (radianHighPair (actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I) H u v) := by
  intro H
  let F := actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I
  have sym : highAdjointSymbol F = actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k I J := by
    funext x
    obtain ⟨p,q⟩ := x
    change conj (F (-p, q + p)) = _
    rw [add_comm q p]
    exact hKernel p q
  have realH : (fun t : E => conj (H t)) = (H : E → ℂ) :=
    funext fun x => projectionFullSchwartz_real_of_source z hz k x
  simpa only [sym, realH] using radianHighPair_highAdjoint F (H : E → ℂ) u v

/-- The transpose entry supplied by the actual screen is the tested adjoint
of any representative of the complete original far pairing. -/
theorem actualFarProjected_representatives_dual (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ) (κ δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (k J I : OrderedPair)
    (hKernel : ∀ p q : Vec,
      conj (actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I (-p, p + q)) =
        actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k I J (p, q))
    (z : ProjectionSchwartzMatrix) (hz : ∀ i j x, conj (z i j x) = z i j x)
    (T S : Field → LP2) :
    let H := projectionFullSchwartz z k.1 k.2
    (∀ u v : Field, inner ℂ (v.toLp 2 volume) (T u) =
      radianHighPair (actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I) H u v) →
    (∀ u v : Field, inner ℂ (v.toLp 2 volume) (S u) =
      radianHighPair (actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k I J) H u v) →
    ∀ u v : Field, inner ℂ (v.toLp 2 volume) (T u) = inner ℂ (S v) (u.toLp 2 volume) := by
  intro H repT repS u v
  have adj := actualFarProjected_pair_adjoint g a ϑ κ δ b i o hm hη inn out k J I hKernel z hz u v
  rw [repT u v, ← inner_conj_symm (S v), repS v u, adj, starRingEnd_self_apply]

/-- The tested far commutator has the literal two mixed high-source terms,
both supplied by the one original projected scalar divergence equation. -/
theorem exists_actualFar_originalProjectedSources :
    ∃ N : ℕ,
      ∀ (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ), (∀ s : ℝ, 1 ≤ s → ϑ s = 0) →
      ∀ (κ : ℝ), 0 < κ → κ < 1 / 16 → ∀ δ b i o : ℝ,
      ∀ (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ),
      ∀ (k J I : OrderedPair) (M : ℝ), 0 ≤ M → GaugeProfileBound N M
        (actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k J I) →
      ∀ (d : Index → Index → SchwartzMap E ℝ), (∀ r s, d r s = d s r) →
      ∀ D : ℝ, 0 ≤ D → (∀ r s x, |d r s x| ≤ D) →
      ∀ L : ℝ≥0, (∀ r s x, ‖fderiv ℝ (d r s : E → ℝ) x‖ ≤ (L : ℝ)) →
      ∀ (z : ProjectionSchwartzMatrix) (A : ProjectedSourceCoefficients),
      (∀ r s x, A.entry r s x = ((inverseMatrix g r s + d r s x : ℝ) : ℂ)) →
      let f := projectionFullSchwartz z
      let H := f k.1 k.2
      let u := f J.1 J.2
      let w := f I.1 I.2
      let F := actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I
      ∃ T Tstar : Field → LP2,
        (∀ p q : Field, inner ℂ (q.toLp 2 volume) (T p) = radianHighPair F H p q ∧
          inner ℂ (q.toLp 2 volume) (T p) = inner ℂ (Tstar q) (p.toLp 2 volume)) ∧
        Complex.I * (radianHighPair F H u (constantWave (inverseMatrix g) w) -
          radianHighPair F H (constantWave (inverseMatrix g) u) w) = Complex.I *
          (inner ℂ (projectedSourceDivergenceL2 A f I.1 I.2) (T u) -
            inner ℂ (Tstar w) (projectedSourceDivergenceL2 A f J.1 J.2) -
              weakDivergenceCommutatorPair d T u w) := by
  obtain ⟨N, _, _, terms⟩ := exists_actualFar_threeDivergenceTerms
  refine ⟨N, ?_⟩
  intro g a ϑ hcut κ hκ hs δ b i o hm η hη inn out k J I M hM jet d hSym D hD hmag L hslope z A hA f H u w F
  obtain ⟨T, Tstar, _, _, pair, _, _⟩ :=
    terms g a ϑ hcut κ hκ hs δ b i o hm hη inn out k J I M hM jet d hSym D hD hmag L hslope z
  refine ⟨T, Tstar, pair, ?_⟩
  have source := weakConstantWaveCommutatorPair_eq_mixedSource (inverseMatrix g) d T Tstar (fun p q => (pair p q).2) u w
  rw [projectedSourceDivergenceL2_eq_constantWave_add_schwartzDivergence A (inverseMatrix g) d hA z I.1 I.2,
    projectedSourceDivergenceL2_eq_constantWave_add_schwartzDivergence A (inverseMatrix g) d hA z J.1 J.2]
  congr 1
  rw [← source]
  rw [weakConstantWaveCommutatorPair, (pair u (constantWave (inverseMatrix g) w)).1,
    (pair (constantWave (inverseMatrix g) u) w).1]

end Burnett.V10.OriginalGaugeCompatibility
