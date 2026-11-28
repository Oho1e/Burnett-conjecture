import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleOrderedTestEnergy
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCyclicHighPassTest
import Burnett.Analysis.FrozenTransport.FrozenCubicActionPairing
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure
import Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 8200000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.A02.FrequencySplit Burnett.A05
open Burnett.Analysis.TransportWardSymbol Burnett.RicciSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.V08 (originalGaugeSpectrum signedCyclicPhase)
open scoped ComplexConjugate ContDiff

open private fixedInfraredSymbol_spectrum_integrable from Burnett.Analysis.FrozenTransport.FrozenCubicActionPairing
open private fixed_homogeneous_spectrum_integrable from Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure
open private radianEval from Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities

private theorem wardOrderedPrincipalLeg_swap (G : Mat) (H : ComplexTensor2)
    (q r : Cov) (J L : ComplexTensor2) :
    wardOrderedPrincipalLeg G H q r J L = wardOrderedPrincipalLeg G H r q L J := by
  let swap : WardActionEntry ≃ WardActionEntry := {
    toFun k := (k.1,k.2.2,k.2.1)
    invFun k := (k.1,k.2.2,k.2.1)
    left_inv _ := rfl
    right_inv _ := rfl }
  unfold wardOrderedPrincipalLeg
  apply Fintype.sum_equiv swap
  intro k
  have hC := frozenActionCubicLinear_symmetry G k.2.1.1 k.2.2.1 k.2.1.2 k.2.2.2 k.1
  have hs : swap k = (k.1,k.2.2,k.2.1) := rfl
  simp only [hs, wardActionEntryCoefficient]
  rw [hC]
  ring

private theorem wardCubicCyclicAverage_scalar (α X Y Z : ℂ) :
    (-Complex.I / 3) * α * -(X+Y+Z) =
      (1/3 : ℂ) * (Complex.I * α * X + Complex.I * α * Y + Complex.I * α * Z) := by
  ring

private theorem wardOrderedCubicCyclicAverage
    (b : E → ℝ) (A : E → E → E → ℂ) (symm : ∀ p q r : E, A p q r = A p r q) (p q : E) :
    let r := -(p+q)
    let α (x y : E) := (signedCyclicPhase b x y : ℂ)
    (-Complex.I / 3) * α p q * -(A p q r + A q p r + A r p q) =
      (1/3 : ℂ) * (Complex.I * α p q * A p q r + Complex.I * α q r * A q r (-(q+r)) +
        Complex.I * α r (-(q+r)) * A r (-(q+r)) (-(r + -(q+r)))) := by
  intro r α
  have hp : -(q+r) = p := by dsimp only [r]; abel
  have hq : -(r+p) = q := by dsimp only [r]; abel
  have h₁ : signedCyclicPhase b q r = signedCyclicPhase b p q := by
    unfold signedCyclicPhase
    rw [hp]
    change b q + b r + b p = b p + b q + b r
    ring
  have h₂ : signedCyclicPhase b r p = signedCyclicPhase b p q := by
    unfold signedCyclicPhase
    rw [hq]
    change b r + b p + b q = b p + b q + b r
    ring
  have hα₁ : α q r = α p q := congrArg Complex.ofReal h₁
  have hα₂ : α r p = α p q := congrArg Complex.ofReal h₂
  rw [hp,hq,hα₁,hα₂,symm q p r]
  exact wardCubicCyclicAverage_scalar (α p q) (A p q r) (A q r p) (A r p q)

private def wardOrderedCubicLegAt (G : Mat) (U : E → ComplexTensor2) (p q r : E) : ℂ :=
  wardOrderedPrincipalLeg G (U p) (fun i => q i) (fun i => r i) (U q) (U r)

private theorem wardCyclicCubicWeight_eq_orderedLeg (G : Mat) (hG : Matrix.det G ≠ 0)
    (b : E → ℝ) (U : E → ComplexTensor2) (p q : E) :
    let r := -(p+q)
    let A := wardOrderedCubicLegAt G U
    wardCyclicCubicWeight G b U U U (p,q) =
      (-Complex.I / 3) * (signedCyclicPhase b p q : ℂ) * -(A p q r + A q p r + A r p q) := by
  intro r A
  change (-Complex.I / 3) * (signedCyclicPhase b p q : ℂ) *
    complexPrincipalVertex G (fun i => p i) (U p) (fun i => q i) (U q) (fun i => r i) (U r) = _
  rw [wardComplexPrincipalVertex_eq_ordered G hG]
  rfl

private theorem wardOrderedCyclicTestWeight_apply (G : Mat)
    (b : E → ℝ) (U : E → ComplexTensor2) (p q : E) :
    wardOrderedCyclicTestWeight G b U (p,q) =
      Complex.I * (signedCyclicPhase b p q : ℂ) * wardOrderedCubicLegAt G U p q (-(p+q)) := rfl

private theorem wardCyclicAverage_integral (b : E → ℝ) (A : E → E → E → ℂ)
    (hA : ∀ p q r, A p q r = A p r q) (W O : Joint → ℂ)
    (hW : ∀ p q,
      let r := -(p+q)
      W (p,q) = (-Complex.I / 3) * (signedCyclicPhase b p q : ℂ) * -(A p q r + A q p r + A r p q))
    (hO : ∀ p q, O (p,q) = Complex.I * (signedCyclicPhase b p q : ℂ) * A p q (-(p+q)))
    (hInt : Integrable O) :
    Integrable W ∧ (∫ x, W x) = ∫ x, O x := by
  have h₁ : Integrable (fun x => O (radianCycle x)) :=
    measurePreserving_radianCycle.integrable_comp_of_integrable hInt
  have h₂ : Integrable (fun x => O (radianCycle (radianCycle x))) :=
    measurePreserving_radianCycle.integrable_comp_of_integrable h₁
  have hw : W = fun x => (1 / 3 : ℂ) * (O x + O (radianCycle x) + O (radianCycle (radianCycle x))) := by
    funext x
    obtain ⟨p,q⟩ := x
    let r := -(p+q)
    change W (p,q) = (1/3 : ℂ) * (O (p,q) + O (q,r) + O (r,-(q+r)))
    rw [hW p q,hO p q,hO q r,hO r (-(q+r))]
    exact wardOrderedCubicCyclicAverage b A hA p q
  refine ⟨hw.symm ▸ ((hInt.add h₁).add h₂).const_mul _, ?_⟩
  have hc₁ : (∫ x, O (radianCycle x)) = ∫ x, O x := measurePreserving_radianCycle.integral_comp' O
  have hc₂ : (∫ x, O (radianCycle (radianCycle x))) = ∫ x, O x :=
    (measurePreserving_radianCycle.integral_comp' (fun y => O (radianCycle y))).trans hc₁
  have h01 : (∫ x, O x + O (radianCycle x)) = (∫ x, O x) + (∫ x, O (radianCycle x)) :=
    integral_add hInt h₁
  have h012 : (∫ x, O x + O (radianCycle x) + O (radianCycle (radianCycle x))) =
      (∫ x, O x + O (radianCycle x)) + (∫ x, O (radianCycle (radianCycle x))) :=
    integral_add (hInt.add h₁) h₂
  rw [hw, integral_const_mul, h012, h01, hc₂, hc₁]
  ring

/-- The Fourier cyclic factor is exactly the average over the three
measure-preserving cyclic distributions of the coordinate derivative slots. -/
theorem wardCyclicActualFourier_eq_oddTestEnergy (G : Mat) (hG : Matrix.det G ≠ 0)
    (b : E → ℝ) (u : RealEnergyField OrderedPair)
    (hInt : ∀ f : SchwartzMap E ℂ, Integrable (radianActionSpectrum b f)) :
    let U := wardRealEnergySpectrum u
    Integrable (wardCyclicCubicWeight G b U U U) ∧
      (wardCyclicCubicForm G b U U U).re = frozenActionCyclicOddTestEnergy G b u := by
  intro U
  let A := wardOrderedCubicLegAt G U
  let W := wardCyclicCubicWeight G b U U U
  let O := wardOrderedCyclicTestWeight G b U
  have hA (p q r : E) : A p q r = A p r q := wardOrderedPrincipalLeg_swap G (U p) _ _ _ _
  have h := wardOrderedCyclicTestWeight_eq_position G b u hInt
  have hAll := wardCyclicAverage_integral b A hA W O (wardCyclicCubicWeight_eq_orderedLeg G hG b U)
    (wardOrderedCyclicTestWeight_apply G b U) h.1
  exact ⟨hAll.1, (congrArg (fun v : ℂ => (((tau^8)⁻¹ : ℝ) • v).re) hAll.2).trans h.2⟩

/-- The physical complete cubic energy and the homogeneous Ward Fourier
form are the same on the actual C02 replacement field. -/
theorem wardActualThinGaugeCubicEnergy_eq_fourier (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (cut add : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ)
    (hCut : ∀ ξ, 1 < ‖ξ‖ → fixedRadianProfile cut ξ = 0)
    (hAdd : ∀ ξ, 1 < ‖ξ‖ → fixedRadianProfile add ξ = 0)
    (hOdd : ∀ ξ, fixedInfraredSymbol cut add a (-ξ) = -fixedInfraredSymbol cut add a ξ)
    (D : ℝ) (hD : 0 ≤ D) (hJets : ∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ Metric.sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ n a ξ‖ ≤ D)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) (hz : ∀ a b x, conj (z a b x) = z a b x) :
    let b := fixedInfraredSymbol cut add a
    let u := originalCubicThinScreen (inverseMatrix G) wi wo hm hη i o z hz
    let g := originalCubicGauge z hz
    let H := wardActualThinSpectrum (inverseMatrix G) wi wo hm hη i o z
    let Q := originalGaugeSpectrum z
    Integrable (wardCyclicCubicWeight G a H H H) ∧
      (wardCyclicCubicForm G a (H+Q) (H+Q) (H+Q)).re =
        completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G) b (u+g) := by
  intro b u g H Q
  have hInt₀ := fixed_homogeneous_spectrum_integrable a ha hHom
  have hInt₁ := fixedInfraredSymbol_spectrum_integrable cut add hcut hadd a ha hHom
  have hU : wardRealEnergySpectrum (u+g) = H+Q := by
    funext ξ d e
    change radianEval ξ (actualThinSchwartzField (inverseMatrix G) wi wo hm hη i o z (d,e) +
      Burnett.C03.projectedGaugeComplement z d e) =
      radianEval ξ (actualThinSchwartzField (inverseMatrix G) wi wo hm hη i o z (d,e)) +
      radianEval ξ (Burnett.C03.projectedGaugeComplement z d e)
    rw [map_add]
  have hPure : wardRealEnergySpectrum u = H := rfl
  have h₀ := (wardCyclicActualFourier_eq_oddTestEnergy G hG a u hInt₀).1
  have h₁ := (wardCyclicActualFourier_eq_oddTestEnergy G hG b (u+g) hInt₁).2
  rw [hPure] at h₀
  rw [hU] at h₁
  have hb := wardActualCyclicCubicForm_fixedInfrared_test G hG a cut add hCut hAdd wi wo hm hη i o z
  exact ⟨h₀, (congrArg Complex.re hb.symm).trans (h₁.trans
    (frozenActionCyclicOddTestEnergy_fixedInfrared_eq_complete G cut add hcut hadd a ha hHom
      D hD hJets hOdd (u+g)))⟩

end Burnett.C02
