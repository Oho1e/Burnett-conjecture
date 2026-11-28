import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleParametricCyclic
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLorentzScreenPairing
import Burnett.Analysis.FrozenTransport.Ward.WardAllScalePhaseBranchSymbols
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers

set_option autoImplicit false
set_option maxRecDepth 7600
set_option maxHeartbeats 18400000

noncomputable section

namespace Burnett.C02

open Set Burnett.RicciSymbol Burnett.A02.FrequencySplit Burnett.A05
open Burnett.P01 (ComplexComponents)
open Burnett.V08 (cyclicLowNormalizedPhase normalizedGaugePotential normalizedGaugePotential_contDiff)
open scoped ContDiff

open private raisedWardScreenEntry raisedWardGaugeComponent wardHighThirdVector wardHighThirdVector_ne_zero from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
open private wardLieVector from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers
open private wardTwoGaugePair raisedScreenBilinear from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers

private abbrev WardJointLow := E × WardLowPoint

/-- Each actual first-low Ward phase profile is smooth jointly in the
original frozen center and in the two independent angles and frequency ratio. -/
theorem wardLowPhaseProfiles_jointSmooth (V : Set E) (m : E → Tensor2) (w : E → ℝ)
    (hm : ∀ a b, ContDiffOn ℝ ∞ (fun x => m x a b) V) (hw : ContDiffOn ℝ ∞ w V)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0}) (G H J : ComplexComponents) :
    let O := V ×ˢ wardLowProfileDomain
    ContDiffOn ℝ ∞ (fun x : WardJointLow => lowGaugeScalarPhaseProfiles (m x.1) (w x.1)
      (fun y => a (x.1,y)) G H J x.2) O ∧
    ContDiffOn ℝ ∞ (fun x : WardJointLow => lowGaugeLiePhaseProfiles (m x.1) (w x.1)
      (fun y => a (x.1,y)) G H J x.2) O ∧
    ContDiffOn ℝ ∞ (fun x : WardJointLow => highGaugePhaseProfiles (m x.1) (w x.1)
      (fun y => a (x.1,y)) G H J x.2) O ∧
    ContDiffOn ℝ ∞ (fun x : WardJointLow => twoGaugePhaseProfiles (m x.1) (w x.1)
      (fun y => a (x.1,y)) G H J x.2) O := by
  intro O
  let d (x : WardJointLow) := x.2.1
  let θ (x : WardJointLow) := x.2.2.1
  let R (x : WardJointLow) := wardHighThirdVector x.2
  let α (x : WardJointLow) := (cyclicLowNormalizedPhase (fun y => a (x.1,y))
    (d x) (x.2.2.2 • d x) (θ x) : ℂ)
  let μ (x : WardJointLow) := (w x.1 : ℂ)
  let ρ (x : WardJointLow) := (‖R x‖ : ℂ)
  have hd : ContDiff ℝ ∞ d := contDiff_snd.fst
  have hθ : ContDiff ℝ ∞ θ := contDiff_snd.snd.fst
  have hR : ContDiff ℝ ∞ R := (hθ.add (contDiff_snd.snd.snd.smul hd)).neg
  have hR₀ (x : WardJointLow) (hx : x ∈ O) : R x ≠ 0 := wardHighThirdVector_ne_zero x.2 hx.2
  have hρ : ContDiffOn ℝ ∞ ρ O := Complex.ofRealCLM.contDiff.comp_contDiffOn (hR.contDiffOn.norm ℝ hR₀)
  have hρ₀ (x : WardJointLow) (hx : x ∈ O) : ρ x ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hR₀ x hx))
  have hα : ContDiffOn ℝ ∞ α O := by
    apply Complex.ofRealCLM.contDiff.comp_contDiffOn ((wardParametricCyclicPhase a ha).comp
      (contDiff_fst.prodMk (((contDiff_snd.snd.snd.smul hd).prodMk hθ).prodMk hd)).contDiffOn ?_)
    intro x hx
    exact ⟨mem_univ _,hx.2⟩
  have hμ : ContDiffOn ℝ ∞ μ O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hw.comp contDiff_fst.contDiffOn (fun _ hx => hx.1))
  have hEntry (i j : Index) : ContDiffOn ℝ ∞ (fun x : WardJointLow => (m x.1 i j : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((hm i j).comp contDiff_fst.contDiffOn (fun _ hx => hx.1))
  have hCoordinate (q : WardJointLow → E) (hq : ContDiff ℝ ∞ q) (j : Index) :
      ContDiffOn ℝ ∞ (fun x => (q x j : ℂ)) O :=
    (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hq)).contDiffOn
  have hGauge (A : ComplexComponents) (q : WardJointLow → E) (hq : ContDiffOn ℝ ∞ q O) (j : Index) :
      ContDiffOn ℝ ∞ (fun x => normalizedGaugePotential (q x) A j) O :=
    (normalizedGaugePotential_contDiff A j).comp_contDiffOn hq
  have hDir : ContDiffOn ℝ ∞ (endpointDirection ∘ R) O :=
    endpointDirection_contDiffOn.comp hR.contDiffOn hR₀
  let u (x : WardJointLow) := normalizedGaugePotential (d x) G
  let v (x : WardJointLow) := normalizedGaugePotential (endpointDirection (R x)) G
  let vJ (x : WardJointLow) := normalizedGaugePotential (endpointDirection (R x)) H
  let uθ (x : WardJointLow) := normalizedGaugePotential (θ x) G
  have hu (j : Index) : ContDiffOn ℝ ∞ (fun x => u x j) O := hGauge G d hd.contDiffOn j
  have hv (j : Index) : ContDiffOn ℝ ∞ (fun x => v x j) O := hGauge G _ hDir j
  have hvJ (j : Index) : ContDiffOn ℝ ∞ (fun x => vJ x j) O := hGauge H _ hDir j
  have huθ (j : Index) : ContDiffOn ℝ ∞ (fun x => uθ x j) O := hGauge G θ hθ.contDiffOn j
  have hRaised (A : ComplexComponents) (i j : Index) :
      ContDiffOn ℝ ∞ (fun x : WardJointLow => raisedWardScreenEntry (m x.1) A i j) O := by
    unfold raisedWardScreenEntry
    exact ContDiffOn.sum fun c _ => ContDiffOn.sum fun b _ =>
      ((hEntry i c).mul (hEntry j b)).mul contDiffOn_const
  have hPair (A B : ComplexComponents) :
      ContDiffOn ℝ ∞ (fun x : WardJointLow => frozenWardScreenPair (m x.1) A B) O := by
    simp_rw [wardFrozenScreenPair_eq_raised]
    exact (contDiffOn_const (c := (1 / 4 : ℂ))).mul
      (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (contDiffOn_const (c := B i j)).mul (hRaised A i j))
  have hRaisedG (b : WardJointLow → ComplexCovector) (hb : ∀ j, ContDiffOn ℝ ∞ (fun x => b x j) O) (i : Index) :
      ContDiffOn ℝ ∞ (fun x : WardJointLow => raisedWardGaugeComponent (m x.1) (b x) i) O := by
    unfold raisedWardGaugeComponent
    exact ContDiffOn.sum fun j _ => (hEntry i j).mul (hb j)
  have hDot : ContDiffOn ℝ ∞ (fun x => raisedWardGaugeDot (m x.1) (u x) (d x)) O := by
    unfold raisedWardGaugeDot
    exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      ((hEntry i j).mul (hu j)).mul (hCoordinate d hd i)
  have hLie (A B : ComplexComponents) :
      ContDiffOn ℝ ∞ (fun x => wardScreenLieContraction (m x.1) A B (u x) (d x)) O := by
    have hV (j : Index) : ContDiffOn ℝ ∞ (fun x => wardLieVector (m x.1) B (u x) j) O := by
      unfold wardLieVector
      exact ContDiffOn.sum fun c _ => (contDiffOn_const (c := B c j)).mul (hRaisedG u hu c)
    have hK (i j : Index) : ContDiffOn ℝ ∞ (fun x => wardLieGaugeInsertion (m x.1) B (u x) (d x) i j) O :=
      ((hCoordinate d hd i).mul (hV j)).add ((hCoordinate d hd j).mul (hV i))
    unfold wardScreenLieContraction
    simp_rw [wardFrozenScreenPair_eq_raised]
    exact (contDiffOn_const (c := (1 / 4 : ℂ))).mul (ContDiffOn.sum fun i _ =>
      ContDiffOn.sum fun j _ => (hK i j).mul (hRaised A i j))
  have hHigh (A B : ComplexComponents) (q : WardJointLow → E) (hq : ContDiff ℝ ∞ q) :
      ContDiffOn ℝ ∞ (fun x => wardHighGaugeBracket (m x.1) (frozenWardScreenPair (m x.1) H J) A B (v x) (q x)) O := by
    unfold wardHighGaugeBracket
    exact (((contDiffOn_const (c := (-2 : ℂ))).mul (ContDiffOn.sum fun i _ =>
      (hRaisedG v hv i).mul (hCoordinate q hq i))).mul (hPair H J)).add
      (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ContDiffOn.sum fun c _ =>
        (((hRaised A i j).mul (hCoordinate q hq i)).mul (contDiffOn_const (c := B j c))).mul (hRaisedG v hv c))
  have hTwo (q : WardJointLow → E) (hq : ContDiff ℝ ∞ q)
      (b : WardJointLow → ComplexCovector) (hb : ∀ j, ContDiffOn ℝ ∞ (fun x => b x j) O) :
      ContDiffOn ℝ ∞ (fun x => wardTwoGaugeBracket (m x.1) J (vJ x) (b x) (q x)) O := by
    unfold wardTwoGaugeBracket wardTwoGaugePair raisedScreenBilinear
    exact (ContDiffOn.sum fun j _ => (hvJ j).mul (hRaisedG b hb j)).mul
      (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
        ((hRaised J i j).mul (hCoordinate q hq i)).mul (hCoordinate q hq j))
  have hρsym (x : WardJointLow) : (‖x.2.2.1 + x.2.2.2 • x.2.1‖ : ℂ) = ρ x := by
    simp only [ρ, R, wardHighThirdVector, norm_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ((hα.mul hμ).mul hDot).mul (hPair H J)
    unfold lowGaugeScalarPhaseProfiles
    simp_rw [hρsym, div_eq_mul_inv]
    exact (h.mul (hρ.inv hρ₀)).prodMk (h.mul hρ)
  · have h := ((contDiffOn_const (c := (-2 : ℂ))).mul hα).mul hμ
    unfold lowGaugeLiePhaseProfiles
    simp only [div_eq_mul_inv]
    exact ((h.mul (hLie H J)).mul (hρ.inv hρ₀)).prodMk ((h.mul (hLie J H)).mul hρ)
  · have h := (hα.mul hμ).mul ((hρ.inv hρ₀).pow 2)
    exact (h.mul (hHigh H J θ hθ)).prodMk (h.mul (hHigh J H d hd))
  · have h := (hα.mul hμ).mul ((hρ.inv hρ₀).pow 2)
    exact (h.mul (hTwo θ hθ uθ huθ)).prodMk (h.mul (hTwo d hd u hu))

end Burnett.C02
