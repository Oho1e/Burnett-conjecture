import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableBrackets
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLorentzScreenPairing
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableFactors
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers

set_option autoImplicit false
set_option maxRecDepth 7300
set_option maxHeartbeats 17000000

noncomputable section

namespace Burnett.C02

open Set Burnett.RicciSymbol Burnett.A02.FrequencySplit Burnett.A05
open Burnett.P01 (ComplexComponents ComplexCovector)
open Burnett.V08 (signedCyclicPhase)
open scoped ContDiff

open private wardComparableGaugePotential wardComparableGaugePotential_smooth from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableBrackets
open private wardComparableDenominator from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableFactors
open private raisedWardScreenEntry raisedWardGaugeComponent from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
open private wardTwoGaugePair raisedScreenBilinear from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers

private abbrev WardJointComparable := E × Joint

/-- The actual comparable Ward phase factors are smooth jointly in the
frozen center and all nonzero signed-frequency variables. -/
theorem wardComparablePhaseProfiles_jointSmooth (V : Set E) (m : E → Tensor2) (w : E → ℝ)
    (hm : ∀ a b, ContDiffOn ℝ ∞ (fun x => m x a b) V) (hw : ContDiffOn ℝ ∞ w V)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0}) (G H J : ComplexComponents) :
    let O := V ×ˢ wardTriadDomain
    (∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x : WardJointComparable => wardComparableOneGaugeProfiles (m x.1) (w x.1)
      (fun y => a (x.1,y)) G H J j x.2) O) ∧
    ContDiffOn ℝ ∞ (fun x : WardJointComparable => wardComparableTwoGaugeProfile (m x.1) (w x.1)
      (fun y => a (x.1,y)) G H J x.2) O := by
  intro O
  let ξ (j : Fin 3) (x : WardJointComparable) := wardPhaseCovector x.2 j
  have hξ (j : Fin 3) : ContDiff ℝ ∞ (ξ j) := (wardPhaseCovector_contDiff j).comp contDiff_snd
  have hξ₀ (j : Fin 3) (x : WardJointComparable) (hx : x ∈ O) : ξ j x ≠ 0 :=
    wardPhaseCovector_ne_zero j hx.2
  have hCoord (j : Fin 3) (i : Index) : ContDiffOn ℝ ∞ (fun x => (ξ j x i : ℂ)) O :=
    (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (hξ j))).contDiffOn
  have hNorm (j : Fin 3) : ContDiffOn ℝ ∞ (fun x => (‖ξ j x‖ : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((hξ j).contDiffOn.norm ℝ (hξ₀ j))
  have hScalar (j : Fin 3) : ContDiffOn ℝ ∞ (fun x => (a (x.1,ξ j x) : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (ha.comp (contDiff_fst.prodMk (hξ j)).contDiffOn (fun x hx => hξ₀ j x hx))
  have hPhase (j : Fin 3) : ContDiffOn ℝ ∞ (fun x =>
      wardComparablePhaseFactor (w x.1) (fun y => a (x.1,y)) j x.2) O := by
    have hw' : ContDiffOn ℝ ∞ (fun x : WardJointComparable => (w x.1 : ℂ)) O :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hw.comp contDiff_fst.contDiffOn (fun _ hx => hx.1))
    have hZ (x : WardJointComparable) (hx : x ∈ O) :
        (‖ξ 0 x‖ : ℂ) * (‖ξ 1 x‖ : ℂ) * (‖ξ 2 x‖ : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hξ₀ 0 x hx)))
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hξ₀ 1 x hx))))
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hξ₀ 2 x hx)))
    have hInv := (((hNorm 0).mul (hNorm 1)).mul (hNorm 2)).inv hZ
    have h := (((((hScalar 0).add (hScalar 1)).add (hScalar 2)).mul hw').mul ((hNorm j).pow 2)).mul hInv
    simpa only [wardComparablePhaseFactor, signedCyclicPhase, wardComparableDenominator, div_eq_mul_inv,
      Complex.ofReal_add, Complex.ofReal_mul, ξ, wardPhaseCovector, Matrix.cons_val_zero,
      Matrix.cons_val_one, wardSignedThird] using h
  have hEntry (i j : Index) : ContDiffOn ℝ ∞ (fun x : WardJointComparable => (m x.1 i j : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((hm i j).comp contDiff_fst.contDiffOn (fun _ hx => hx.1))
  have hRaised (A : ComplexComponents) (i j : Index) :
      ContDiffOn ℝ ∞ (fun x : WardJointComparable => raisedWardScreenEntry (m x.1) A i j) O := by
    unfold raisedWardScreenEntry
    exact ContDiffOn.sum fun c _ => ContDiffOn.sum fun d _ => ((hEntry i c).mul (hEntry j d)).mul contDiffOn_const
  have hGauge (A : ComplexComponents) (j : Fin 3) (i : Index) :
      ContDiffOn ℝ ∞ (fun x => wardComparableGaugePotential (ξ j x) A i) O :=
    (wardComparableGaugePotential_smooth A j i).comp contDiff_snd.contDiffOn (fun _ hx => hx.2)
  have hRaisedG (A : ComplexComponents) (j : Fin 3) (i : Index) :
      ContDiffOn ℝ ∞ (fun x => raisedWardGaugeComponent (m x.1) (wardComparableGaugePotential (ξ j x) A) i) O := by
    unfold raisedWardGaugeComponent
    exact ContDiffOn.sum fun c _ => (hEntry i c).mul (hGauge A j c)
  have hPair : ContDiffOn ℝ ∞ (fun x : WardJointComparable => frozenWardScreenPair (m x.1) H J) O := by
    simp_rw [wardFrozenScreenPair_eq_raised]
    exact (contDiffOn_const (c := (1 / 4 : ℂ))).mul (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      (contDiffOn_const (c := J i j)).mul (hRaised H i j))
  have hHigh (A B : ComplexComponents) (j : Fin 3) : ContDiffOn ℝ ∞
      (fun x => wardHighGaugeBracket (m x.1) (frozenWardScreenPair (m x.1) H J) A B
        (wardComparableGaugePotential (ξ 2 x) G) (ξ j x)) O := by
    unfold wardHighGaugeBracket
    exact (((contDiffOn_const (c := (-2 : ℂ))).mul (ContDiffOn.sum fun i _ =>
      (hRaisedG G 2 i).mul (hCoord j i))).mul hPair).add
      (ContDiffOn.sum fun i _ => ContDiffOn.sum fun k _ => ContDiffOn.sum fun c _ =>
        (((hRaised A i k).mul (hCoord j i)).mul (contDiffOn_const (c := B k c))).mul (hRaisedG G 2 c))
  have hDouble : ContDiffOn ℝ ∞ (fun x => wardTwoGaugeBracket (m x.1) J
      (wardComparableGaugePotential (ξ 2 x) H) (wardComparableGaugePotential (ξ 1 x) G) (ξ 1 x)) O := by
    unfold wardTwoGaugeBracket wardTwoGaugePair raisedScreenBilinear
    exact (ContDiffOn.sum fun j _ => (hGauge H 2 j).mul (hRaisedG G 1 j)).mul
      (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ((hRaised J i j).mul (hCoord 1 i)).mul (hCoord 1 j))
  constructor
  · intro j
    fin_cases j
    · exact (hPhase 0).mul (hHigh H J 1)
    · exact (hPhase 1).mul (hHigh J H 0)
  · exact (hPhase 0).mul hDouble

end Burnett.C02
