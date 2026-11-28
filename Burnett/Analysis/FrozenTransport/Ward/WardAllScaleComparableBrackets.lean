import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableFactors
import Burnett.Analysis.FrozenTransport.Ward.WardAllScalePhaseBranchSymbols
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers

set_option autoImplicit false
set_option maxRecDepth 6700
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Set Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.RicciSymbol (Tensor2)
open Burnett.P01 (ComplexComponents ComplexCovector)
open Burnett.V08 (normalizedGaugePotential normalizedGaugePotential_contDiff signedCyclicPhase)
open Burnett.Analysis.ProjectiveNullCaps (quadratic)
open scoped ContDiff

open private raisedWardGaugeComponent raisedWardScreenEntry from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
open private wardTwoGaugePair wardTwoGaugeBracket_scale raisedScreenBilinear from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers
open private wardComparableDenominator from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableFactors

private def wardComparableGaugePotential (ξ : E) (G : ComplexComponents) : ComplexCovector :=
  fun b => (‖ξ‖⁻¹ : ℝ) * normalizedGaugePotential (endpointDirection ξ) G b

private theorem wardComparableGaugePotential_smooth (G : ComplexComponents) (j : Fin 3) (b : Fin 4) :
    ContDiffOn ℝ ∞ (fun x : Joint => wardComparableGaugePotential (wardPhaseCovector x j) G b) wardTriadDomain := by
  have hX := wardPhaseCovector_contDiff j
  have hD := endpointDirection_contDiffOn.comp hX.contDiffOn (fun _ hx => wardPhaseCovector_ne_zero j hx)
  have hN := Complex.ofRealCLM.contDiff.comp_contDiffOn (hX.contDiffOn.norm ℝ (fun _ hx => wardPhaseCovector_ne_zero j hx))
  have hInv := hN.inv (fun _ hx => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (wardPhaseCovector_ne_zero j hx)))
  simpa only [wardComparableGaugePotential, Function.comp_apply, Complex.ofReal_inv] using
    hInv.mul ((normalizedGaugePotential_contDiff G b).comp_contDiffOn hD)

private theorem wardComparableGaugePotential_smul (G : ComplexComponents) (t : ℝ) (ht : 0 < t) (ξ : E) :
    wardComparableGaugePotential (t • ξ) G = fun b => (t⁻¹ : ℝ) * wardComparableGaugePotential ξ G b := by
  funext b
  simp only [wardComparableGaugePotential, endpointDirection_pos_smul t ht, norm_smul, Real.norm_of_nonneg ht.le,
    Complex.ofReal_mul, Complex.ofReal_inv, mul_inv_rev]
  ring

private theorem wardComparableRaisedGauge_smooth (m : Tensor2) (G : ComplexComponents) (j : Fin 3) (b : Fin 4) :
    ContDiffOn ℝ ∞ (fun x : Joint => raisedWardGaugeComponent m (wardComparableGaugePotential (wardPhaseCovector x j) G) b)
      wardTriadDomain :=
  ContDiffOn.sum fun c _ => contDiffOn_const.mul (wardComparableGaugePotential_smooth G j c)

private theorem wardComparableHighBracket_smooth (m : Tensor2) (pair : ℂ) (H J G : ComplexComponents) (d : Fin 3) :
    ContDiffOn ℝ ∞ (fun x : Joint => wardHighGaugeBracket m pair H J
      (wardComparableGaugePotential (wardPhaseCovector x 2) G) (wardPhaseCovector x d)) wardTriadDomain := by
  have hv (b : Fin 4) := wardComparableRaisedGauge_smooth m G 2 b
  have hd (i : Fin 4) : ContDiffOn ℝ ∞ (fun x : Joint => (wardPhaseCovector x d i : ℂ)) wardTriadDomain :=
    ((Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).comp (wardPhaseCovector_contDiff d)).contDiffOn
  unfold wardHighGaugeBracket
  exact (((contDiffOn_const (c := (-2 : ℂ))).mul (ContDiffOn.sum (fun i _ => (hv i).mul (hd i)))).mul
    (contDiffOn_const (c := pair))).add (ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ =>
      ContDiffOn.sum fun c _ => (((contDiffOn_const (c := raisedWardScreenEntry m H a b)).mul (hd a)).mul
        (contDiffOn_const (c := J b c))).mul (hv c))

private theorem wardComparableHighBracket_hom (m : Tensor2) (pair : ℂ) (H J G : ComplexComponents) (d : Fin 3)
    (t : ℝ) (ht : 0 < t) (x : Joint) :
    wardHighGaugeBracket m pair H J (wardComparableGaugePotential (wardPhaseCovector (t • x) 2) G)
        (wardPhaseCovector (t • x) d) =
      wardHighGaugeBracket m pair H J (wardComparableGaugePotential (wardPhaseCovector x 2) G) (wardPhaseCovector x d) := by
  rw [wardPhaseCovector_smul t x 2, wardPhaseCovector_smul t x d, wardComparableGaugePotential_smul G t ht,
    wardHighGaugeBracket_scale]
  simp [ht.ne']

/-- The two exact comparable symbols for one high gauge leg, with the
designated physical phases in the first and second actual slots. -/
def wardComparableOneGaugeProfiles (m : Tensor2) (w : ℝ) (a : E → ℝ) (G H J : ComplexComponents)
    (j : Fin 2) (x : Joint) : ℂ :=
  let v := wardComparableGaugePotential (wardPhaseCovector x 2) G
  let pair := frozenWardScreenPair m H J
  ![wardComparablePhaseFactor w a 0 x * wardHighGaugeBracket m pair H J v x.2,
    wardComparablePhaseFactor w a 1 x * wardHighGaugeBracket m pair J H v x.1] j

theorem wardComparableOneGaugeProfiles_smooth_hom (m : Tensor2) (w : ℝ) (a : E → ℝ) (G H J : ComplexComponents)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ) (j : Fin 2) :
    ContDiffOn ℝ ∞ (wardComparableOneGaugeProfiles m w a G H J j) wardTriadDomain ∧
    ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain,
      wardComparableOneGaugeProfiles m w a G H J j (t • x) = wardComparableOneGaugeProfiles m w a G H J j x := by
  let pair := frozenWardScreenPair m H J
  fin_cases j
  · refine ⟨(wardComparablePhaseFactor_smooth w a 0 ha).mul (wardComparableHighBracket_smooth m pair H J G 1),?_⟩
    intro t ht x hx
    exact congrArg₂ (· * ·) (wardComparablePhaseFactor_homogeneous w a 0 hHom t ht x hx)
      (wardComparableHighBracket_hom m pair H J G 1 t ht x)
  · refine ⟨(wardComparablePhaseFactor_smooth w a 1 ha).mul (wardComparableHighBracket_smooth m pair J H G 0),?_⟩
    intro t ht x hx
    exact congrArg₂ (· * ·) (wardComparablePhaseFactor_homogeneous w a 1 hHom t ht x hx)
      (wardComparableHighBracket_hom m pair J H G 0 t ht x)

theorem wardComparableOneGaugeRaw_normalized (m : Tensor2) (w : ℝ) (a : E → ℝ) (G H J : ComplexComponents)
    (x : Joint) (hx : x ∈ wardTriadDomain) :
    wardOneHighGaugeRaw m w a G H J x = wardComparableDenominator x *
      ∑ j : Fin 2, wardComparableOneGaugeProfiles m w a G H J j x *
        (normalizedFrozenPhase m (wardPhaseCovector x (![0,1] j)) : ℂ) := by
  let v := wardComparableGaugePotential (wardPhaseCovector x 2) G
  let pair := frozenWardScreenPair m H J
  let U := wardHighGaugeBracket m pair H J v x.2
  let V := wardHighGaugeBracket m pair J H v x.1
  let D := wardComparableDenominator x
  let F₀ := wardComparablePhaseFactor w a 0 x
  let F₁ := wardComparablePhaseFactor w a 1 x
  let P₀ := (normalizedFrozenPhase m x.1 : ℂ)
  let P₁ := (normalizedFrozenPhase m x.2 : ℂ)
  have h₀ : D * (F₀ * P₀) = (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) * (quadratic m x.1 : ℂ) :=
    wardComparablePhaseFactor_mul_phase m w a 0 x hx
  have h₁ : D * (F₁ * P₁) = (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) * (quadratic m x.2 : ℂ) :=
    wardComparablePhaseFactor_mul_phase m w a 1 x hx
  rw [Fin.sum_univ_two]
  change (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) * ((quadratic m x.1 : ℂ) * U + (quadratic m x.2 : ℂ) * V) =
    D * (F₀ * U * P₀ + F₁ * V * P₁)
  calc
    _ = (D * (F₀ * P₀)) * U + (D * (F₁ * P₁)) * V := by rw [h₀, h₁]; ring
    _ = _ := by ring

/-- The same two-gauge expression on the comparable branch, keeping its
physical phase wherever the physical leg falls in the signed triad. -/
def wardComparableTwoGaugeProfile (m : Tensor2) (w : ℝ) (a : E → ℝ) (G₁ G₂ H : ComplexComponents) (x : Joint) : ℂ :=
  wardComparablePhaseFactor w a 0 x * wardTwoGaugeBracket m H
    (wardComparableGaugePotential (wardPhaseCovector x 2) G₂)
    (wardComparableGaugePotential (wardPhaseCovector x 1) G₁) x.2

theorem wardComparableTwoGaugeProfile_smooth_hom (m : Tensor2) (w : ℝ) (a : E → ℝ) (G₁ G₂ H : ComplexComponents)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ) :
    ContDiffOn ℝ ∞ (wardComparableTwoGaugeProfile m w a G₁ G₂ H) wardTriadDomain ∧
    ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain,
      wardComparableTwoGaugeProfile m w a G₁ G₂ H (t • x) = wardComparableTwoGaugeProfile m w a G₁ G₂ H x := by
  let U (x : Joint) := wardComparableGaugePotential (wardPhaseCovector x 2) G₂
  let V (x : Joint) := wardComparableGaugePotential (wardPhaseCovector x 1) G₁
  let f (x : Joint) := wardTwoGaugeBracket m H (U x) (V x) x.2
  have hu (i : Fin 4) := wardComparableGaugePotential_smooth G₂ 2 i
  have hv (i : Fin 4) := wardComparableRaisedGauge_smooth m G₁ 1 i
  have hq (i : Fin 4) : ContDiffOn ℝ ∞ (fun x : Joint => (x.2 i : ℂ)) wardTriadDomain :=
    ((Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).comp contDiff_snd).contDiffOn
  have hf : ContDiffOn ℝ ∞ f wardTriadDomain := by
    exact (ContDiffOn.sum fun i _ => (hu i).mul (hv i)).mul
      (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ((contDiffOn_const (c := raisedWardScreenEntry m H i j)).mul
        (hq i)).mul (hq j))
  refine ⟨(wardComparablePhaseFactor_smooth w a 0 ha).mul hf,?_⟩
  intro t ht x hx
  have he : f (t • x) = f x := by
    dsimp only [f, U, V, Prod.smul_snd]
    rw [wardPhaseCovector_smul t x 2, wardPhaseCovector_smul t x 1, wardComparableGaugePotential_smul G₂ t ht,
      wardComparableGaugePotential_smul G₁ t ht, wardTwoGaugeBracket_scale]
    have hn : t ≠ 0 := ht.ne'
    have hc : t⁻¹ * t⁻¹ * t^2 = 1 := by field_simp
    rw [hc, Complex.ofReal_one, one_mul]
  exact congrArg₂ (· * ·) (wardComparablePhaseFactor_homogeneous w a 0 hHom t ht x hx) he

theorem wardComparableTwoGaugeRaw_normalized (m : Tensor2) (w : ℝ) (a : E → ℝ) (G₁ G₂ H : ComplexComponents)
    (x : Joint) (hx : x ∈ wardTriadDomain) :
    wardTwoGaugePhysicalLowRaw m w a G₁ G₂ H x = wardComparableDenominator x *
      (wardComparableTwoGaugeProfile m w a G₁ G₂ H x * (normalizedFrozenPhase m x.1 : ℂ)) := by
  let U := wardComparableGaugePotential (wardPhaseCovector x 2) G₂
  let V := wardComparableGaugePotential (wardPhaseCovector x 1) G₁
  let T := wardTwoGaugeBracket m H U V x.2
  let P := (normalizedFrozenPhase m x.1 : ℂ)
  let F := wardComparablePhaseFactor w a 0 x
  let D := wardComparableDenominator x
  have h : D * (F * P) = (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) * (quadratic m x.1 : ℂ) :=
    wardComparablePhaseFactor_mul_phase m w a 0 x hx
  change _ * T = D * (F * T * P)
  rw [← h]
  ring

end Burnett.C02
