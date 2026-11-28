import Burnett.Analysis.TransportWard.Weyl.FrozenWeylOperatorRemainder
import Burnett.Analysis.TransportWard.Weyl.VariableWeylScalarRemainder
import Burnett.Analysis.TransportWard.Weyl.WeylBaseSupport
import Burnett.Analysis.PrincipalEnergy.Quantization.CompactQuantization

set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxRecDepth 1800

noncomputable section

namespace Burnett.V03.Palatini

open Function Set MeasureTheory Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open scoped ContDiff BigOperators

local notation "P" => RadianParameter
local notation "J" => Fin 4 × Fin 4
local notation "W" => radianFrequencyWeight

def densityWeylLeadingSymbol {ι : Type*} (c : ι → ι → J → SchwartzMap E ℂ)
    (b : E → E → ℂ) (i j : ι) (x ξ : E) : ℂ :=
  ∑ d : J, (c i j d x * frozenSecondWeylLeading b d.1 d.2 x ξ +
    variableSecondWeylLeading b (c i j d) d x ξ)

/-- The actual exact left symbol after removing the complete second-order
contribution of the same Weyl test. -/
def densityWeylResidualSymbol {ι : Type*} (c : ι → ι → J → SchwartzMap E ℂ)
    (a b : E → E → ℂ) (i j : ι) (x ξ : E) : ℂ :=
  ∑ d : J, (c i j d x *
    (frozenSecondCommutatorSymbol a d.1 d.2 x ξ - frozenSecondWeylLeading b d.1 d.2 x ξ) +
    (variableCoefficientSecondSymbol a (c i j d) d x ξ - variableSecondWeylLeading b (c i j d) d x ξ))

theorem exact_densityWeylSymbol_eq_leading_add_residual {ι : Type*}
    (c : ι → ι → J → SchwartzMap E ℂ) (a b : E → E → ℂ) (i j : ι) (x ξ : E) :
    (∑ d : J, (c i j d x * frozenSecondCommutatorSymbol a d.1 d.2 x ξ +
      variableCoefficientSecondSymbol a (c i j d) d x ξ)) =
      densityWeylLeadingSymbol c b i j x ξ + densityWeylResidualSymbol c a b i j x ξ := by
  unfold densityWeylLeadingSymbol densityWeylResidualSymbol
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  ring

theorem densityWeylResidualSymbol_profile {ι : Type*}
    (c : ι → ι → J → SchwartzMap E ℂ) (i j : ι)
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ) (hθ : HasCompactSupport θ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) :
    let a := windowedWeylLeftSymbol θ β R h
    let b := normalizedWeylSymbol β
    ContDiff ℝ ∞ (uncurry (densityWeylResidualSymbol c a b i j)) ∧
      CompactBaseOrderOne (densityWeylResidualSymbol c a b i j) := by
  intro a b
  let F (d : J) (x ξ : E) := frozenSecondCommutatorSymbol a d.1 d.2 x ξ - frozenSecondWeylLeading b d.1 d.2 x ξ
  let V (d : J) (x ξ : E) := variableCoefficientSecondSymbol a (c i j d) d x ξ -
    variableSecondWeylLeading b (c i j d) d x ξ
  have hF (d : J) : ContDiff ℝ ∞ (uncurry (F d)) ∧ BaseDerivativeBounds (F d) W :=
    frozenSecondCompactWeylSymbol_sub_leading_profile θ β R h hAmp hPlateau hβ d.1 d.2
  have hV (d : J) : ContDiff ℝ ∞ (uncurry (V d)) ∧ BaseDerivativeBounds (V d) W :=
    variableCoefficientSecondSymbol_sub_normalizedWeylLeading_profile θ β R (c i j d) d h hAmp hPlateau hβ
  let U (d : J) (x ξ : E) := c i j d x * F d x ξ + V d x ξ
  have hU (d : J) : BaseDerivativeBounds (U d) W :=
    (((BaseDerivativeBounds.schwartz_coefficient (c i j d)).mul (hF d).2 (fun _ => zero_le_one)).weight_congr
      (fun ξ => one_mul (W ξ))).add (hV d).2
  have hs : ContDiff ℝ ∞ (uncurry (densityWeylResidualSymbol c a b i j)) := by
    change ContDiff ℝ ∞ (fun p : P => ∑ d : J, U d p.1 p.2)
    exact ContDiff.sum fun d _ => (((c i j d).smooth'.comp contDiff_fst).mul (hF d).1).add (hV d).1
  have hB : BaseDerivativeBounds (densityWeylResidualSymbol c a b i j) W := BaseDerivativeBounds.sum U hU
  refine ⟨hs,hB.compactBaseOrderOne hθ (fun x hx ξ => ?_)⟩
  have hA (y : E) (hy : y ∉ tsupport θ) (ν : E) : a y ν = 0 :=
    windowedWeylLeftSymbol_eq_zero_of_output θ β R h y ν (image_eq_zero_of_notMem_tsupport hy)
  have hD (y : E) (hy : y ∉ tsupport θ) (ν : E) : b y ν = 0 :=
    normalizedWeylSymbol_eq_zero_of_output hPlateau (image_eq_zero_of_notMem_tsupport hy)
  have ha₁ (e : E) (y : E) (hy : y ∉ tsupport θ) (ν : E) : baseDirectionSymbol a e y ν = 0 :=
    baseDirectionSymbol_eq_zero_off_closed (isClosed_tsupport θ) hA e hy
  have ha₂ (e f : E) : baseDirectionSymbol (baseDirectionSymbol a e) f x ξ = 0 :=
    baseDirectionSymbol_eq_zero_off_closed (isClosed_tsupport θ) (ha₁ e) f hx
  have hb₁ (e : E) : baseDirectionSymbol b e x ξ = 0 :=
    baseDirectionSymbol_eq_zero_off_closed (isClosed_tsupport θ) hD e hx
  change (∑ d : J, U d x ξ) = 0
  refine Finset.sum_eq_zero fun d _ => ?_
  simp only [U,F,V,frozenSecondCommutatorSymbol,frozenSecondWeylLeading,
    variableCoefficientSecondSymbol,variableSecondWeylLeading,
    ha₁ _ x hx ξ,ha₂,hb₁,
    coefficientCommutatorSymbol_eq_zero_of_zero_row (c i j d) (hA x hx),
    coefficientCommutatorLeading_eq_zero_of_zero_row (c i j d) (hD x hx),mul_zero,add_zero,sub_zero]

/-- The actual compact Weyl commutator residual is bounded from coordinate
H¹ to L² by the repository's Fourier Young estimate, using the compact
output carried by this same reduced symbol. -/
theorem exists_densityWeylResidualAction_h1_to_l2 {ι : Type*}
    (c : ι → ι → J → SchwartzMap E ℂ) (i j : ι)
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ) (hθ : HasCompactSupport θ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) :
    let a := windowedWeylLeftSymbol θ β R h
    let b := normalizedWeylSymbol β
    let p := densityWeylResidualSymbol c a b i j
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SchwartzMap E ℂ,
      ∃ hL : MemLp (firstOrderAction p u) 2 (volume : Measure E),
        ‖hL.toLp (firstOrderAction p u)‖^2 ≤ C^2 * schwartzH1Energy u := by
  intro a b p
  obtain ⟨hs,hp⟩ := densityWeylResidualSymbol_profile c i j θ β R hθ h hAmp hPlateau hβ
  exact exists_compactBase_firstOrderAction_h1_to_l2 hp hs.continuous

end Burnett.V03.Palatini
