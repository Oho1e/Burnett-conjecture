import Burnett.Analysis.TransportWard.Weyl.BaseDerivativeBounds
import Burnett.Analysis.TransportWard.Weyl.FrozenWeylSymbolRemainder
import Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction

set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxRecDepth 1700

noncomputable section

namespace Burnett.V03

open Function Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic (baseDirectionSymbol)
open Burnett.Analysis.CarlesonEmbedding (baseDirectionSymbol_joint_smooth)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped ContDiff

local notation "P" => RadianParameter
local notation "W" => radianFrequencyWeight

open private baseDirectionSymbol_eq_joint from Burnett.Analysis.TransportWard.Weyl.ScaledSymbolA01
open private norm_physicalRadianCovector_le from Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction

private theorem baseDirectionSymbol_order_zero_of_scaled_zero {r : E → E → ℂ}
    (hs : ContDiff ℝ ∞ (uncurry r))
    (h : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P,
      ‖radianScaledParameterJet (uncurry r) n p‖ ≤ C) (e : E) :
    BaseDerivativeBounds (baseDirectionSymbol r e) (fun _ => 1) := by
  apply BaseDerivativeBounds.of_joint (baseDirectionSymbol_joint_smooth hs e)
  intro n
  obtain ⟨C,hC,hB⟩ := h (n+1)
  let d : P := (e,0)
  have hf : uncurry (baseDirectionSymbol r e) = fun p : P => fderiv ℝ (uncurry r) p d :=
    funext (baseDirectionSymbol_eq_joint r hs e)
  have hD : ContDiff ℝ ∞ (fderiv ℝ (uncurry r)) := hs.fderiv_right (by simp)
  refine ⟨‖d‖*C,mul_nonneg (norm_nonneg _) hC,fun p => ?_⟩
  rw [hf,mul_one]
  calc
    _ ≤ ‖d‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ (uncurry r)) p‖ :=
      norm_iteratedFDeriv_clm_apply_const hD.contDiffAt (by exact_mod_cast le_top)
    _ = ‖d‖ * ‖iteratedFDeriv ℝ (n+1) (uncurry r) p‖ := by rw [norm_iteratedFDeriv_fderiv]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((radian_parameter_jet_norm_le_scaled _ (n+1) p).trans (hB p)) (norm_nonneg _)

def frozenSecondWeylLeading (b : E → E → ℂ) (i j : Fin 4) (x ξ : E) : ℂ :=
  (physicalRadianCovector ξ j : ℂ) * baseDirectionSymbol b (coordinateDirection i) x ξ +
    (physicalRadianCovector ξ i : ℂ) * baseDirectionSymbol b (coordinateDirection j) x ξ

private theorem baseDirectionSymbol_sub {a b : E → E → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (hb : ContDiff ℝ ∞ (uncurry b)) (e x ξ : E) :
    baseDirectionSymbol (fun y ν => a y ν - b y ν) e x ξ =
      baseDirectionSymbol a e x ξ - baseDirectionSymbol b e x ξ := by
  have hp : ContDiff ℝ ∞ (fun y : E => (y,ξ)) := contDiff_id.prodMk contDiff_const
  have hA : DifferentiableAt ℝ (fun y => a y ξ) x := (ha.comp hp).differentiable (by simp) x
  have hB : DifferentiableAt ℝ (fun y => b y ξ) x := (hb.comp hp).differentiable (by simp) x
  exact DFunLike.congr_fun (fderiv_fun_sub hA hB) e

/-- The exact frozen correction keeps the order-one pure spatial jets on
the full same reduced Weyl symbol. The twice differentiated left symbol has
no multiplier of degree one, while the first-derivative terms use the order
zero difference between the exact left symbol and its diagonal. -/
theorem frozenSecondCompactWeylSymbol_sub_leading_profile
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) (i j : Fin 4) :
    let a := windowedWeylLeftSymbol θ β R h
    let b := normalizedWeylSymbol β
    let v (x ξ : E) := frozenSecondCommutatorSymbol a i j x ξ - frozenSecondWeylLeading b i j x ξ
    ContDiff ℝ ∞ (uncurry v) ∧ BaseDerivativeBounds v W := by
  intro a b v
  let r (x ξ : E) := a x ξ - b x ξ
  let D (k : Fin 4) := baseDirectionSymbol r (coordinateDirection k)
  let L := baseDirectionSymbol (baseDirectionSymbol a (coordinateDirection j)) (coordinateDirection i)
  let K (k : Fin 4) (ξ : E) := (physicalRadianCovector ξ k : ℂ)
  have ha : ScaledJointOrderOne a := windowedWeyl_leftSymbol_scaled_order_one θ β R h hAmp hPlateau hβ
  obtain ⟨hr, hR⟩ := windowedWeyl_leftSymbol_scaled_remainder θ β R h hAmp hPlateau
  have hL : ScaledJointOrderOne L := (ha.baseDirection (coordinateDirection j)).baseDirection (coordinateDirection i)
  have hD (k : Fin 4) : ContDiff ℝ ∞ (uncurry (D k)) := baseDirectionSymbol_joint_smooth hr (coordinateDirection k)
  have hDB (k : Fin 4) : BaseDerivativeBounds (D k) (fun _ => 1) :=
    baseDirectionSymbol_order_zero_of_scaled_zero hr hR (coordinateDirection k)
  have hkB (k : Fin 4) := BaseDerivativeBounds.frequency_multiplier (K k) W tau
    (mul_pos (by norm_num) Real.pi_pos).le (fun ξ => (radian_frequency_weight_pos ξ).le)
    (fun ξ => by simpa only [K,Complex.norm_real] using norm_physicalRadianCovector_le k ξ)
  have hTerm (a b : Fin 4) : BaseDerivativeBounds (fun x ξ => K a ξ * D b x ξ) W :=
    ((hkB a).mul (hDB b) (fun ξ => (radian_frequency_weight_pos ξ).le)).weight_congr
      (fun ξ => mul_one _)
  have hI := BaseDerivativeBounds.frequency_multiplier (fun _ => -Complex.I) (fun _ => 1) 1
    zero_le_one (fun _ => zero_le_one) (fun _ => by simp)
  have hLast : BaseDerivativeBounds (fun x ξ => (-Complex.I) * L x ξ) W :=
    (hI.mul ⟨fun ξ => hL.smooth.comp (contDiff_id.prodMk contDiff_const),hL.pureBase⟩
      (fun _ => zero_le_one)).weight_congr
      (fun ξ => one_mul _)
  have he : v = fun x ξ => K j ξ * D i x ξ + K i ξ * D j x ξ + (-Complex.I) * L x ξ := by
    funext x ξ
    have hBase (e : E) : baseDirectionSymbol r e x ξ =
        baseDirectionSymbol a e x ξ - baseDirectionSymbol b e x ξ :=
      baseDirectionSymbol_sub ha.smooth hβ.smooth e x ξ
    simp only [v,frozenSecondCommutatorSymbol,frozenSecondWeylLeading,D,L,K,hBase]
    ring
  rw [he]
  have hU := ((physicalRadianCovector_complex_smooth j).comp contDiff_snd).mul (hD i)
  have hV := ((physicalRadianCovector_complex_smooth i).comp contDiff_snd).mul (hD j)
  exact ⟨(hU.add hV).add (contDiff_const.mul hL.smooth), ((hTerm j i).add (hTerm i j)).add hLast⟩

end Burnett.V03
