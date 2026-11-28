import Burnett.Analysis.TransportWard.Weyl.WeylLeadingProfile

set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option maxRecDepth 1700

noncomputable section

namespace Burnett.V03.Palatini

open Function Set Filter MeasureTheory Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped ContDiff

local notation "P" => RadianParameter
local notation "W" => radianFrequencyWeight
local notation "D" => frozenSchwartzCoordinatePartial

open private frequencyDirectionalSymbol_order_zero_of_scaled_one coordinateSymbol_bounds from Burnett.Analysis.TransportWard.Weyl.WeylLeadingProfile
open private firstOrderAction_input_coordinateDerivative norm_physicalRadianCovector_le from Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction

theorem coefficientCommutatorSymbol_order_zero {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (c : SchwartzMap E ℂ) :
    ContDiff ℝ ∞ (uncurry (coefficientCommutatorSymbol a c)) ∧
      BaseDerivativeBounds (coefficientCommutatorSymbol a c) (fun _ => 1) := by
  obtain ⟨hs,hL⟩ := coefficientCommutatorRemainder_joint_order_minus_one ha c
  have hR : BaseDerivativeBounds (coefficientCommutatorRemainder a c) (fun _ => 1) := by
    apply BaseDerivativeBounds.of_joint hs
    intro n
    obtain ⟨C,hC,hB⟩ := hL n
    exact ⟨C,hC,fun p => (hB p).trans ((div_le_self hC (radian_frequency_weight_one_le p.2)).trans_eq (mul_one _).symm)⟩
  have hLead := coefficientCommutatorLeading_bounds (frequencyDirectionalSymbol_order_zero_of_scaled_one ha) c
  have he : coefficientCommutatorSymbol a c = fun x ξ => coefficientCommutatorLeading a c x ξ +
      coefficientCommutatorRemainder a c x ξ :=
    funext fun x => funext (coefficientCommutatorSymbol_eq_leading_add_remainder ha.firstBaseFrequency.frequency c x)
  rw [he]
  exact ⟨(coefficientCommutatorLeading_smooth ha.smooth c).add hs,hLead.add hR⟩

/-- The exact left symbol of the first-order part `i[c ∂j,B]`. -/
def lowerFirstOrderWeylCommutatorSymbol (a : E → E → ℂ) (c : SchwartzMap E ℂ) (j : Fin 4) (x ξ : E) : ℂ :=
  (Complex.I * c x) * baseDirectionSymbol a (coordinateDirection j) x ξ +
    (-Complex.I * (physicalRadianCovector ξ j : ℂ)) * coefficientCommutatorSymbol a c x ξ

theorem lowerFirstOrderWeylCommutatorSymbol_profile {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (c : SchwartzMap E ℂ) (j : Fin 4) :
    ContDiff ℝ ∞ (uncurry (lowerFirstOrderWeylCommutatorSymbol a c j)) ∧
      BaseDerivativeBounds (lowerFirstOrderWeylCommutatorSymbol a c j) W := by
  let A := baseDirectionSymbol a (coordinateDirection j)
  let Q := coefficientCommutatorSymbol a c
  have hA := ha.baseDirection (coordinateDirection j)
  obtain ⟨hQ,hQB⟩ := coefficientCommutatorSymbol_order_zero ha c
  have hAB : BaseDerivativeBounds A W :=
    ⟨fun ξ => hA.smooth.comp (contDiff_id.prodMk contDiff_const),hA.pureBase⟩
  have hI (z : ℂ) : BaseDerivativeBounds (fun _ _ => z) (fun _ => 1) :=
    BaseDerivativeBounds.frequency_multiplier _ _ ‖z‖ (norm_nonneg _)
      (fun _ => zero_le_one) (fun _ => by rw [mul_one])
  have hX := (((hI Complex.I).mul (BaseDerivativeBounds.schwartz_coefficient c)
    (fun _ => zero_le_one)).weight_congr (fun ξ => one_mul (1 : ℝ))).mul hAB (fun _ => zero_le_one)
  have hY₀ : BaseDerivativeBounds (fun _ ξ => -Complex.I * (physicalRadianCovector ξ j : ℂ)) W :=
    ((hI (-Complex.I)).mul (coordinateSymbol_bounds j) (fun _ => zero_le_one)).weight_congr
      (fun ξ => one_mul (W ξ))
  have hY := hY₀.mul hQB (fun ξ => (radian_frequency_weight_pos ξ).le)
  have hs₁ : ContDiff ℝ ∞ (fun p : P => Complex.I * c p.1 * A p.1 p.2) :=
    (contDiff_const.mul (c.smooth'.comp contDiff_fst)).mul hA.smooth
  have hs₂ : ContDiff ℝ ∞ (fun p : P => (-Complex.I * (physicalRadianCovector p.2 j : ℂ)) * Q p.1 p.2) :=
    (contDiff_const.mul ((physicalRadianCovector_complex_smooth j).comp contDiff_snd)).mul hQ
  exact ⟨hs₁.add hs₂,(hX.weight_congr (fun ξ => one_mul (W ξ))).add
    (hY.weight_congr (fun ξ => mul_one (W ξ)))⟩

private theorem continuous_frequency_section {q : E → E → ℂ} (h : ContDiff ℝ ∞ (uncurry q))
    (x : E) : Continuous (q x) := by
  change Continuous (uncurry q ∘ fun ξ : E => (x,ξ))
  exact h.continuous.comp (continuous_const.prodMk continuous_id)

theorem firstOrderAction_lowerFirstOrderWeylCommutatorSymbol {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (c : SchwartzMap E ℂ) (j : Fin 4) (u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction (lowerFirstOrderWeylCommutatorSymbol a c j) u x =
      Complex.I * (c x * physicalCoordinatePartial j (firstOrderAction a u) x -
        firstOrderAction a (scalarSchwartzProduct c (D j u)) x) := by
  let A := baseDirectionSymbol a (coordinateDirection j)
  let Q := coefficientCommutatorSymbol a c
  let A₁ (y ξ : E) := (Complex.I * c y) * A y ξ
  let Q₁ (y ξ : E) := (-Complex.I * (physicalRadianCovector ξ j : ℂ)) * Q y ξ
  have hA := ha.baseDirection (coordinateDirection j)
  have hAi : Integrable (leftActionIntegrand A u x) volume := by
    obtain ⟨C,_,hC⟩ := hA.pureBase 0
    refine leftActionIntegrand_integrable_of_growth u x
      (hA.smooth.continuous.comp (continuous_const.prodMk continuous_id)) 1 (M := C) (fun ξ => ?_)
    simpa only [norm_iteratedFDeriv_zero,pow_one] using hC x ξ
  have hA₁ : Integrable (leftActionIntegrand A₁ u x) volume := by
    convert hAi.const_mul (Complex.I*c x) using 1
    funext ξ
    simp only [leftActionIntegrand,A₁]
    ring
  obtain ⟨hQs,hQb⟩ := coefficientCommutatorSymbol_order_zero ha c
  obtain ⟨C,_,hQ₀⟩ := hQb.bound 0
  have hτ : 0 ≤ tau := (mul_pos (by norm_num) Real.pi_pos).le
  have hQ₁ : Integrable (leftActionIntegrand Q₁ u x) volume := by
    have hZ : Continuous (fun ξ => -Complex.I * (physicalRadianCovector ξ j : ℂ)) :=
      continuous_const.mul (physicalRadianCovector_complex_smooth j).continuous
    have hQx : Continuous (Q x) :=
      continuous_frequency_section (q := coefficientCommutatorSymbol a c) hQs x
    have hQ₁x : Continuous (Q₁ x) := hZ.mul hQx
    refine leftActionIntegrand_integrable_of_growth u x hQ₁x 1 (M := tau*C) (fun ξ => ?_)
    have hQval : ‖Q x ξ‖ ≤ C := by simpa only [norm_iteratedFDeriv_zero,mul_one] using hQ₀ x ξ
    simp only [Q₁,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,pow_one]
    refine (mul_le_mul (norm_physicalRadianCovector_le j ξ) hQval (norm_nonneg _)
      (mul_nonneg hτ (radian_frequency_weight_pos ξ).le)).trans_eq ?_
    change (tau * W ξ) * C = (tau * C) * W ξ
    ring
  have hActA : firstOrderAction A₁ u x = (Complex.I * c x) * firstOrderAction A u x := by
    simp only [firstOrderAction_eq_leftActionIntegrand,← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun ξ => by simp only [leftActionIntegrand,A₁]; ring
  have hActQ : firstOrderAction Q₁ u x = -firstOrderAction Q (D j u) x := by
    rw [firstOrderAction_input_coordinateDerivative Q j u x, ← neg_mul, ← firstOrderAction_symbol_scale]
    exact congrArg (fun a' => firstOrderAction a' u x) (funext fun y => funext fun ξ =>
      mul_assoc (-Complex.I) (physicalRadianCovector ξ j : ℂ) (Q y ξ))
  change firstOrderAction (fun y ξ => A₁ y ξ + Q₁ y ξ) u x = _
  rw [firstOrderAction_symbol_add _ _ hA₁ hQ₁,hActA,hActQ,physicalCoordinatePartial_leftAction ha]
  have hC := firstOrderAction_coefficientCommutatorSymbol ha.firstBaseFrequency.frequency c (D j u) x
  change firstOrderAction Q (D j u) x = _ at hC
  rw [hC]
  ring

theorem lowerFirstOrderWeylCommutatorSymbol_compactBaseOrderOne {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (c : SchwartzMap E ℂ) (j : Fin 4)
    {K : Set E} (hK : IsCompact K) (hZero : ∀ x ∉ K, ∀ ξ, a x ξ = 0) :
    CompactBaseOrderOne (lowerFirstOrderWeylCommutatorSymbol a c j) := by
  apply (lowerFirstOrderWeylCommutatorSymbol_profile ha c j).2.compactBaseOrderOne hK
  intro x hx ξ
  simp only [lowerFirstOrderWeylCommutatorSymbol,
    baseDirectionSymbol_eq_zero_off_closed hK.isClosed hZero (coordinateDirection j) hx,
    coefficientCommutatorSymbol_eq_zero_of_zero_row c (hZero x hx),mul_zero,add_zero]

/-- The order-zero lower term gives precisely `i[c,B]` with opposite
sign to the input-side coefficient commutator. -/
theorem firstOrderAction_lowerZeroOrderWeylCommutator {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (c u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction (fun y ξ => -coefficientCommutatorSymbol a c y ξ) u x =
      Complex.I * (c x * firstOrderAction a u x - firstOrderAction a (scalarSchwartzProduct c u) x) := by
  have h' := firstOrderAction_symbol_scale (coefficientCommutatorSymbol a c) (-1 : ℂ) u x
  rw [show (fun y ξ => -coefficientCommutatorSymbol a c y ξ) =
      (fun y ξ => (-1 : ℂ)*coefficientCommutatorSymbol a c y ξ) by simp only [neg_one_mul],h']
  rw [firstOrderAction_coefficientCommutatorSymbol ha.firstBaseFrequency.frequency]
  ring

theorem lowerZeroOrderWeylCommutator_compactBaseOrderOne {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (c : SchwartzMap E ℂ)
    {K : Set E} (hK : IsCompact K) (hZero : ∀ x ∉ K, ∀ ξ, a x ξ = 0) :
    CompactBaseOrderOne (fun y ξ => -coefficientCommutatorSymbol a c y ξ) := by
  obtain ⟨hs,hB⟩ := coefficientCommutatorSymbol_order_zero ha c
  have hB' : BaseDerivativeBounds (coefficientCommutatorSymbol a c) W := by
    refine ⟨hB.smooth,fun n => ?_⟩
    obtain ⟨C,hC,hV⟩ := hB.bound n
    exact ⟨C,hC,fun x ξ => (hV x ξ).trans
      (mul_le_mul_of_nonneg_left (radian_frequency_weight_one_le ξ) hC)⟩
  have hSign := BaseDerivativeBounds.frequency_multiplier (fun _ => (-1 : ℂ)) (fun _ => 1) 1
    zero_le_one (fun _ => zero_le_one) (fun _ => by simp)
  have hNeg := ((hSign.mul hB' (fun _ => zero_le_one)).weight_congr (fun ξ => one_mul (W ξ)))
  have hEq : (fun y ξ => (-1 : ℂ)*coefficientCommutatorSymbol a c y ξ) =
      (fun y ξ => -coefficientCommutatorSymbol a c y ξ) := by simp only [neg_one_mul]
  rw [hEq] at hNeg
  exact hNeg.compactBaseOrderOne hK (fun x hx ξ => by
    simp only [coefficientCommutatorSymbol_eq_zero_of_zero_row c (hZero x hx),neg_zero])

end Burnett.V03.Palatini
