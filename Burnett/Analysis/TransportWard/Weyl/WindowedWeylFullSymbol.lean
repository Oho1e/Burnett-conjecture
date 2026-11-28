import Burnett.Analysis.TransportWard.Weyl.ScaledSymbolA01

/-! Main Weyl amplitude and its genuine A03 remainder produce exactly one
order-one A01 symbol for the localized test. -/

set_option autoImplicit false
set_option maxHeartbeats 6900000
set_option maxRecDepth 4400

noncomputable section

namespace Burnett.V03

open Function MeasureTheory Set Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff Topology BigOperators

local notation "P" => RadianParameter
local notation "W" => radianFrequencyWeight

private theorem scaled_joint_add (a b : E → E → ℂ)
    (ha : ContDiff ℝ ∞ (uncurry a)) (hb : ContDiff ℝ ∞ (uncurry b)) (n : ℕ) (p : P) :
    radianScaledParameterJet (uncurry (fun x ξ => a x ξ + b x ξ)) n p =
      radianScaledParameterJet (uncurry a) n p + radianScaledParameterJet (uncurry b) n p := by
  let s := W p.2
  have A : ContDiff ℝ ∞ (fun z => uncurry a (p + radianParameterScale s z)) :=
    ha.comp (contDiff_const.add (radianParameterScale s).contDiff)
  have B : ContDiff ℝ ∞ (fun z => uncurry b (p + radianParameterScale s z)) :=
    hb.comp (contDiff_const.add (radianParameterScale s).contDiff)
  have H : ContDiff ℝ ∞ (uncurry (fun x ξ => a x ξ + b x ξ)) := ha.add hb
  have hScaled (f : P → ℂ) (hf : ContDiff ℝ ∞ f) :
      iteratedFDeriv ℝ n (fun z => f (p + radianParameterScale s z)) 0 = radianScaledParameterJet f n p :=
    radian_parameter_jet_affine f hf n p s
  rw [← hScaled _ H, ← hScaled _ ha, ← hScaled _ hb]
  change iteratedFDeriv ℝ n ((fun z => uncurry a (p + radianParameterScale s z)) +
    (fun z => uncurry b (p + radianParameterScale s z))) 0 = _
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  exact iteratedFDeriv_add_apply (A.contDiffAt.of_le hn) (B.contDiffAt.of_le hn)

private theorem tau_at_least_one : 1 ≤ tau := by
  change 1 ≤ 2 * Real.pi
  linarith [Real.two_le_pi]

private theorem scaled_radian_order_zero_normalize (r : E → E → ℂ)
    (hs : ContDiff ℝ ∞ (uncurry r))
    (h : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, ‖radianScaledParameterJet (uncurry r) n p‖ ≤ C) :
    ContDiff ℝ ∞ (uncurry (normalizedWeylSymbol r)) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P,
        ‖radianScaledParameterJet (uncurry (normalizedWeylSymbol r)) n p‖ ≤ C := by
  have hsN : ContDiff ℝ ∞ (uncurry (normalizedWeylSymbol r)) := hs.comp (radianParameterScale tau).contDiff
  refine ⟨hsN, fun n => ?_⟩
  obtain ⟨C,C0,hC⟩ := h n
  have tauPos : 0 < tau := zero_lt_one.trans_le tau_at_least_one
  refine ⟨C * tau^n, mul_nonneg C0 (pow_nonneg tauPos.le _), fun p => ?_⟩
  let q := radianParameterScale tau p
  let s := W p.2
  let t := W q.2
  let u := tau*s/t
  let L := radianParameterScale u
  let G (z : P) := uncurry r (q + radianParameterScale t z)
  have hG : ContDiff ℝ ∞ G := hs.comp (contDiff_const.add (radianParameterScale t).contDiff)
  have ht : 0 < t := radian_frequency_weight_pos q.2
  have hs_le_t : s ≤ t := by
    change 1 + ‖p.2‖ ≤ 1 + ‖tau • p.2‖
    rw [norm_smul, Real.norm_of_nonneg tauPos.le]
    exact add_le_add_left (le_mul_of_one_le_left (norm_nonneg _) tau_at_least_one) 1
  have hu : 0 ≤ u := div_nonneg (mul_nonneg tauPos.le (radian_frequency_weight_pos p.2).le) ht.le
  have hu_le : u ≤ tau := (div_le_iff₀ ht).mpr (mul_le_mul_of_nonneg_left hs_le_t tauPos.le)
  have hL : ‖L‖ ≤ tau := (norm_radian_parameter_scale_le u).trans
    (by rw [Real.norm_of_nonneg hu]; exact max_le tau_at_least_one hu_le)
  have hEq : (fun z => uncurry (normalizedWeylSymbol r) (p + radianParameterScale s z)) = G ∘ L := by
    funext z
    change uncurry r (radianParameterScale tau (p + radianParameterScale s z)) =
      uncurry r (q + radianParameterScale t (L z))
    congr 1
    apply Prod.ext
    · rfl
    · change tau • (p.2 + s • z.2) = tau • p.2 + t • (u • z.2)
      rw [smul_add, smul_smul, smul_smul]
      have he : t * u = tau * s := by dsimp [u]; field_simp [ht.ne']
      rw [he]
  have hScaled : iteratedFDeriv ℝ n
      (fun z => uncurry (normalizedWeylSymbol r) (p + radianParameterScale s z)) 0 =
      radianScaledParameterJet (uncurry (normalizedWeylSymbol r)) n p :=
    radian_parameter_jet_affine _ hsN n p s
  rw [← hScaled, hEq,
    L.iteratedFDeriv_comp_right hG 0 (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)), map_zero]
  have hj : iteratedFDeriv ℝ n G 0 = radianScaledParameterJet (uncurry r) n q :=
    radian_parameter_jet_affine _ hs n q t
  rw [hj]
  calc
    _ ≤ ‖radianScaledParameterJet (uncurry r) n q‖ * ‖L‖^n := by
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        (radianScaledParameterJet (uncurry r) n q).norm_compContinuousLinearMap_le (fun _ => L)
    _ ≤ C * tau^n := mul_le_mul (hC q) (pow_le_pow_left₀ (norm_nonneg _) hL _) (by positivity) C0

/-- The diagonal is exactly the same full infrared symbol when the two
physical windows are flat on its base support. Its exact left correction
has the scalar order-zero scaled joint estimates in cycles. -/
theorem windowedWeyl_leftSymbol_scaled_remainder (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hθ : ∀ x ξ, β x ξ ≠ 0 → θ x = 1) :
    let r (x ξ : E) := windowedWeylLeftSymbol θ β R h x ξ - normalizedWeylSymbol β x ξ
    ContDiff ℝ ∞ (uncurry r) ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P,
      ‖radianScaledParameterJet (uncurry r) n p‖ ≤ C := by
  intro r
  let a := windowedWeylAmplitude θ β
  let J := compactRadianParameterProfile a R R h
  have rapid := compact_radian_parameter_profile_rapid_joint a R R
    (compact_radian_scaled_order_one_of_directional a R R h hAmp)
  obtain ⟨sm,b⟩ := radian_shifted_profile_remainder_scaled_jet_bounds J rapid
    (exists_radian_phased_joint_profile_shift_scaled_bound J rapid)
  have hDiag (x ξ : E) : a x x ξ = β x ξ := by
    change windowedWeylAmplitude θ β x x ξ = β x ξ
    rw [windowedWeylAmplitude_diagonal]
    by_cases hz : β x ξ = 0
    · simp [hz]
    · simp [hθ x ξ hz]
  have heq (x ξ : E) : windowedWeylLeftRadianSymbol θ β R h x ξ - β x ξ =
      radianShiftedProfileRemainder J x ξ := by
    rw [← hDiag x ξ]
    exact compact_radian_two_point_shifted_profile_identity a R R h x ξ
  have hR : r = normalizedWeylSymbol (radianShiftedProfileRemainder J) := by
    funext x ξ
    exact heq x (tau • ξ)
  rw [hR]
  exact scaled_radian_order_zero_normalize _ sm b

theorem windowedWeyl_leftSymbol_scaled_order_one (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hθ : ∀ x ξ, β x ξ ≠ 0 → θ x = 1) (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) :
    ScaledJointOrderOne (windowedWeylLeftSymbol θ β R h) := by
  let a := normalizedWeylSymbol β
  let b := windowedWeylLeftSymbol θ β R h
  let r (x ξ : E) := b x ξ - a x ξ
  obtain ⟨hr,hD⟩ := windowedWeyl_leftSymbol_scaled_remainder θ β R h hAmp hθ
  have he : b = fun x ξ => a x ξ + r x ξ := by
    funext x ξ
    change b x ξ = a x ξ + (b x ξ - a x ξ)
    ring
  rw [show windowedWeylLeftSymbol θ β R h = b from rfl, he]
  refine ⟨hβ.smooth.add hr, fun n => ?_⟩
  obtain ⟨C,C0,hC⟩ := hβ.bound n
  obtain ⟨D,D0,hDb⟩ := hD n
  refine ⟨C+D, add_nonneg C0 D0, fun p => ?_⟩
  rw [scaled_joint_add a r hβ.smooth hr]
  calc
    _ ≤ ‖radianScaledParameterJet (uncurry a) n p‖ + ‖radianScaledParameterJet (uncurry r) n p‖ :=
      norm_add_le _ _
    _ ≤ C * W p.2 + D := add_le_add (hC p) (hDb p)
    _ ≤ (C+D) * W p.2 := by
      rw [add_mul]
      exact add_le_add_left (le_mul_of_one_le_right D0 (radian_frequency_weight_one_le p.2)) _

end Burnett.V03
