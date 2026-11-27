import Burnett.Analysis.PrincipalEnergy.Freezing.CubicEnergyLpContinuity
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalPoincare
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedEnergyFields

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview
open scoped BigOperators ENNReal Burnett.A03

private theorem order_zero_term_sum_bound {ι : Type*} [Fintype ι] (g : ι → ℂ)
    (B : ℝ≥0∞) (h : ∀ i, ‖g i‖ₑ ≤ B) :
    ‖∑ i, g i‖ₑ ≤ (Fintype.card ι : ℝ≥0∞) * B := by
  calc
    _ ≤ ∑ i, ‖g i‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum fun i _ => h i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The three actual principal energy placements obey the order-zero residual
scale. The first derivative norm of the test may have a term proportional
to the undifferentiated field, which patch Poincaré absorbs into the factor. -/
theorem principal_cubic_order_zero_placement_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (w : PatchFieldLpJet J) (c : E) (R ℓ : ℝ) (hR : 0 < R) (hℓ : 0 < ℓ)
    (hz : tsupport (fieldValueArray z) ⊆ ball c (R * ℓ))
    (C₀ A B D : ℝ≥0∞)
    (hC₀ : ∀ a b i j k, eLpNorm (C a b i j k : E → ℂ) ⊤ volume ≤ C₀) :
    let p := ENNReal.ofReal 3
    let X := euclideanFieldGradientNorm z
    let Y := eLpNorm (fieldValueArray z) p volume
    (∀ i, eLpNorm (w.1 i : E → ℂ) p volume ≤ A * Y) →
    (∀ j : Index × J, eLpNorm (w.2 j : E → ℂ) p volume ≤ B * X + D * Y) →
    ‖principalCubicLpFunctional C z w‖ₑ ≤
      (Fintype.card ((Index × J) × (Index × J)) : ℝ≥0∞) * Fintype.card J * C₀ *
        (A + 2 * (B + D * ENNReal.ofReal (3 * (R * ℓ)))) * Y * X ^ 2 := by
  classical
  intro p X Y hv hd
  let T := Index × J
  let S := T × T
  let N : ℝ≥0∞ := Fintype.card S
  let M : ℝ≥0∞ := Fintype.card J
  let r := ENNReal.ofReal (3 * (R * ℓ))
  let U (q : T) := energyPartial q.1 (z q.2)
  let L (q : S) := principalCoefficientContraction C z q
  let c₀ (q : S) (i : J) := C q.1.1 q.2.1 i q.1.2 q.2.2
  let V (q : S) (i : J) := patchLpPair (energyProduct (c₀ q i)
    (energyProduct (U q.1) (U q.2))) (w.1 i)
  let E₁ (q : S) := patchLpPair (energyProduct (L q) (U q.2)) (w.2 q.1)
  let E₂ (q : S) := patchLpPair (energyProduct (L q) (U q.1)) (w.2 q.2)
  have poincare : Y ≤ r * X :=
    euclidean_field_local_poincare_eLpNorm z c (R * ℓ) (mul_pos hR hℓ) hz
  have dBound (q : T) : eLpNorm (w.2 q : E → ℂ) p volume ≤ (B + D * r) * X := by
    refine (hd q).trans ?_
    rw [add_mul, mul_assoc]
    exact add_le_add le_rfl (mul_le_mul_left' poincare _)
  obtain ⟨_, hU, _⟩ := separated_field_component_L3_bounds z
  have vTerm (q : S) (i : J) : ‖V q i‖ₑ ≤ C₀ * (A * Y) * X * X := by
    let v := w.1 i
    let g (x : E) := c₀ q i x * v x
    have hV : MemLp (v : E → ℂ) p volume := Lp.memLp v
    have hG : MemLp g p volume := hV.mul' ((c₀ q i).memLp ⊤ volume)
    have hGN : eLpNorm g p volume ≤ eLpNorm (c₀ q i : E → ℂ) ⊤ volume * eLpNorm (v : E → ℂ) p volume :=
      eLpNorm_smul_le_mul_eLpNorm (φ := (c₀ q i : E → ℂ)) (f := (v : E → ℂ)) (p := ⊤) (q := p) (r := p)
        hV.1 (c₀ q i).continuous.aestronglyMeasurable
    have eq : V q i = ∫ x, g x * U q.1 x * U q.2 x := by
      change (∫ x, v x * energyProduct (c₀ q i) (energyProduct (U q.1) (U q.2)) x) = _
      congr 1
      funext x
      simp only [energyProduct_apply, g]
      ring
    rw [eq]
    refine (energy_integral_three_factors hG ((U q.1).memLp p volume) ((U q.2).memLp p volume)).2.trans ?_
    exact mul_le_mul' (mul_le_mul' (hGN.trans (mul_le_mul' (hC₀ _ _ _ _ _) (hv i))) (hU q.1)) (hU q.2)
  have dTerm (q : S) (t s : T) :
      ‖patchLpPair (energyProduct (L q) (U t)) (w.2 s)‖ₑ ≤
        M * (C₀ * Y) * X * ((B + D * r) * X) := by
    let v := w.2 s
    have eq : patchLpPair (energyProduct (L q) (U t)) v = ∫ x, L q x * U t x * v x := by
      change (∫ x, v x * energyProduct (L q) (U t) x) = _
      congr 1
      funext x
      simp only [energyProduct_apply]
      ring
    change ‖patchLpPair (energyProduct (L q) (U t)) v‖ₑ ≤ _
    rw [eq]
    have Lbound := (principalCoefficientContraction_value_and_gradient_L3_bound C z C₀ ⊤ hC₀
      (fun _ _ _ _ _ _ => le_top) q).1
    refine (energy_integral_three_factors ((L q).memLp p volume) ((U t).memLp p volume) (Lp.memLp v)).2.trans ?_
    exact mul_le_mul' (mul_le_mul' Lbound (hU t)) (dBound s)
  have expression : principalCubicLpFunctional C z w =
      (∑ q : S, ∑ i : J, V q i) + ∑ q : S, (E₁ q + E₂ q) := by
    dsimp only [V, E₁, E₂, c₀, U, L]
    simp only [principalCubicLpFunctional, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply]
    rfl
  rw [expression]
  have totalV : ‖∑ q : S, ∑ i : J, V q i‖ₑ ≤ N * (M * (C₀ * (A * Y) * X * X)) :=
    order_zero_term_sum_bound _ _ fun q => order_zero_term_sum_bound _ _ (vTerm q)
  have totalD : ‖∑ q : S, (E₁ q + E₂ q)‖ₑ ≤ N *
      (M * (C₀ * Y) * X * ((B + D * r) * X) + M * (C₀ * Y) * X * ((B + D * r) * X)) :=
    order_zero_term_sum_bound _ _ fun q =>
      (enorm_add_le _ _).trans (add_le_add (dTerm q q.2 q.1) (dTerm q q.1 q.2))
  refine (enorm_add_le _ _).trans ((add_le_add totalV totalD).trans_eq ?_)
  change _ = N * M * C₀ * (A + 2 * (B + D * r)) * Y * X ^ 2
  ring

end Burnett.A03
