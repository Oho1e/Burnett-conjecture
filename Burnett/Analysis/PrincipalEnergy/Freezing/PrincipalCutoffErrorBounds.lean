import Burnett.Analysis.PrincipalEnergy.Freezing.OrderZeroCubicPlacements
import Burnett.Analysis.PrincipalEnergy.Freezing.SummedOrderZeroJets

set_option autoImplicit false
set_option maxHeartbeats 6900000

noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview
open scoped ENNReal BigOperators Burnett.A03

private theorem integral_coefficient_three_L3_bound (c : SchwartzMap E ℂ) (u v w : E → ℂ)
    (hU : MemLp u (ENNReal.ofReal 3) volume) (hV : MemLp v (ENNReal.ofReal 3) volume)
    (hW : MemLp w (ENNReal.ofReal 3) volume) (C U V W : ℝ≥0∞)
    (hc : eLpNorm (c : E → ℂ) ⊤ volume ≤ C)
    (hu : eLpNorm u (ENNReal.ofReal 3) volume ≤ U)
    (hv : eLpNorm v (ENNReal.ofReal 3) volume ≤ V)
    (hw : eLpNorm w (ENNReal.ofReal 3) volume ≤ W) :
    Integrable (fun x => c x * u x * v x * w x) ∧
      ‖∫ x, c x * u x * v x * w x‖ₑ ≤ C * U * V * W := by
  let g (x : E) := c x * u x
  have hG : MemLp g (ENNReal.ofReal 3) volume := hU.mul' (c.memLp ⊤ volume)
  have hg : eLpNorm g (ENNReal.ofReal 3) volume ≤ C * U :=
    (eLpNorm_smul_le_mul_eLpNorm (φ := (c : E → ℂ)) (f := u) (p := ⊤)
      (q := ENNReal.ofReal 3) (r := ENNReal.ofReal 3) hU.1 c.continuous.aestronglyMeasurable).trans
      (mul_le_mul' hc hu)
  obtain ⟨hi, h⟩ := energy_integral_three_factors hG hV hW
  exact ⟨hi, h.trans (mul_le_mul' (mul_le_mul' hg hv) hw)⟩

/-- The three original cubic placements use the value and first derivative
of the commutator output. Its bounds may come from a different Schwartz
input than the two localized fields, as in the original spatial partition. -/
theorem principalVariation_cutoff_error_integral_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) (A Y X U V : ℝ≥0∞)
    (hC : ∀ a b i j k, eLpNorm (C a b i j k : E → ℂ) ⊤ volume ≤ A)
    (hz : ∀ i, eLpNorm (z i : E → ℂ) (ENNReal.ofReal 3) volume ≤ Y)
    (hdz : ∀ a i, eLpNorm (energyPartial a (z i) : E → ℂ) (ENNReal.ofReal 3) volume ≤ X)
    (hw : ∀ i, MemLp (w i) (ENNReal.ofReal 3) volume ∧ eLpNorm (w i) (ENNReal.ofReal 3) volume ≤ U)
    (hdw : ∀ a i, MemLp (actualCoordinateJet (w i) a) (ENNReal.ofReal 3) volume ∧
      eLpNorm (actualCoordinateJet (w i) a) (ENNReal.ofReal 3) volume ≤ V) :
    Integrable (principalVariationDensity (fun a b i j k => C a b i j k) z w) ∧
      ‖∫ x, principalVariationDensity (fun a b i j k => C a b i j k) z w x‖ₑ ≤
        (Fintype.card (Index × Index × J × J × J) : ℝ≥0∞) * A * (U * X ^ 2 + 2 * Y * V * X) := by
  classical
  let T := Index × Index × J × J × J
  let c (q : T) := C q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  let E₀ (q : T) (x : E) := c q x * w q.2.2.1 x * energyPartial q.1 (z q.2.2.2.1) x * energyPartial q.2.1 (z q.2.2.2.2) x
  let E₁ (q : T) (x : E) := c q x * z q.2.2.1 x * actualCoordinateJet (w q.2.2.2.1) q.1 x * energyPartial q.2.1 (z q.2.2.2.2) x
  let E₂ (q : T) (x : E) := c q x * z q.2.2.1 x * energyPartial q.1 (z q.2.2.2.1) x * actualCoordinateJet (w q.2.2.2.2) q.2.1 x
  let out (q : T) := fun x => E₀ q x + E₁ q x + E₂ q x
  have h0 (q : T) : Integrable (E₀ q) ∧ ‖∫ x, E₀ q x‖ₑ ≤ A * U * X * X :=
    integral_coefficient_three_L3_bound _ _ _ _ (hw _).1 ((energyPartial _ (z _)).memLp _ volume)
      ((energyPartial _ (z _)).memLp _ volume) A U X X (hC _ _ _ _ _) (hw _).2 (hdz _ _) (hdz _ _)
  have h1 (q : T) : Integrable (E₁ q) ∧ ‖∫ x, E₁ q x‖ₑ ≤ A * Y * V * X :=
    integral_coefficient_three_L3_bound _ _ _ _ ((z _).memLp _ volume) (hdw _ _).1
      ((energyPartial _ (z _)).memLp _ volume) A Y V X (hC _ _ _ _ _) (hz _) (hdw _ _).2 (hdz _ _)
  have h2 (q : T) : Integrable (E₂ q) ∧ ‖∫ x, E₂ q x‖ₑ ≤ A * Y * X * V :=
    integral_coefficient_three_L3_bound _ _ _ _ ((z _).memLp _ volume) ((energyPartial _ (z _)).memLp _ volume)
      (hdw _ _).1 A Y X V (hC _ _ _ _ _) (hz _) (hdz _ _) (hdw _ _).2
  have hI (q : T) : Integrable (out q) := ((h0 q).1.add (h1 q).1).add (h2 q).1
  have hEq : principalVariationDensity (fun a b i j k => C a b i j k) z w = fun x => ∑ q : T, out q x := by
    funext x
    simp only [T, principalVariationDensity, Fintype.sum_prod_type, out, E₀, E₁, E₂, c, actualCoordinateJet]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  rw [hEq]
  refine ⟨integrable_finset_sum _ fun q _ => hI q, ?_⟩
  rw [integral_finset_sum Finset.univ (fun q _ => hI q)]
  refine (enorm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _q : T, A * (U * X ^ 2 + 2 * Y * V * X) := by
      apply Finset.sum_le_sum
      intro q _
      change ‖∫ x, (E₀ q + E₁ q) x + E₂ q x‖ₑ ≤ _
      have hs : (∫ x, (E₀ q + E₁ q) x) = (∫ x, E₀ q x) + (∫ x, E₁ q x) :=
        integral_add (h0 q).1 (h1 q).1
      rw [integral_add ((h0 q).1.add (h1 q).1) (h2 q).1, hs]
      exact (enorm_add_le _ _).trans ((add_le_add ((enorm_add_le _ _).trans
        (add_le_add (h0 q).2 (h1 q).2)) (h2 q).2).trans_eq (by ring))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Burnett.A03
