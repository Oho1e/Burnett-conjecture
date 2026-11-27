import Burnett.Analysis.PrincipalEnergy.Freezing.CoefficientGradientLp
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSkewCoordinateL3
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedSkewCommutatorL32

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace Burnett.A02.FrequencySplit

open MeasureTheory Burnett.RicciSymbol Burnett.A02.FieldAndCoefficientReview
open scoped BigOperators ENNReal

/-- Scalar bounds use the actual Euclidean value and coordinate derivative arrays. -/
theorem separated_field_component_L3_bounds {J : Type} [Fintype J]
    (z : J → SchwartzMap E ℂ) :
    let X := euclideanFieldGradientNorm z
    let Y := eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume
    (∀ i, eLpNorm (z i : E → ℂ) (ENNReal.ofReal 3) volume ≤ Y) ∧
    (∀ k : Index × J, eLpNorm (energyPartial k.1 (z k.2) : E → ℂ) (ENNReal.ofReal 3) volume ≤ X) ∧
    (∀ i, energyGradientNorm (z i) ≤ (Fintype.card Index : ℝ≥0∞) * X) := by
  intro X Y
  have hvalue (i : J) : eLpNorm (z i : E → ℂ) (ENNReal.ofReal 3) volume ≤ Y :=
    eLpNorm_mono (f := (z i : E → ℂ)) (g := fieldValueArray z)
      (fun x => PiLp.norm_apply_le (fieldValueArray z x) i)
  have hpartial (k : Index × J) :
      eLpNorm (energyPartial k.1 (z k.2) : E → ℂ) (ENNReal.ofReal 3) volume ≤ X :=
    eLpNorm_mono (f := (energyPartial k.1 (z k.2) : E → ℂ)) (g := euclideanFieldGradient z)
      (fun x => PiLp.norm_apply_le (euclideanFieldGradient z x) k)
  refine ⟨hvalue, hpartial, fun i => (energyGradientNorm_le_coordinate_L3_sum (z i)).trans ?_⟩
  calc
    _ ≤ ∑ _a : Index, X := Finset.sum_le_sum (fun a _ => hpartial (a, i))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Bounds for the actual coefficient contraction with the same field. -/
theorem principalCoefficientContraction_value_and_gradient_L3_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (C₀ C₁ : ℝ≥0∞)
    (hC₀ : ∀ a d i j k, eLpNorm (C a d i j k : E → ℂ) ⊤ volume ≤ C₀)
    (hC₁ : ∀ a d i j k l, eLpNorm (energyPartial l (C a d i j k) : E → ℂ) ⊤ volume ≤ C₁)
    (p : (Index × J) × (Index × J)) :
    let X := euclideanFieldGradientNorm z
    let Y := eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume
    let R := principalCoefficientContraction C z p
    eLpNorm (R : E → ℂ) (ENNReal.ofReal 3) volume ≤ (Fintype.card J : ℝ≥0∞) * (C₀ * Y) ∧
    energyGradientNorm R ≤ ((Fintype.card Index : ℝ≥0∞) * Fintype.card J) * (C₀ * X + C₁ * Y) := by
  intro X Y R
  let c (i : J) := C p.1.1 p.2.1 i p.1.2 p.2.2
  let P := ENNReal.ofReal 3
  obtain ⟨hvalue, hpartial, _⟩ := separated_field_component_L3_bounds z
  have top (i : J) : eLpNorm (c i : E → ℂ) ⊤ volume ≤ C₀ := hC₀ _ _ _ _ _
  have derivativeTop (a : Index) (i : J) :
      eLpNorm (energyPartial a (c i) : E → ℂ) ⊤ volume ≤ C₁ := hC₁ _ _ _ _ _ a
  constructor
  · have eq : (R : E → ℂ) = ∑ i, (energyProduct (c i) (z i) : E → ℂ) := by
      funext x
      rw [Finset.sum_apply, principalCoefficientContraction_apply]
      rfl
    rw [eq]
    refine (eLpNorm_sum_le (f := fun i => (energyProduct (c i) (z i) : E → ℂ))
      (fun i _ => (energyProduct (c i) (z i)).continuous.aestronglyMeasurable)
      (by norm_num [P])).trans ?_
    calc
      _ ≤ ∑ _i : J, C₀ * Y := Finset.sum_le_sum (fun i _ =>
        (energyProduct_eLpNorm_le P (c i) (z i)).trans (mul_le_mul' (top i) (hvalue i)))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · refine (energyGradientNorm_le_coordinate_L3_sum R).trans ?_
    calc
      _ ≤ ∑ _a : Index, (Fintype.card J : ℝ≥0∞) * (C₀ * X + C₁ * Y) := by
        apply Finset.sum_le_sum
        intro a _
        have hc := principalCoefficientContraction_partial_L3 C z p a
        have hcd : eLpNorm (energyPartial a R : E → ℂ) P volume ≤
            ∑ i, (eLpNorm (c i : E → ℂ) ⊤ volume * eLpNorm (energyPartial a (z i) : E → ℂ) P volume +
              eLpNorm (energyPartial a (c i) : E → ℂ) ⊤ volume * eLpNorm (z i : E → ℂ) P volume) := by
          simpa only [P, ENNReal.ofReal_ofNat] using hc
        refine hcd.trans ?_
        calc
          _ ≤ ∑ _i : J, (C₀ * X + C₁ * Y) := Finset.sum_le_sum (fun i _ =>
            add_le_add (mul_le_mul' (top i) (hpartial (a, i))) (mul_le_mul' (derivativeTop a i) (hvalue i)))
          _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

end Burnett.A02.FrequencySplit
