import Burnett.Analysis.PrincipalEnergy.Freezing.EnergyHolder
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearIBP
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open scoped BigOperators ENNReal

/-- The integral of one fixed smooth coefficient and three scalar field slots. -/
def weightedCubicIntegral (c u v w : SchwartzMap E ℂ) : ℂ := ∫ x, c x * u x * v x * w x

private theorem weighted_cubic_integrable (c u v w : SchwartzMap E ℂ) :
    Integrable (fun x => c x * u x * v x * w x) volume := by
  simpa only [energyProduct_apply] using (energyProduct (energyProduct (energyProduct c u) v) w).integrable

private theorem weighted_cubic_integral_ibp (a : Index) (c u v w : SchwartzMap E ℂ) :
    weightedCubicIntegral c u v (energyPartial a w) =
      -(weightedCubicIntegral (energyPartial a c) u v w + weightedCubicIntegral c (energyPartial a u) v w +
        weightedCubicIntegral c u (energyPartial a v) w) := by
  let F := energyProduct (energyProduct c u) v
  have e₁ := (energyProduct (energyPartial a F) w).integrable (μ := (volume : Measure E))
  have e₂ := (energyProduct F (energyPartial a w)).integrable (μ := (volume : Measure E))
  have e₃ := (energyProduct F w).integrable (μ := (volume : Measure E))
  simp only [energyPartial] at e₁ e₂ e₃
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure E)) (f := (F : E → ℂ)) (g := (w : E → ℂ)) (v := EuclideanSpace.single a 1)
    e₁ e₂ e₃ F.differentiable w.differentiable
  change (∫ x, F x * energyPartial a w x) = -(∫ x, energyPartial a F x * w x) at h
  have dx (x : E) : energyPartial a F x * w x =
      (energyPartial a c x * u x * v x * w x + c x * energyPartial a u x * v x * w x) +
        c x * u x * energyPartial a v x * w x := by
    simp only [F, energyPartial_product, energyProduct_apply]
    ring
  simp_rw [dx] at h
  have h₁ := weighted_cubic_integrable (energyPartial a c) u v w
  have h₂ := weighted_cubic_integrable c (energyPartial a u) v w
  have h₃ := weighted_cubic_integrable c u (energyPartial a v) w
  have hIntegralSum : (∫ x, energyPartial a c x * u x * v x * w x + c x * energyPartial a u x * v x * w x +
        c x * u x * energyPartial a v x * w x) =
      weightedCubicIntegral (energyPartial a c) u v w + weightedCubicIntegral c (energyPartial a u) v w +
        weightedCubicIntegral c u (energyPartial a v) w := by
    unfold weightedCubicIntegral
    calc
      _ = (∫ x, energyPartial a c x * u x * v x * w x + c x * energyPartial a u x * v x * w x) +
          ∫ x, c x * u x * energyPartial a v x * w x := integral_add (h₁.add h₂) h₃
      _ = _ := congrArg (fun z => z + ∫ x, c x * u x * energyPartial a v x * w x) (integral_add h₁ h₂)
  rw [hIntegralSum] at h
  simpa only [F, energyProduct_apply, weightedCubicIntegral] using h

private abbrev fieldL3 (u : SchwartzMap E ℂ) : ℝ≥0∞ := eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume
private abbrev coeffLInf (c : SchwartzMap E ℂ) : ℝ≥0∞ := eLpNorm (c : E → ℂ) ⊤ volume

private theorem weighted_cubic_bound (c u v w : SchwartzMap E ℂ) :
    ‖weightedCubicIntegral c u v w‖ₑ ≤ coeffLInf c * fieldL3 u * fieldL3 v * fieldL3 w := by
  let p := ENNReal.ofReal 3
  let cu := energyProduct c u
  have mulBound : fieldL3 cu ≤ coeffLInf c * fieldL3 u :=
    eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm p (u.memLp p volume).aestronglyMeasurable (c : E → ℂ)
  have h := (energy_integral_three_factors (cu.memLp p volume) (v.memLp p volume) (w.memLp p volume)).2
  have h' : ‖weightedCubicIntegral c u v w‖ₑ ≤ fieldL3 cu * fieldL3 v * fieldL3 w := by
    simpa only [weightedCubicIntegral, cu, energyProduct_apply] using h
  exact h'.trans (mul_le_mul_right' (mul_le_mul_right' mulBound _) _)

private theorem weighted_cubic_bound_of_component_limits (c u v w : SchwartzMap E ℂ)
    {D X Y Z : ℝ≥0∞} (hc : coeffLInf c ≤ D) (hu : fieldL3 u ≤ X) (hv : fieldL3 v ≤ Y) (hw : fieldL3 w ≤ Z) :
    ‖weightedCubicIntegral c u v w‖ₑ ≤ D * X * Y * Z :=
  (weighted_cubic_bound c u v w).trans (mul_le_mul' (mul_le_mul' (mul_le_mul' hc hu) hv) hw)

/-- The diagonal lower-order polynomial contains all monomials with no
field derivative or one field derivative. The differentiated component is
the third slot of the ordered monomial. -/
def lowerCubicPolynomial {J : Type} [Fintype J]
    (C₀ : J × J × J → SchwartzMap E ℂ) (C₁ : Index × J × J × J → SchwartzMap E ℂ)
    (z : J → SchwartzMap E ℂ) : ℝ :=
  ((∑ i : J × J × J, weightedCubicIntegral (C₀ i) (z i.1) (z i.2.1) (z i.2.2)) +
    ∑ i : Index × J × J × J, weightedCubicIntegral (C₁ i) (z i.2.1) (z i.2.2.1)
      (energyPartial i.1 (z i.2.2.2))).re

private def lowerValueTest (c u v w U V W : SchwartzMap E ℂ) : ℂ :=
  weightedCubicIntegral c U v w + weightedCubicIntegral c u V w + weightedCubicIntegral c u v W

private def lowerDerivativeTest (a : Index) (c u v w U V W : SchwartzMap E ℂ) : ℂ :=
  lowerValueTest c u v (energyPartial a w) U V (energyPartial a W)

/-- Variation of the general lower-order polynomial in all three test
placements. The test derivative is subsequently transferred by IBP. -/
def realLowerCubicVariation {J : Type} [Fintype J]
    (C₀ : J × J × J → SchwartzMap E ℂ) (C₁ : Index × J × J × J → SchwartzMap E ℂ)
    (z w : J → SchwartzMap E ℂ) : ℝ :=
  ((∑ i : J × J × J, lowerValueTest (C₀ i) (z i.1) (z i.2.1) (z i.2.2) (w i.1) (w i.2.1) (w i.2.2)) +
    ∑ i : Index × J × J × J, lowerDerivativeTest i.1 (C₁ i) (z i.2.1) (z i.2.2.1) (z i.2.2.2)
      (w i.2.1) (w i.2.2.1) (w i.2.2.2)).re

private theorem lower_value_test_bound (c u v w U V W : SchwartzMap E ℂ) {D Y Z : ℝ≥0∞}
    (hc : coeffLInf c ≤ D) (hu : fieldL3 u ≤ Y) (hv : fieldL3 v ≤ Y) (hw : fieldL3 w ≤ Y)
    (hU : fieldL3 U ≤ Z) (hV : fieldL3 V ≤ Z) (hW : fieldL3 W ≤ Z) :
    ‖lowerValueTest c u v w U V W‖ₑ ≤ 3 * D * Y ^ 2 * Z := by
  unfold lowerValueTest
  refine ((enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)).trans ?_
  refine (add_le_add (add_le_add (weighted_cubic_bound_of_component_limits c U v w hc hU hv hw)
    (weighted_cubic_bound_of_component_limits c u V w hc hu hV hw))
    (weighted_cubic_bound_of_component_limits c u v W hc hu hv hW)).trans_eq ?_
  ring

private theorem lower_derivative_test_bound (a : Index) (c u v w U V W : SchwartzMap E ℂ) {D X Y Z : ℝ≥0∞}
    (hc : coeffLInf c ≤ D) (hdc : coeffLInf (energyPartial a c) ≤ D)
    (hu : fieldL3 u ≤ Y) (hv : fieldL3 v ≤ Y)
    (hdu : fieldL3 (energyPartial a u) ≤ X) (hdv : fieldL3 (energyPartial a v) ≤ X)
    (hdw : fieldL3 (energyPartial a w) ≤ X)
    (hU : fieldL3 U ≤ Z) (hV : fieldL3 V ≤ Z) (hW : fieldL3 W ≤ Z) :
    ‖lowerDerivativeTest a c u v w U V W‖ₑ ≤ 4 * D * Y * X * Z + D * Y ^ 2 * Z := by
  unfold lowerDerivativeTest lowerValueTest
  rw [weighted_cubic_integral_ibp a c u v W]
  refine (enorm_add_le _ _).trans ?_
  rw [enorm_neg]
  have pos := (enorm_add_le _ _).trans (add_le_add
    (weighted_cubic_bound_of_component_limits c U v (energyPartial a w) hc hU hv hdw)
    (weighted_cubic_bound_of_component_limits c u V (energyPartial a w) hc hu hV hdw))
  have neg := (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans (add_le_add
    (weighted_cubic_bound_of_component_limits (energyPartial a c) u v W hdc hu hv hW)
    (weighted_cubic_bound_of_component_limits c (energyPartial a u) v W hc hdu hv hW)))
    (weighted_cubic_bound_of_component_limits c u (energyPartial a v) W hc hu hdv hW))
  exact (add_le_add pos neg).trans_eq (by ring)

/-- Once the general lower-order action is integrated by parts, it uses
only the L³ value of the test and the value and first derivatives of the field. -/
theorem exists_general_lower_cubic_variation_bound {J : Type} [Fintype J]
    (C₀ : J × J × J → SchwartzMap E ℂ) (C₁ : Index × J × J × J → SchwartzMap E ℂ) :
    ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ (z w : J → SchwartzMap E ℂ) (X Y Z : ℝ≥0∞),
      (∀ i, fieldL3 (z i) ≤ Y) → (∀ a i, fieldL3 (energyPartial a (z i)) ≤ X) →
      (∀ i, fieldL3 (w i) ≤ Z) →
      ‖realLowerCubicVariation C₀ C₁ z w‖ₑ ≤ D * (Y ^ 2 + Y * X) * Z := by
  classical
  let I := J × J × J
  let K := Index × J × J × J
  let U := ∑ i : I, coeffLInf (C₀ i)
  let V := ∑ i : K, coeffLInf (C₁ i)
  let W := ∑ i : K, coeffLInf (energyPartial i.1 (C₁ i))
  let D := 3 * U + 5 * (V + W)
  have finite (f : SchwartzMap E ℂ) : coeffLInf f < ⊤ := (f.memLp ⊤ volume).2
  have uFin : U < ⊤ := ENNReal.sum_lt_top.mpr fun i _ => finite (C₀ i)
  have vFin : V < ⊤ := ENNReal.sum_lt_top.mpr fun i _ => finite (C₁ i)
  have wFin : W < ⊤ := ENNReal.sum_lt_top.mpr fun i _ => finite (energyPartial i.1 (C₁ i))
  refine ⟨D, ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) uFin,
    ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨vFin,wFin⟩)⟩, ?_⟩
  intro z w X Y Z hVal hDer hTest
  let f (i : I) := lowerValueTest (C₀ i) (z i.1) (z i.2.1) (z i.2.2) (w i.1) (w i.2.1) (w i.2.2)
  let g (i : K) := lowerDerivativeTest i.1 (C₁ i) (z i.2.1) (z i.2.2.1) (z i.2.2.2)
    (w i.2.1) (w i.2.2.1) (w i.2.2.2)
  have fBound (i : I) : ‖f i‖ₑ ≤ coeffLInf (C₀ i) * (3 * Y ^ 2 * Z) := by
    exact (lower_value_test_bound _ _ _ _ _ _ _ le_rfl (hVal _) (hVal _) (hVal _) (hTest _) (hTest _) (hTest _)).trans_eq (by ring)
  have gBound (i : K) : ‖g i‖ₑ ≤ (coeffLInf (C₁ i) + coeffLInf (energyPartial i.1 (C₁ i))) *
      ((4 * Y * X + Y ^ 2) * Z) := by
    exact (lower_derivative_test_bound _ _ _ _ _ _ _ _ (le_self_add) (le_add_self)
      (hVal _) (hVal _) (hDer _ _) (hDer _ _) (hDer _ _) (hTest _) (hTest _) (hTest _)).trans_eq (by ring)
  have fSum : ‖∑ i, f i‖ₑ ≤ U * (3 * Y ^ 2 * Z) := by
    refine (enorm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => fBound i).trans_eq ?_)
    rw [← Finset.sum_mul]
  have gSum : ‖∑ i, g i‖ₑ ≤ (V + W) * ((4 * Y * X + Y ^ 2) * Z) := by
    refine (enorm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => gBound i).trans_eq ?_)
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
  have re : ‖((∑ i, f i) + ∑ i, g i).re‖ₑ ≤ ‖(∑ i, f i) + ∑ i, g i‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)
  change ‖((∑ i, f i) + ∑ i, g i).re‖ₑ ≤ _
  refine (re.trans ((enorm_add_le _ _).trans (add_le_add fSum gSum))).trans ?_
  have hf : 3 * Y ^ 2 * Z ≤ 3 * (Y ^ 2 + Y * X) * Z := by gcongr; exact le_self_add
  have hg : (4 * Y * X + Y ^ 2) * Z ≤ 5 * (Y ^ 2 + Y * X) * Z := by
    have ha : 4 * Y * X ≤ 4 * (Y ^ 2 + Y * X) := by rw [mul_assoc]; gcongr; exact le_add_self
    have hb : Y ^ 2 ≤ Y ^ 2 + Y * X := le_self_add
    exact mul_le_mul_right' ((add_le_add ha hb).trans_eq (by ring)) Z
  exact (add_le_add (mul_le_mul_left' hf U) (mul_le_mul_left' hg (V + W))).trans_eq (by dsimp only [D]; ring)

end Burnett.A03
