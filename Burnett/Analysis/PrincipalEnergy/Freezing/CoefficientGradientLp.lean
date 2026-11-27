import Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalCoefficientContraction
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ENNReal

theorem energyProduct_eLpNorm_le (p : ℝ≥0∞) (a u : SchwartzMap E ℂ) :
    eLpNorm (energyProduct a u : E → ℂ) p volume ≤
      eLpNorm (a : E → ℂ) ⊤ volume * eLpNorm (u : E → ℂ) p volume := by
  change eLpNorm (fun x => a x * u x) p volume ≤ _
  have bound := eLpNorm_le_eLpNorm_top_mul_eLpNorm (μ := volume) p (a : E → ℂ)
    u.continuous.aestronglyMeasurable (fun v w : ℂ => v*w) 1
    (Filter.Eventually.of_forall fun x => by
      simp only [nnnorm_mul, one_mul]
      exact le_rfl)
  simpa only [ENNReal.coe_one, one_mul] using bound

/-- The coefficient product rule in the actual derivative and Lebesgue norms. -/
theorem coefficientProduct_partial_L3 (a : Index) (C z : SchwartzMap E ℂ) :
    eLpNorm (energyPartial a (energyProduct C z) : E → ℂ) 3 volume ≤
      eLpNorm (C : E → ℂ) ⊤ volume * eLpNorm (energyPartial a z : E → ℂ) 3 volume +
      eLpNorm (energyPartial a C : E → ℂ) ⊤ volume * eLpNorm (z : E → ℂ) 3 volume := by
  let A := energyProduct C (energyPartial a z)
  let B := energyProduct (energyPartial a C) z
  have eq : (energyPartial a (energyProduct C z) : E → ℂ) = (A : E → ℂ) + B := by
    funext x
    simp only [A, B, energyPartial_product, Pi.add_apply, energyProduct_apply]
    exact add_comm _ _
  rw [eq]
  exact (eLpNorm_add_le A.continuous.aestronglyMeasurable B.continuous.aestronglyMeasurable
      (by norm_num)).trans (add_le_add (energyProduct_eLpNorm_le 3 C (energyPartial a z))
      (energyProduct_eLpNorm_le 3 (energyPartial a C) z))

/-- The full finite coefficient contraction uses the same field in its value
and derivative terms. The sum is over its original undifferentiated index. -/
theorem principalCoefficientContraction_partial_L3 {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (p : (Index × J) × (Index × J)) (a : Index) :
    let c (i : J) := C p.1.1 p.2.1 i p.1.2 p.2.2
    eLpNorm (energyPartial a (principalCoefficientContraction C z p) : E → ℂ) 3 volume ≤
      ∑ i, (eLpNorm (c i : E → ℂ) ⊤ volume * eLpNorm (energyPartial a (z i) : E → ℂ) 3 volume +
        eLpNorm (energyPartial a (c i) : E → ℂ) ⊤ volume * eLpNorm (z i : E → ℂ) 3 volume) := by
  intro c
  let W (i : J) := energyPartial a (energyProduct (c i) (z i))
  let eval : SchwartzMap E ℂ →+ (E → ℂ) :=
    {toFun := fun f => f, map_zero' := rfl, map_add' := fun _ _ => rfl}
  have eqS : energyPartial a (principalCoefficientContraction C z p) = ∑ i, W i := by
    simp only [principalCoefficientContraction, energyPartial, map_sum, W, c]
  have eq : (energyPartial a (principalCoefficientContraction C z p) : E → ℂ) =
      ∑ i, (W i : E → ℂ) := by
    rw [eqS]
    exact map_sum eval _ _
  rw [eq]
  refine (eLpNorm_sum_le (f := fun i => (W i : E → ℂ))
      (fun i _ => (W i).continuous.aestronglyMeasurable) (by norm_num)).trans ?_
  exact Finset.sum_le_sum (fun i _ => coefficientProduct_partial_L3 a (c i) (z i))

end Burnett.A02.FrequencySplit
