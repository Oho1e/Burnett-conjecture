import Burnett.Analysis.PrincipalEnergy.Freezing.PatchLpDuality
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal BigOperators Burnett.A03

/-- The Fourier mode outputs and their actual first derivatives converge
absolutely in (L^3), and the limits satisfy the weak derivative identity. -/
theorem exists_summable_separated_mode_jets {I : Type*}
    (f : I → Fin 2 → SchwartzMap E ℂ) (b : I → Fin 2 → E → ℝ) (D : I → Fin 2 → ℝ)
    (hb : ∀ k j, ContDiffOn ℝ ∞ (b k j) {ξ | ξ ≠ 0})
    (hom : ∀ k j (t : ℝ), 0 < t → ∀ ξ, b k j (t • ξ) = t * b k j ξ)
    (nonneg : ∀ k j, 0 ≤ D k j)
    (jets : ∀ k j n, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (b k j) ξ‖ ≤ D k j)
    (weight : ∀ r : ℕ, r ≤ 2 →
      Summable (fun k : I => ∑ j : Fin 2, D k j * schwartzProfileJetLInfinity r (f k j)))
    (u : SchwartzMap E ℂ) :
    ∃ h : ∀ k j, SeparatedModeLpJet (f k j) (b k j) u,
      let value (k : I) := ∑ j : Fin 2, (h k j).valueLp
      let coordinate (a : Index) (k : I) := ∑ j : Fin 2, (h k j).coordinateLp a
      Summable (fun k : I => ∑ j : Fin 2, ‖(h k j).valueLp‖) ∧
        (∀ a : Index, Summable (fun k : I => ∑ j : Fin 2, ‖(h k j).coordinateLp a‖)) ∧
        HasSum value (∑' k, value k) ∧
        ∀ a : Index, HasSum (coordinate a) (∑' k, coordinate a k) ∧
          HasWeakCoordinateDerivative3 (∑' k, value k) (∑' k, coordinate a k) a := by
  classical
  obtain ⟨K, _, bound⟩ := exists_separated_mode_Lp_jet_bound
  choose h estimate using fun (k : I) (j : Fin 2) =>
    bound (b k j) (hb k j) (hom k j) (D k j) (nonneg k j) (jets k j) (f k j) u
  let X := (energyGradientNorm u).toReal
  let Y := (eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume).toReal
  let Xₐ (a : Index) := (energyGradientNorm (energyPartial a u)).toReal
  let Yₐ (a : Index) := (eLpNorm (energyPartial a u : E → ℂ) (ENNReal.ofReal 3) volume).toReal
  let W (r : ℕ) (k : I) := ∑ j : Fin 2, D k j * schwartzProfileJetLInfinity r (f k j)
  let value (k : I) := ∑ j : Fin 2, (h k j).valueLp
  let coordinate (a : Index) (k : I) := ∑ j : Fin 2, (h k j).coordinateLp a
  have valueMajor : Summable (fun k => K * (X * W 0 k + Y * W 1 k)) :=
    (((weight 0 (by decide)).mul_left X).add ((weight 1 (by decide)).mul_left Y)).mul_left K
  have eachValue (k : I) (j : Fin 2) : ‖(h k j).valueLp‖ ≤ K *
      (X * (D k j * schwartzProfileJetLInfinity 0 (f k j)) +
        Y * (D k j * schwartzProfileJetLInfinity 1 (f k j))) := by
    refine (estimate k j).1.trans_eq ?_
    change K * D k j * (schwartzProfileJetLInfinity 0 (f k j) * X +
      schwartzProfileJetLInfinity 1 (f k j) * Y) = _
    ring
  have valueAbs : Summable (fun k : I => ∑ j : Fin 2, ‖(h k j).valueLp‖) := by
    apply Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) _ valueMajor
    intro k
    refine (Finset.sum_le_sum fun j _ => eachValue k j).trans_eq ?_
    simp only [W, Finset.sum_add_distrib, ← Finset.mul_sum]
  have coordinateMajor (a : Index) :
      Summable (fun k => K * (Xₐ a * W 0 k + (Yₐ a + X) * W 1 k + Y * W 2 k)) :=
    ((((weight 0 (by decide)).mul_left (Xₐ a)).add ((weight 1 (by decide)).mul_left (Yₐ a + X))).add
      ((weight 2 (by decide)).mul_left Y)).mul_left K
  have eachCoordinate (a : Index) (k : I) (j : Fin 2) : ‖(h k j).coordinateLp a‖ ≤ K *
      (Xₐ a * (D k j * schwartzProfileJetLInfinity 0 (f k j)) +
        (Yₐ a + X) * (D k j * schwartzProfileJetLInfinity 1 (f k j)) +
          Y * (D k j * schwartzProfileJetLInfinity 2 (f k j))) := by
    refine ((estimate k j).2 a).trans_eq ?_
    change K * D k j * (schwartzProfileJetLInfinity 0 (f k j) * Xₐ a +
      schwartzProfileJetLInfinity 1 (f k j) * (Yₐ a + X) + schwartzProfileJetLInfinity 2 (f k j) * Y) = _
    ring
  have coordinateAbs (a : Index) : Summable (fun k : I => ∑ j : Fin 2, ‖(h k j).coordinateLp a‖) := by
    apply Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) _ (coordinateMajor a)
    intro k
    refine (Finset.sum_le_sum fun j _ => eachCoordinate a k j).trans_eq ?_
    simp only [W, Finset.sum_add_distrib, ← Finset.mul_sum]
  have valueSum : HasSum value (∑' k, value k) :=
    (Summable.of_norm_bounded (f := value) valueAbs (fun _ => norm_sum_le _ _)).hasSum
  have coordinateSum (a : Index) : HasSum (coordinate a) (∑' k, coordinate a k) :=
    (Summable.of_norm_bounded (f := coordinate a) (coordinateAbs a) (fun _ => norm_sum_le _ _)).hasSum
  have modeWeak (a : Index) (k : I) : HasWeakCoordinateDerivative3 (value k) (coordinate a k) a :=
    weak_coordinate_derivative_finset_sum Finset.univ (fun j => (h k j).valueLp)
      (fun j => (h k j).coordinateLp a) a
      (fun j _ => separated_mode_Lp_jet_is_weak_derivative (hb k j) (hom k j) (h k j) a)
  exact ⟨h, valueAbs, coordinateAbs, valueSum, fun a =>
    ⟨coordinateSum a, weak_coordinate_derivative_hasSum value (coordinate a) _ _ a
      valueSum (coordinateSum a) (modeWeak a)⟩⟩

end Burnett.A03
