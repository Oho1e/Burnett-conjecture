import Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalFreezingWeakJets
import Burnett.Analysis.PrincipalEnergy.Freezing.OrderZeroCubicPlacements
import Burnett.Analysis.PrincipalEnergy.Freezing.SummedOrderZeroJets

set_option autoImplicit false
set_option maxHeartbeats 6300000

noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview
open scoped ContDiff ENNReal BigOperators Burnett.A03

/-- The actual order-zero comparison of the Weyl action with its left
principal action controls the difference of their principal cubic energies.
The term containing a derivative of the error is absorbed by patch Poincaré. -/
theorem principal_cubic_freezing_order_zero_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) (hJet : ∀ i, BoundedCoordinateJet (w i))
    (hDiff : ∀ i, Differentiable ℝ (w i))
    (hW : ∀ i, MemLp (w i) (ENNReal.ofReal 3) volume)
    (hDW : ∀ p : Index × J, MemLp (actualCoordinateJet (w p.2) p.1) (ENNReal.ofReal 3) volume)
    (L Δ : SchwartzMap E ℂ → E → ℂ) (A B : ℝ≥0∞) (hΔ : SchwartzOrderZeroJetBound Δ A B)
    (hCompare : ∀ i x, w i x = L (z i) x + Δ (z i) x)
    (V : PatchFieldLpJet J) (hLV : ∀ i, (V.1 i : E → ℂ) =ᵐ[volume] L (z i))
    (hV : ∀ p : Index × J, HasWeakCoordinateDerivative3 (V.1 p.2) (V.2 p) p.1)
    (c : E) (R ℓ : ℝ) (hR : 0 < R) (hℓ : 0 < ℓ)
    (hz : tsupport (fieldValueArray z) ⊆ ball c (R * ℓ))
    (C₀ : ℝ≥0∞) (hC₀ : ∀ a b i j k, eLpNorm (C a b i j k : E → ℂ) ⊤ volume ≤ C₀) :
    let p := ENNReal.ofReal 3
    let Y := eLpNorm (fieldValueArray z) p volume
    let X := euclideanFieldGradientNorm z
    ‖principalPatchTestEnergy C z w - principalCubicLpFunctional C z V‖ₑ ≤
      (Fintype.card ((Index × J) × (Index × J)) : ℝ≥0∞) * Fintype.card J * C₀ *
        (A + 2 * (A + B * ENNReal.ofReal (3 * (R * ℓ)))) * Y * X ^ 2 := by
  classical
  intro p Y X
  let F := principalCubicLpFunctional C z
  let W : PatchFieldLpJet J := (fun i => (hW i).toLp _, fun q => (hDW q).toLp _)
  let E₀ : PatchFieldLpJet J := (fun i => (hΔ (z i)).1.toLp _,
    fun q => ((hΔ (z q.2)).2.2.2 q.1).1.toLp _)
  have hWeakW (q : Index × J) : HasWeakCoordinateDerivative3 (W.1 q.2) (W.2 q) q.1 :=
    classical_patchLpJet_is_weak_derivative _ (hDiff q.2) (hW q.2) q.1 (hDW q)
  have hWeakE (q : Index × J) : HasWeakCoordinateDerivative3 (E₀.1 q.2) (E₀.2 q) q.1 :=
    classical_patchLpJet_is_weak_derivative _ (hΔ (z q.2)).2.2.1
      (hΔ (z q.2)).1 q.1 ((hΔ (z q.2)).2.2.2 q.1).1
  have hWeakSum (q : Index × J) : HasWeakCoordinateDerivative3 ((V + E₀).1 q.2) ((V + E₀).2 q) q.1 := by
    intro φ
    change patchLpPair (energyPartial q.1 φ) (V.1 q.2 + E₀.1 q.2) =
      -patchLpPair φ (V.2 q + E₀.2 q)
    rw [map_add, map_add, hV q φ, hWeakE q φ, neg_add]
  have hVal (i : J) : (W.1 i : E → ℂ) =ᵐ[volume] w i := MemLp.coeFn_toLp (hW i)
  have hErr (i : J) : (E₀.1 i : E → ℂ) =ᵐ[volume] Δ (z i) := MemLp.coeFn_toLp (hΔ (z i)).1
  have hEq : W.1 = (V + E₀).1 := by
    funext i
    apply Lp.ext
    have hAdd := Lp.coeFn_add (V.1 i) (E₀.1 i)
    filter_upwards [hVal i, hLV i, hErr i, hAdd] with x hw hl he ha
    change W.1 i x = (V.1 i + E₀.1 i : PatchLp3) x
    rw [hw, ha, Pi.add_apply, hl, he, hCompare i x]
  have hF : principalPatchTestEnergy C z w - F V = F E₀ := by
    rw [← principal_cubic_Lp_functional_eq_action C z w hJet hW hDW]
    change F W - F V = F E₀
    rw [principal_cubic_Lp_functional_eq_of_same_weak_value C z W (V + E₀) hEq hWeakW hWeakSum,
      map_add, add_sub_cancel_left]
  obtain ⟨hValue, hDerivative, _⟩ := separated_field_component_L3_bounds z
  rw [hF]
  apply principal_cubic_order_zero_placement_bound C z E₀ c R ℓ hR hℓ hz C₀ A A B hC₀
  · intro i
    rw [eLpNorm_congr_ae (hErr i)]
    exact (hΔ (z i)).2.1.trans (mul_le_mul_left' (hValue i) A)
  · intro q
    have hDerErr : (E₀.2 q : E → ℂ) =ᵐ[volume] actualCoordinateJet (Δ (z q.2)) q.1 :=
      MemLp.coeFn_toLp ((hΔ (z q.2)).2.2.2 q.1).1
    rw [eLpNorm_congr_ae hDerErr]
    exact ((hΔ (z q.2)).2.2.2 q.1).2.trans
      (add_le_add (mul_le_mul_left' (hDerivative q) A) (mul_le_mul_left' (hValue q.2) B))

end Burnett.A03
