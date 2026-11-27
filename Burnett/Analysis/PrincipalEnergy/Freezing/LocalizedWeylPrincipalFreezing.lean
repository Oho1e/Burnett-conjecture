import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedLeftPrincipalFreezing
import Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalFreezingOrderZero
import Burnett.Analysis.PrincipalEnergy.Freezing.CompactWeylFullTestConsumer

set_option autoImplicit false
set_option maxHeartbeats 7500000

noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview
open scoped ContDiff ENNReal BigOperators Burnett.A03

/-- The real left action in the localized Fourier expansion is exactly
the left comparison symbol of the original Weyl action, with its sign. -/
theorem localizedFrozenPrincipalSkewLeft_eq (a : E → E → ℝ) (c : E)
    (θ : SchwartzMap E ℂ) (q : E → ℝ) (hθ : ∀ x, θ x = (q x : ℂ))
    (u : SchwartzMap E ℂ) (x : E) :
    (-Complex.I) * radianLeftQuantization (localizedFrozenPrincipalSymbol a c θ) u x =
      radianSkewAction (fun ξ => (q x)^2 * (a x ξ - a c ξ)) u x := by
  rw [radianSkewAction, ← radian_left_quantization_frozen]
  congr 1
  unfold radianLeftQuantization
  apply integral_congr_ae
  filter_upwards with ξ
  rw [localizedFrozenPrincipalSymbol, hθ]
  push_cast
  rfl

/-- Freeze the symbol in the complete physical Weyl principal cubic
action by using the exact left expansion and its genuine first-jet remainder. -/
theorem localized_weyl_principal_freezing_of_left_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (B B₀ : SchwartzMap E ℂ → E → ℂ) (a : E → E → ℝ) (c : E)
    (θ : SchwartzMap E ℂ) (q : E → ℝ) (hθ : ∀ x, θ x = (q x : ℂ))
    (R ℓ : ℝ) (hR : 0 < R) (hℓ : 0 < ℓ)
    (hz : tsupport (fieldValueArray z) ⊆ ball c (R * ℓ))
    (C₀ : ℝ≥0∞) (hC₀ : ∀ a b i j k, eLpNorm (C a b i j k : E → ℂ) ⊤ volume ≤ C₀)
    (A K : ℝ≥0∞)
    (hRemainder : SchwartzOrderZeroJetBound (fun u => (-Complex.I) •
      (sandwichedScalarTest θ (fun v => B v - B₀ v) u -
        radianLeftQuantization (localizedFrozenPrincipalSymbol a c θ) u)) A A)
    (V : PatchFieldLpJet J)
    (hValue : ∀ i : J, (V.1 i : E → ℂ) =ᵐ[volume] fun x =>
      radianSkewAction (fun ξ => (q x)^2 * (a x ξ - a c ξ)) (z i) x)
    (hWeak : ∀ j : Index × J, HasWeakCoordinateDerivative3 (V.1 j.2) (V.2 j) j.1)
    (energyBound : ‖principalCubicLpFunctional C z V‖ₑ ≤ K)
    (w : J → SchwartzMap E ℂ)
    (hw : ∀ i x, w i x = (-Complex.I) * sandwichedScalarTest θ (fun v => B v - B₀ v) (z i) x) :
    let p := ENNReal.ofReal 3
    let Y := eLpNorm (fieldValueArray z) p volume
    let X := euclideanFieldGradientNorm z
    ‖principalPatchTestEnergy C z (fun i => w i)‖ₑ ≤ K +
      (Fintype.card ((Index × J) × (Index × J)) : ℝ≥0∞) * Fintype.card J * C₀ *
        (A + 2 * (A + A * ENNReal.ofReal (3 * (R * ℓ)))) * Y * X ^ 2 := by
  intro p Y X
  let Q := sandwichedScalarTest θ (fun v => B v - B₀ v)
  let L (u : SchwartzMap E ℂ) := (-Complex.I) • radianLeftQuantization (localizedFrozenPrincipalSymbol a c θ) u
  let Δ (u : SchwartzMap E ℂ) := (-Complex.I) • (Q u - radianLeftQuantization (localizedFrozenPrincipalSymbol a c θ) u)
  have hCompare (i : J) (x : E) : w i x = L (z i) x + Δ (z i) x := by
    rw [hw]
    change (-Complex.I) * Q (z i) x = (-Complex.I) * radianLeftQuantization _ _ _ +
      (-Complex.I) * (Q (z i) x - radianLeftQuantization _ _ _)
    ring
  have hVL (i : J) : (V.1 i : E → ℂ) =ᵐ[volume] L (z i) := by
    filter_upwards [hValue i] with x hx
    change _ = (-Complex.I) * radianLeftQuantization (localizedFrozenPrincipalSymbol a c θ) (z i) x
    rw [localizedFrozenPrincipalSkewLeft_eq a c θ q hθ]
    exact hx
  have hJet : ∀ i, BoundedCoordinateJet (w i : E → ℂ) := fun i => schwartz_bounded_coordinate_jet (w i)
  have hD (j : Index × J) : MemLp (actualCoordinateJet (w j.2) j.1) p volume :=
    (energyPartial j.1 (w j.2)).memLp p volume
  let F := principalCubicLpFunctional C z
  let G := principalPatchTestEnergy C z (fun i => w i)
  have hError := principal_cubic_freezing_order_zero_bound C z (fun i => w i) hJet
    (fun i => (w i).differentiable) (fun i => (w i).memLp p volume) hD
    L Δ A A hRemainder hCompare V hVL hWeak c R ℓ hR hℓ hz C₀ hC₀
  change ‖G - F V‖ₑ ≤ _ at hError
  change ‖G‖ₑ ≤ _
  rw [show G = F V + (G - F V) by ring]
  exact (enorm_add_le _ _).trans (add_le_add energyBound hError)

end Burnett.A03
