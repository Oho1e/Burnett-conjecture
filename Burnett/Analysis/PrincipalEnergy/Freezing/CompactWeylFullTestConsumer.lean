import Burnett.Analysis.PrincipalEnergy.Freezing.CompactWeylPrincipalComparison

set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal Topology

/-- The fixed compact Weyl test used by the paper consists of the
regularized principal midpoint action, the order-zero midpoint action
and the actual compact proper-support correction kernel. -/
def compactWeylFullTest (P : ℝ) (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hS : tsupport ρ ⊆ ball (0 : E) P) (cut : SchwartzMap E ℂ)
    (a r : E → E → ℝ) (K : E → E → ℂ) (u : SchwartzMap E ℂ) : E → ℂ :=
  compactBaseFixedInfraredWeyl P ρ hρ hS cut a u +
    compactBaseModeQuantization P ρ hρ hS (1/2) r u + compactKernelAction K u

/-- One value and first-jet comparison for the full compact Weyl action.
The actual input, the two actual cutoff placements, the fixed infrared
choice and the complete first-order and order-zero symbols are
explicit. The kernel input states exactly the regularity still needed
when a concrete proper-support construction is supplied. -/
theorem exists_compact_weyl_full_test_center_uniform_comparison_W13
    (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a r : E → E → ℝ)
    (supportA : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (supportR : ∀ x ξ, x ∉ closedBall (0 : E) R → r x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hr : CompactBaseFrequencyJets (fun x q => (r x q : ℂ)) univ)
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M N : ℝ) (M0 : 0 ≤ M) (N0 : 0 ≤ N)
    (hM : CompactBaseOrderOneBudget a M) (hN : CompactBaseOrderZeroBudget r N)
    (cut add : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ)
    (plateau : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1)
    (K : E → E → ℂ) (RK : ℝ) (smoothK : ContDiff ℝ 1 (Function.uncurry K))
    (supportK : ∀ x y, x ∉ closedBall (0 : E) RK ∨ y ∉ closedBall (0 : E) RK → K x y = 0)
    (Θ : SchwartzMap E ℂ) (θ : E → SchwartzMap E ℂ)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (θshape : ∀ c x, θ c x = Θ (ℓ⁻¹ • (x-c))) :
    let B := compactWeylFullTest P ρ hρ hS cut a r K
    let B₀ (c : E) := radianAction (fixedInfraredSymbol cut add (a c))
    ∃ Bℓ : ℝ≥0∞, Bℓ < ⊤ ∧ ∀ c : E,
      SchwartzOrderZeroJetBound (fun u => (-Complex.I) •
        (sandwichedScalarTest (θ c) (fun v => B v - B₀ c v) u -
          radianLeftQuantization (localizedFrozenPrincipalSymbol a c (θ c)) u)) Bℓ Bℓ := by
  intro B B₀
  let L := radianLeftQuantization (fun x ξ => (a x ξ : ℂ))
  let Q := compactBaseFixedInfraredWeyl P ρ hρ hS cut a
  let W := compactBaseModeQuantization P ρ hρ hS (1/2) r
  let S := compactKernelAction K
  let G (u : SchwartzMap E ℂ) := Q u - L u
  let F (u : SchwartzMap E ℂ) := (G u + W u) + S u
  obtain ⟨C,Cfin,hG⟩ := exists_compact_fixed_principal_weyl_left_gap_W13 P R hP hRP ρ hρ hS ρone
    a supportA ha hom M M0 hM cut hcut plateau
  obtain ⟨D,Dfin,lower⟩ := exists_compact_base_order_zero_mode_action_W13 P R hP hRP.le
    ρ hρ hS r supportR hr N N0 hN
  obtain ⟨A,Afin,hK⟩ := exists_compact_kernel_order_zero_jet_bound K RK smoothK supportK
  have hW : SchwartzOrderZeroJetBound W D D := lower (1/2)
  have re : SchwartzOrderZeroJetBound F (C+D+A) (C+D+A) :=
    schwartz_order_zero_jet_bound_add _ _ _ _ _ _
      (schwartz_order_zero_jet_bound_add G W C C D D hG hW) hK
  have fin : C+D+A < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨Cfin,Dfin⟩,Afin⟩
  have same (u : SchwartzMap E ℂ) : B u = L u + F u := by
    funext x
    change ((Q u x + W u x) + S u x) = L u x + (((Q u x - L u x) + W u x) + S u x)
    ring
  exact exists_affine_original_test_comparison_W13 P R hP hRP ρ hρ hS ρone
    a supportA ha hom M M0 hM B F same _ _ fin fin re cut add hcut hadd Θ θ ℓ hℓ θshape

end Burnett.A03
