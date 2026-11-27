import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedRescaledSymbolJets

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Metric Set Burnett.Geometry.ConnectionDifference
open scoped ContDiff

/-- The actual ambient frequency jet commutes with the spatial cutoff.
The smoothness assumptions concern only the single frequency point. -/
theorem angular_rescaled_symbol_jet_eq (χ : CoordinateSpace → ℝ)
    (a : CoordinateSpace → CoordinateSpace → ℝ) (c y angle : CoordinateSpace) (ℓ : ℝ) (k : ℕ)
    (ha : ContDiffAt ℝ (k : ℕ) (a (c + ℓ • y)) angle)
    (hc : ContDiffAt ℝ (k : ℕ) (a c) angle) :
    iteratedFDeriv ℝ k (fun ξ =>
        rescaledLocalizedSymbolDifference χ (fun x => a x ξ) c ℓ y) angle =
      rescaledLocalizedSymbolDifference χ (fun x => iteratedFDeriv ℝ k (a x) angle) c ℓ y := by
  change iteratedFDeriv ℝ k (fun ξ => (χ y) ^ 2 • (a (c + ℓ • y) ξ - a c ξ)) angle =
    (χ y) ^ 2 • (iteratedFDeriv ℝ k (a (c + ℓ • y)) angle - iteratedFDeriv ℝ k (a c) angle)
  rw [iteratedFDeriv_const_smul_apply' (ha.sub hc)]
  have hSub : (fun ξ => a (c + ℓ • y) ξ - a c ξ) =
      fun ξ => a (c + ℓ • y) ξ + -a c ξ := funext fun _ => sub_eq_add_neg _ _
  have hNeg : iteratedFDeriv ℝ k (fun ξ => -a c ξ) angle = -iteratedFDeriv ℝ k (a c) angle :=
    iteratedFDeriv_neg_apply
  rw [hSub, iteratedFDeriv_add_apply' ha hc.neg, hNeg, sub_eq_add_neg]

/-- Spatial derivatives of each actual ambient angular jet satisfy the same
uniform scale bound. The direction set may be the unit sphere. -/
theorem exists_rescaled_ambient_angular_spatial_jet_bound
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (S : ℝ) (hS : 0 ≤ S)
    (hSupport : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S) (N k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (a : CoordinateSpace → CoordinateSpace → ℝ) (centers directions : Set CoordinateSpace),
        (∀ x : CoordinateSpace, ∀ angle ∈ directions, ContDiffAt ℝ (k : ℕ) (a x) angle) →
        (∀ angle ∈ directions, ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ k (a x) angle)) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ c ∈ centers, ∀ angle ∈ directions, ∀ j : ℕ, 0 < j → j ≤ max 1 N →
            ∀ x ∈ closedBall c S,
              ‖iteratedFDeriv ℝ j (fun z => iteratedFDeriv ℝ k (a z) angle) x‖ ≤ M) →
          ∀ c ∈ centers, ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ angle ∈ directions,
            ∀ n : ℕ, n ≤ N → ∀ y : CoordinateSpace,
              ‖iteratedFDeriv ℝ n (fun z => iteratedFDeriv ℝ k (fun ξ =>
                rescaledLocalizedSymbolDifference χ (fun x => a x ξ) c ℓ z) angle) y‖ ≤ K * M * ℓ := by
  let Jet := ContinuousMultilinearMap ℝ (fun _ : Fin k => CoordinateSpace) ℝ
  obtain ⟨K, hK, estimate⟩ :=
    exists_rescaled_localized_symbol_jet_bound (F := Jet) (Ω := CoordinateSpace) χ hχ S hS hSupport N
  refine ⟨K, hK, ?_⟩
  intro a centers directions smoothFrequency smoothSpatial M hM hBounds c hc ℓ hℓ hUpper angle hAngle n hn y
  let A (x ξ : CoordinateSpace) : Jet := iteratedFDeriv ℝ k (a x) ξ
  have same : (fun z => iteratedFDeriv ℝ k (fun ξ =>
      rescaledLocalizedSymbolDifference χ (fun x => a x ξ) c ℓ z) angle) =
      rescaledLocalizedSymbolDifference χ (fun x => A x angle) c ℓ := by
    funext z
    exact angular_rescaled_symbol_jet_eq χ a c z angle ℓ k (smoothFrequency (c + ℓ • z) angle hAngle)
      (smoothFrequency c angle hAngle)
  rw [same]
  exact estimate A centers directions smoothSpatial M hM hBounds c hc ℓ hℓ hUpper angle hAngle n hn y

end Burnett.A03
