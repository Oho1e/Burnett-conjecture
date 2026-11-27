import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedSpatialModeProfileJets
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff BigOperators ENNReal

/-- The actual real-valued essential supremum of the Euclidean
operator norm of a spatial profile jet. -/
def spatialProfileJetLInfinity (n : ℕ) (f : CoordinateSpace → ℝ) : ℝ :=
  (eLpNormEssSup (iteratedFDeriv ℝ n f) (volume : Measure CoordinateSpace)).toReal

private theorem spatial_profile_jet_essSup_le (n : ℕ) (f : CoordinateSpace → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (bound : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ A) :
    spatialProfileJetLInfinity n f ≤ A := by
  have ess := eLpNormEssSup_le_of_ae_bound (μ := volume) (Eventually.of_forall bound)
  unfold spatialProfileJetLInfinity
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ess).trans_eq (ENNReal.toReal_ofReal hA)

/-- A normalized symbol coefficient weight can be paired with the actual
spatial essential suprema. The resulting bounds are uniform over all
finite selections of integer modes and also hold for the full sum. -/
theorem exists_weighted_spatial_profile_sum_bound (P : ℝ) (L : ℕ) (hL : 7 < L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ρ : CoordinateSpace → ℝ) (B : ℝ), ContDiff ℝ ∞ ρ → 0 ≤ B →
        (∀ r : ℕ, r ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ r ρ y‖ ≤ B) →
        ∀ (c : CoordinateSpace) (ℓ : ℝ), 0 < ℓ →
          ∀ (aCos aSin : (Index → ℤ) → ℝ) (M : ℝ), 0 ≤ M →
            (∀ k, 0 ≤ aCos k ∧ aCos k ≤ M * ℓ / (spatialLatticeWeight k)^L) →
            (∀ k, 0 ≤ aSin k ∧ aSin k ≤ M * ℓ / (spatialLatticeWeight k)^L) →
            ∀ r : ℕ, r ≤ 2 →
              let term (k : Index → ℤ) :=
                aCos k * spatialProfileJetLInfinity r (localizedSpatialCosineProfile P k ρ c ℓ) +
                  aSin k * spatialProfileJetLInfinity r (localizedSpatialSineProfile P k ρ c ℓ)
              Summable term ∧
                (∑' k, term k) ≤ C * B * M * ℓ * (ℓ⁻¹)^r ∧
                ∀ modes : Finset (Index → ℤ),
                  (∑ k ∈ modes, term k) ≤ C * B * M * ℓ * (ℓ⁻¹)^r := by
  obtain ⟨D, hD, profiles⟩ := exists_localized_spatial_mode_profile_jet_bound P
  obtain ⟨A, hA, truncations⟩ := exists_spatial_lattice_weighted_truncation_bound L hL
  let C := 2 * D * A
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro ρ B hρ hB hJets c ℓ hℓ aCos aSin M hM bCos bSin r hr term
  let W (k : Index → ℤ) := (spatialLatticeWeight k)^r / (spatialLatticeWeight k)^L
  let U := 2 * D * B * M * ℓ * (ℓ⁻¹)^r
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have termNonneg (k : Index → ℤ) : 0 ≤ term k := by
    dsimp only [term, spatialProfileJetLInfinity]
    exact add_nonneg (mul_nonneg (bCos k).1 ENNReal.toReal_nonneg)
      (mul_nonneg (bSin k).1 ENNReal.toReal_nonneg)
  have termBound (k : Index → ℤ) : term k ≤ U * W k := by
    have profile (f : CoordinateSpace → ℝ)
        (h : ∀ x, ‖iteratedFDeriv ℝ r f x‖ ≤ D * B * (ℓ⁻¹)^r * (spatialLatticeWeight k)^r) :
        spatialProfileJetLInfinity r f ≤ D * B * (ℓ⁻¹)^r * (spatialLatticeWeight k)^r :=
      spatial_profile_jet_essSup_le r f _ (by unfold spatialLatticeWeight; positivity) h
    have cosine := profile (localizedSpatialCosineProfile P k ρ c ℓ)
      (fun x => (profiles ρ hρ B hB hJets k c ℓ hℓ r hr x).1)
    have sine := profile (localizedSpatialSineProfile P k ρ c ℓ)
      (fun x => (profiles ρ hρ B hB hJets k c ℓ hℓ r hr x).2)
    have hc : 0 ≤ spatialProfileJetLInfinity r (localizedSpatialCosineProfile P k ρ c ℓ) :=
      ENNReal.toReal_nonneg
    have hs : 0 ≤ spatialProfileJetLInfinity r (localizedSpatialSineProfile P k ρ c ℓ) :=
      ENNReal.toReal_nonneg
    have b : 0 ≤ M * ℓ / (spatialLatticeWeight k)^L := by unfold spatialLatticeWeight; positivity
    have := add_le_add (mul_le_mul (bCos k).2 cosine hc b) (mul_le_mul (bSin k).2 sine hs b)
    refine this.trans_eq ?_
    dsimp only [U, W]
    ring
  have weighted := summable_spatial_lattice_weighted_decay L r hL hr
  have termsSummable : Summable term :=
    Summable.of_nonneg_of_le termNonneg termBound (weighted.mul_left U)
  have finite (modes : Finset (Index → ℤ)) :
      (∑ k ∈ modes, term k) ≤ C * B * M * ℓ * (ℓ⁻¹)^r := by
    calc
      _ ≤ ∑ k ∈ modes, U * W k := Finset.sum_le_sum (fun k _ => termBound k)
      _ = U * ∑ k ∈ modes, W k := by rw [Finset.mul_sum]
      _ ≤ U * A := mul_le_mul_of_nonneg_left (truncations r hr modes) hU
      _ = _ := by dsimp only [C, U]; ring
  refine ⟨termsSummable, ?_, finite⟩
  exact le_of_tendsto termsSummable.hasSum (Eventually.of_forall finite)

end Burnett.A03
