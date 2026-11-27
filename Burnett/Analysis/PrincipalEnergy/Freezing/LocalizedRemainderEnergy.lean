import Burnett.Analysis.PrincipalEnergy.Freezing.OrderZeroRemainderSeries
import Burnett.Analysis.PrincipalEnergy.Freezing.OrderZeroCubicPlacements
import Burnett.Analysis.PrincipalEnergy.Freezing.SummableModeFourierMoments

set_option autoImplicit false
set_option maxHeartbeats 2800000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview
open scoped BigOperators ContDiff ENNReal Burnett.A03

/-- The literal order-zero symmetrization difference for the localized real
Fourier modes contributes at most the manuscript's residual energy scale.
For this remainder the loss in the derivative estimate cancels against
the patch radius, so the displayed coefficient is uniform in length. -/
theorem exists_localized_symmetrization_remainder_energy_bound {J : Type} [Fintype J]
    (L : ℕ) (hL : 7 < L) (P R : ℝ) (hP : 0 < P) (hR : 0 < R)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hSupport : tsupport ρ ⊆ ball (0 : E) P) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      ∀ (b : (Index → ℤ) → Fin 2 → E → ℝ) (D : (Index → ℤ) → Fin 2 → ℝ),
        (∀ k j, ContDiffOn ℝ ∞ (b k j) {ξ | ξ ≠ 0}) →
        (∀ k j (t : ℝ), 0 < t → ∀ ξ, b k j (t • ξ) = t * b k j ξ) →
        (∀ k j n, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (b k j) ξ‖ ≤ D k j) →
        ∀ (c : E) (ℓ : ℝ) (hℓ : 0 < ℓ) (M : ℝ), 0 ≤ M →
        (∀ k j, 0 ≤ D k j ∧ D k j ≤ M * ℓ / spatialLatticeWeight k ^ L) →
        ∀ (C : Index → Index → J → J → J → SchwartzMap E ℂ) (C₀ : ℝ≥0∞),
        (∀ a d i j k, eLpNorm (C a d i j k : E → ℂ) ⊤ volume ≤ C₀) →
        ∀ z : J → SchwartzMap E ℂ, tsupport (fieldValueArray z) ⊆ ball c (R * ℓ) →
          let I := Index → ℤ
          let f (k : I) (j : Fin 2) := localizedRealSpatialModeSchwartz P k ρ hρ hSupport c ℓ hℓ j
          let W (i : J) (k : I) (j : Fin 2) := separatedSkewLeftRemainder (f k j) (b k j) (z i)
          ∃ (v : J → I → Fin 2 → PatchLp3) (d : Index × J → I → Fin 2 → PatchLp3) (V : PatchFieldLpJet J),
            (∀ i k j, (v i k j : E → ℂ) =ᵐ[volume] W i k j) ∧
            (∀ p k j, (d p k j : E → ℂ) =ᵐ[volume]
              fun x => fderiv ℝ (W p.2 k j) x (EuclideanSpace.single p.1 1)) ∧
            (∀ i, HasSum (fun k => ∑ j, v i k j) (V.1 i)) ∧
            (∀ p, HasSum (fun k => ∑ j, d p k j) (V.2 p) ∧ HasWeakCoordinateDerivative3 (V.1 p.2) (V.2 p) p.1) ∧
            ‖principalCubicLpFunctional C z V‖ₑ ≤
              (Fintype.card ((Index × J) × (Index × J)) : ℝ≥0∞) * Fintype.card J * C₀ *
              (ENNReal.ofReal (K₁ * M) + 2 * (ENNReal.ofReal (K₁ * M) + ENNReal.ofReal (3 * R * K₂ * M))) *
              eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume * euclideanFieldGradientNorm z ^ 2 := by
  classical
  obtain ⟨K, hK, series⟩ := exists_summable_symmetrization_remainder_jets
  obtain ⟨F₁, hF₁, momOne⟩ := exists_summable_localized_mode_fourier_moments
    L 1 hL (by decide) P hP ρ hρ hSupport
  obtain ⟨F₂, hF₂, momTwo⟩ := exists_summable_localized_mode_fourier_moments
    L 2 hL (by decide) P hP ρ hρ hSupport
  have t0 : 0 ≤ tau := by unfold tau; positivity
  let K₁ := K * F₁
  let K₂ := K * tau * F₂
  have hK₁ : 0 ≤ K₁ := mul_nonneg hK hF₁
  have hK₂ : 0 ≤ K₂ := mul_nonneg (mul_nonneg hK t0) hF₂
  refine ⟨K₁, K₂, hK₁, hK₂, ?_⟩
  intro b D hb hom jet c ℓ hℓ M hM decay C C₀ hC₀ z hz I f W
  let p := ENNReal.ofReal 3
  let Y := eLpNorm (fieldValueArray z) p volume
  let X := euclideanFieldGradientNorm z
  let A := ENNReal.ofReal (K₁ * M)
  let B := ENNReal.ofReal (K₂ * M * ℓ⁻¹)
  obtain ⟨summ1, bound1⟩ := momOne c ℓ hℓ M hM D decay
  obtain ⟨summ2, bound2⟩ := momTwo c ℓ hℓ M hM D decay
  have scale1 : ℓ * (ℓ ^ 1)⁻¹ = 1 := by rw [pow_one, mul_inv_cancel₀ hℓ.ne']
  have scale2 : ℓ * (ℓ ^ 2)⁻¹ = ℓ⁻¹ := by field_simp [hℓ.ne']
  rw [scale1, mul_one] at bound1
  rw [scale2] at bound2
  choose v d cert using fun i : J =>
    series f b D hb hom (fun k j => (decay k j).1) jet summ1 summ2 (z i)
  let V : PatchFieldLpJet J :=
    (fun i => ∑' k, ∑ j, v i k j, fun q => ∑' k, ∑ j, d q.2 q.1 k j)
  refine ⟨v, (fun q => d q.2 q.1), V, (fun i => (cert i).1),
    (fun q => (cert q.2).2.1 q.1), (fun i => (cert i).2.2.1),
    (fun q => ⟨((cert q.2).2.2.2.2 q.1).1, ((cert q.2).2.2.2.2 q.1).2.1⟩), ?_⟩
  obtain ⟨hVal, hDer, _⟩ := separated_field_component_L3_bounds z
  have val (i : J) : eLpNorm (V.1 i : E → ℂ) p volume ≤ A * Y := by
    let Yi := eLpNorm (z i : E → ℂ) p volume
    have hB : ‖V.1 i‖ ≤ (K₁ * M) * Yi.toReal := by
      refine (cert i).2.2.2.1.trans ?_
      calc
        _ ≤ K * Yi.toReal * (F₁ * M) := mul_le_mul_of_nonneg_left bound1 (by positivity)
        _ = _ := by dsimp only [K₁]; ring
    rw [← ENNReal.ofReal_toReal (Lp.memLp (V.1 i)).eLpNorm_lt_top.ne]
    change ENNReal.ofReal ‖V.1 i‖ ≤ A * Y
    refine (ENNReal.ofReal_le_ofReal hB).trans ?_
    rw [ENNReal.ofReal_mul (mul_nonneg hK₁ hM), ENNReal.ofReal_toReal ((z i).memLp p volume).eLpNorm_lt_top.ne]
    exact mul_le_mul_left' (hVal i) _
  have der (q : Index × J) : eLpNorm (V.2 q : E → ℂ) p volume ≤ A * X + B * Y := by
    let Yi := eLpNorm (z q.2 : E → ℂ) p volume
    let Xi := eLpNorm (energyPartial q.1 (z q.2) : E → ℂ) p volume
    have hX0 : 0 ≤ (K₁ * M) * Xi.toReal := by positivity
    have hY0 : 0 ≤ (K₂ * M * ℓ⁻¹) * Yi.toReal := by positivity
    have hB : ‖V.2 q‖ ≤ (K₁ * M) * Xi.toReal + (K₂ * M * ℓ⁻¹) * Yi.toReal := by
      refine ((cert q.2).2.2.2.2 q.1).2.2.trans ?_
      calc
        _ ≤ K * Xi.toReal * (F₁ * M) + K * tau * Yi.toReal * (F₂ * M * ℓ⁻¹) :=
          add_le_add (mul_le_mul_of_nonneg_left bound1 (by positivity))
            (mul_le_mul_of_nonneg_left bound2 (by positivity))
        _ = _ := by dsimp only [K₁, K₂]; ring
    rw [← ENNReal.ofReal_toReal (Lp.memLp (V.2 q)).eLpNorm_lt_top.ne]
    change ENNReal.ofReal ‖V.2 q‖ ≤ A * X + B * Y
    refine (ENNReal.ofReal_le_ofReal hB).trans ?_
    rw [ENNReal.ofReal_add hX0 hY0, ENNReal.ofReal_mul (mul_nonneg hK₁ hM),
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hK₂ hM) (inv_nonneg.mpr hℓ.le))]
    rw [ENNReal.ofReal_toReal ((energyPartial q.1 (z q.2)).memLp p volume).eLpNorm_lt_top.ne,
      ENNReal.ofReal_toReal ((z q.2).memLp p volume).eLpNorm_lt_top.ne]
    exact add_le_add (mul_le_mul_left' (hDer q) _) (mul_le_mul_left' (hVal q.2) _)
  refine (principal_cubic_order_zero_placement_bound C z V c R ℓ hR hℓ hz C₀ A A B hC₀ val der).trans_eq ?_
  have length : B * ENNReal.ofReal (3 * (R * ℓ)) = ENNReal.ofReal (3 * R * K₂ * M) := by
    dsimp only [B]
    rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hK₂ hM) (inv_nonneg.mpr hℓ.le))]
    congr 1
    field_simp [hℓ.ne']
  rw [length]

end Burnett.A03
