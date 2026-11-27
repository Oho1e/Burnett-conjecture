import Burnett.Analysis.PrincipalEnergy.Freezing.RescaledDifferenceJets
import Burnett.Analysis.PrincipalEnergy.Freezing.NestedPatchCutoffs
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Metric Set Filter Burnett.Geometry.ConnectionDifference
open scoped ContDiff Topology BigOperators

variable {F Ω : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual localized difference as a function of the rescaled coordinate. -/
def rescaledLocalizedSymbolDifference (χ : CoordinateSpace → ℝ) (A : CoordinateSpace → F)
    (c : CoordinateSpace) (ℓ : ℝ) (y : CoordinateSpace) : F :=
  (χ y) ^ 2 • rescaledSpatialDifference A c ℓ y

/-- On the physical patch the same cutoff is the inverse affine rescaling
of the fixed spatial profile. -/
theorem rescaled_localized_symbol_pullback (χ : CoordinateSpace → ℝ) (A : CoordinateSpace → F)
    (c y : CoordinateSpace) (ℓ : ℝ) (hℓ : ℓ ≠ 0) :
    (χ (ℓ⁻¹ • ((c + ℓ • y) - c))) ^ 2 • (A (c + ℓ • y) - A c) =
      rescaledLocalizedSymbolDifference χ A c ℓ y := by
  simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hℓ, one_smul,
    rescaledLocalizedSymbolDifference, rescaledSpatialDifference]

/-- One constant works for every center, scale and angular parameter within
the specified fixed closed-ball seminorm bound. The estimate is global in y. -/
theorem exists_rescaled_localized_symbol_jet_bound
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (S : ℝ) (hS : 0 ≤ S)
    (hSupport : tsupport χ ⊆ closedBall (0 : CoordinateSpace) S) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (A : CoordinateSpace → Ω → F) (centers : Set CoordinateSpace) (directions : Set Ω),
        (∀ angle ∈ directions, ContDiff ℝ ∞ (fun x => A x angle)) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ c ∈ centers, ∀ angle ∈ directions, ∀ j : ℕ, 0 < j → j ≤ max 1 N →
            ∀ x ∈ closedBall c S, ‖iteratedFDeriv ℝ j (fun z => A z angle) x‖ ≤ M) →
          ∀ c ∈ centers, ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ angle ∈ directions,
            ∀ n : ℕ, n ≤ N → ∀ y : CoordinateSpace,
              ‖iteratedFDeriv ℝ n
                  (rescaledLocalizedSymbolDifference χ (fun x => A x angle) c ℓ) y‖ ≤ K * M * ℓ := by
  let q : CoordinateSpace → ℝ := fun y => (χ y) ^ 2
  have hq : ContDiff ℝ ∞ q := hχ.pow 2
  have hqSupport : tsupport q ⊆ tsupport χ := by
    simpa only [q, pow_two] using (tsupport_mul_subset_left (f := χ) (g := χ))
  have hqCompact : HasCompactSupport q :=
    (isCompact_closedBall (0 : CoordinateSpace) S).of_isClosed_subset isClosed_closure
      (hqSupport.trans hSupport)
  have boundProfile (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖iteratedFDeriv ℝ j q y‖ ≤ C := by
    have hj : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    obtain ⟨y, maximum⟩ :=
      (hq.continuous_iteratedFDeriv hj).norm.exists_forall_ge_of_hasCompactSupport
        (hqCompact.iteratedFDeriv (𝕜 := ℝ) j).norm
    exact ⟨_, norm_nonneg _, maximum⟩
  choose C hC hCbound using boundProfile
  let B := ∑ j ∈ Finset.range (N + 1), C j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hC j)
  have allProfile (j : ℕ) (hj : j ≤ N) (y : CoordinateSpace) :
      ‖iteratedFDeriv ℝ j q y‖ ≤ B :=
    (hCbound j y).trans
      (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  let S₁ := max 1 S
  have hS₁ : 0 ≤ S₁ := zero_le_one.trans (le_max_left 1 S)
  let K := (2 : ℝ) ^ N * B * S₁
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro A centers directions smooth M hM jet c hc ℓ hℓ hSmall angle hAngle n hn y
  let fiber := fun x => A x angle
  let G := rescaledSpatialDifference fiber c ℓ
  have hFiber : ContDiff ℝ ∞ fiber := smooth angle hAngle
  have hG : ContDiff ℝ ∞ G :=
    (hFiber.comp (contDiff_const.add (contDiff_id.const_smul ℓ))).sub contDiff_const
  have smallBall : closedBall c (S * ℓ) ⊆ closedBall c S :=
    closedBall_subset_closedBall (mul_le_of_le_one_right hS hSmall)
  change ‖iteratedFDeriv ℝ n (fun y => q y • G y) y‖ ≤ K * M * ℓ
  by_cases hy : y ∈ closedBall (0 : CoordinateSpace) S
  · have physical := smallBall (affine_rescaling_mem_closedBall c y S ℓ hℓ.le hy)
    have spatial (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j G y‖ ≤ S₁ * M * ℓ := by
      cases j with
      | zero =>
        rw [norm_iteratedFDeriv_zero]
        have grad (x : CoordinateSpace) (hx : x ∈ closedBall c (S * ℓ)) :
            ‖fderiv ℝ fiber x‖ ≤ M := by
          rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ fiber) (x := x),
            norm_iteratedFDeriv_fderiv]
          exact jet c hc angle hAngle 1 Nat.one_pos (le_max_left 1 N) x (smallBall hx)
        calc
          _ ≤ M * (S * ℓ) :=
            rescaled_spatial_difference_zero_bound fiber hFiber c y S ℓ M hS hℓ.le hM hy grad
          _ = S * M * ℓ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right 1 S) hM) hℓ.le
      | succ j =>
        rw [rescaled_spatial_difference_succ_jet fiber hFiber c y ℓ j, norm_smul,
          Real.norm_of_nonneg (pow_nonneg hℓ.le _)]
        have boundJ : ‖iteratedFDeriv ℝ (j + 1) fiber (c + ℓ • y)‖ ≤ M :=
          jet c hc angle hAngle (j + 1) (Nat.succ_pos j) (hj.trans (le_max_right 1 N)) _ physical
        have scale : ℓ ^ (j + 1) ≤ ℓ := by
          rw [pow_succ]
          exact mul_le_of_le_one_left hℓ.le (pow_le_one₀ hℓ.le hSmall)
        calc
          _ ≤ ℓ ^ (j + 1) * M := mul_le_mul_of_nonneg_left boundJ (pow_nonneg hℓ.le _)
          _ ≤ ℓ * M := mul_le_mul_of_nonneg_right scale hM
          _ = 1 * M * ℓ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left 1 S) hM) hℓ.le
    have hnInf : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hSum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i q y‖ *
          ‖iteratedFDeriv ℝ (n - i) G y‖ :=
        norm_iteratedFDeriv_smul_le hq hG y hnInf
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B * (S₁ * M * ℓ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiN := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (allProfile i hiN y) (by positivity))
          (spatial (n - i) ((Nat.sub_le n i).trans hn)) (norm_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ n * B * (S₁ * M * ℓ) := by
        rw [← hSum]
        simp only [Finset.sum_mul]
      _ ≤ (2 : ℝ) ^ N * B * (S₁ * M * ℓ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hB) (by positivity)
      _ = _ := by dsimp only [K]; ring
  · have hLocalSupport : tsupport (fun y => q y • G y) ⊆ closedBall (0 : CoordinateSpace) S :=
      (tsupport_smul_subset_left q G).trans (hqSupport.trans hSupport)
    have hZero : iteratedFDeriv ℝ n (fun y => q y • G y) y = 0 := by
      apply Function.notMem_support.mp
      intro hs
      exact hy (hLocalSupport (support_iteratedFDeriv_subset n hs))
    rw [hZero, norm_zero]
    dsimp only [K]
    positivity

/-- The fixed profile from the physical nested cutoffs supplies the same
all-order rescaled bound. The two chosen windows retain their exact nesting. -/
theorem exists_nested_profile_rescaled_symbol_jet_bound (R : ℝ) (hR : 0 ≤ R) (N : ℕ) :
    ∃ (χ : CoordinateSpace → ℝ) (K : ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ 0 ≤ K ∧
      tsupport χ ⊆ ball (0 : CoordinateSpace) (R + 2) ∧
      (∀ y ∈ closedBall (0 : CoordinateSpace) (R + 1), χ y = 1) ∧
      (∀ (c : CoordinateSpace) (ℓ : ℝ), 0 < ℓ →
        let θ : CoordinateSpace → ℝ := fun x => χ (ℓ⁻¹ • (x - c))
        let Θ : CoordinateSpace → ℝ := fun x => χ ((2 * ℓ)⁻¹ • (x - c))
        (∀ x ∈ closedBall c (R * ℓ), θ =ᶠ[𝓝 x] 1) ∧
        (∀ x ∈ tsupport θ, Θ =ᶠ[𝓝 x] 1)) ∧
      ∀ (A : CoordinateSpace → Ω → F) (centers : Set CoordinateSpace) (directions : Set Ω),
        (∀ angle ∈ directions, ContDiff ℝ ∞ (fun x => A x angle)) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ c ∈ centers, ∀ angle ∈ directions, ∀ j : ℕ, 0 < j → j ≤ max 1 N →
            ∀ x ∈ closedBall c (R + 2), ‖iteratedFDeriv ℝ j (fun z => A z angle) x‖ ≤ M) →
          ∀ c ∈ centers, ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ angle ∈ directions,
            ∀ n : ℕ, n ≤ N → ∀ y : CoordinateSpace,
              ‖iteratedFDeriv ℝ n
                  (rescaledLocalizedSymbolDifference χ (fun x => A x angle) c ℓ) y‖ ≤ K * M * ℓ := by
  obtain ⟨χ, _, hχ, hComp, _, scaled, nested⟩ := exists_nested_patch_cutoffs R hR
  obtain ⟨_, _, oneOnPlateau, support, _, _, _⟩ := scaled (0 : CoordinateSpace) 1 (by norm_num)
  have hSupport : tsupport χ ⊆ ball (0 : CoordinateSpace) (R + 2) := by simpa using support
  have oneOn : ∀ y ∈ closedBall (0 : CoordinateSpace) (R + 1), χ y = 1 := by
    simpa using oneOnPlateau
  obtain ⟨K, hK, estimate⟩ := exists_rescaled_localized_symbol_jet_bound (F := F) (Ω := Ω) χ hχ
    (R + 2) (by linarith) (hSupport.trans ball_subset_closedBall) N
  exact ⟨χ, K, hχ, hComp, hK, hSupport, oneOn, nested, estimate⟩

end Burnett.A03
