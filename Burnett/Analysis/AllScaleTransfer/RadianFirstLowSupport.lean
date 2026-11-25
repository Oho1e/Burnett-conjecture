import Burnett.Analysis.AllScaleTransfer.RadianLowBranchComplete

set_option autoImplicit false
set_option maxHeartbeats 5800000

noncomputable section

namespace Burnett.A05

open MeasureTheory Set
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier
open scoped ContDiff

theorem radianFirstLowRemainder_eq_original
    (χ₀ : ℝ → ℝ) (hχ : χ₀ 0 = 1) (A : E ≃L[ℝ] E) (M₀ m : Joint → ℂ)
    (M : Burnett.Analysis.LowRatio.Point → ℂ) (p : Joint) (hq : p.2 ≠ 0)
    (ang : Burnett.Analysis.LowRatio.Angles)
    (hm : m p = M (ang,‖A p.1‖ / ‖A p.2‖))
    (hM₀ : radianEndpointAngular M₀ p.1 p.2 = Burnett.Analysis.LowRatio.endpoint M ang) :
    radianFirstLowRemainder χ₀ A M₀ m p =
      (‖A p.1‖ / ‖A p.2‖) • Burnett.Analysis.LowRatio.remainder M χ₀
        (ang,‖A p.1‖ / ‖A p.2‖) := by
  rw [radianFirstLowRemainder, if_neg hq]
  exact radianRatioRemainderSymbol_eq_original χ₀ hχ A M₀ m M p ang hm hM₀

theorem radianFirstLowRemainder_homogeneous
    (χ₀ : ℝ → ℝ) (A : E ≃L[ℝ] E) (M₀ m : Joint → ℂ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p)
    (t : ℝ) (ht : 0 < t) (p : Joint) :
    radianFirstLowRemainder χ₀ A M₀ m (t • p) = radianFirstLowRemainder χ₀ A M₀ m p := by
  change (if t • p.2 = 0 then 0 else radianRatioRemainderSymbol χ₀ A M₀ m (t • p)) =
    (if p.2 = 0 then 0 else radianRatioRemainderSymbol χ₀ A M₀ m p)
  have dir (x : E) : ‖t • x‖⁻¹ • (t • x) = ‖x‖⁻¹ • x := by
    rw [norm_smul, Real.norm_of_nonneg ht.le, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ ht.ne',
      mul_one]
  have ratio : ‖A (t • p.1)‖ / ‖A (t • p.2)‖ = ‖A p.1‖ / ‖A p.2‖ := by
    simp only [map_smul,norm_smul,Real.norm_of_nonneg ht.le]
    exact mul_div_mul_left _ _ ht.ne'
  by_cases hq : p.2 = 0
  · simp [hq]
  have hTq : t • p.2 ≠ 0 := smul_ne_zero ht.ne' hq
  rw [if_neg hTq, if_neg hq]
  unfold radianRatioRemainderSymbol radianEndpointAngular
  change m (t • p) - M₀ (‖t • p.1‖⁻¹ • (t • p.1), ‖t • p.2‖⁻¹ • (t • p.2)) *
    (χ₀ (‖A (t • p.1)‖ / ‖A (t • p.2)‖) : ℂ) = _
  rw [hHom t ht p, dir p.1, dir p.2, ratio]

/-- The support of the raw low-ratio difference lies in the same fixed
physical ratio range as the original branch and its cutoff trace. -/
theorem radianRatioRemainderSymbol_support
    (χ₀ : ℝ → ℝ) (A : E ≃L[ℝ] E) (M₀ m : Joint → ℂ)
    (L U u : ℝ) (hL : 0 < L) (hu : 0 ≤ u)
    (hCut : ∀ t, u ≤ t → χ₀ t = 0) (upper : ∀ x, ‖A x‖ ≤ U * ‖x‖)
    (hM : ∀ p : Joint, p.2 ≠ 0 → m p ≠ 0 →
      L * ‖p.1‖ ≤ ‖A p.1‖ ∧ ‖A p.1‖ / ‖A p.2‖ ≤ u)
    (hM₀ : ∀ p : Joint, radianEndpointAngular M₀ p.1 p.2 ≠ 0 → L * ‖p.1‖ ≤ ‖A p.1‖)
    (p : Joint) (hq : p.2 ≠ 0) (hp : radianRatioRemainderSymbol χ₀ A M₀ m p ≠ 0) :
    ‖A p.1‖ / ‖A p.2‖ ≤ u ∧ ‖p.1‖ ≤ (u * U / L) * ‖p.2‖ := by
  have hAq : 0 < ‖A p.2‖ :=
    norm_pos_iff.mpr (fun z => hq (A.injective (z.trans A.map_zero.symm)))
  have haveBound : L * ‖p.1‖ ≤ ‖A p.1‖ ∧ ‖A p.1‖ / ‖A p.2‖ ≤ u := by
    by_cases hmp : m p = 0
    · have he : radianEndpointAngular M₀ p.1 p.2 ≠ 0 := by
        intro z
        exact hp (by simp [radianRatioRemainderSymbol, hmp, z])
      have hc : ‖A p.1‖ / ‖A p.2‖ ≤ u := by
        by_contra! z
        exact hp (by simp [radianRatioRemainderSymbol, hmp, hCut _ z.le])
      exact ⟨hM₀ p he,hc⟩
    · exact hM p hq hmp
  refine ⟨haveBound.2, ?_⟩
  have hb : ‖p.1‖ * L ≤ (u * U) * ‖p.2‖ := by
    calc
      ‖p.1‖ * L = L * ‖p.1‖ := mul_comm _ _
      _ ≤ ‖A p.1‖ := haveBound.1
      _ ≤ u * ‖A p.2‖ := (div_le_iff₀ hAq).mp haveBound.2
      _ ≤ (u * U) * ‖p.2‖ := (mul_le_mul_of_nonneg_left (upper p.2) hu).trans_eq (mul_assoc _ _ _).symm
  convert (le_div_iff₀ hL).mpr hb using 1
  ring

/-- A smaller positive window on which the chosen low cutoff is constant
uses the same one-sided derivatives and the original symbol. -/
theorem oneSided_low_box_restrict {U : Set Burnett.Analysis.LowRatio.Angles}
    (hU : IsOpen U) {b₁ b₂ B : ℝ} (hB : b₁ ≤ b₂)
    (M : Burnett.Analysis.LowRatio.Point → ℂ)
    (hM : ContDiffOn ℝ 100 M (U ×ˢ Ico (0 : ℝ) b₂))
    (hD : ∀ n ≤ 100, ∀ z ∈ U ×ˢ Ico (0 : ℝ) b₂,
      ‖iteratedFDerivWithin ℝ n M (U ×ˢ Ico (0 : ℝ) b₂) z‖ ≤ B) :
    ContDiffOn ℝ 100 M (U ×ˢ Ico (0 : ℝ) b₁) ∧
    ∀ n ≤ 100, ∀ z ∈ U ×ˢ Ico (0 : ℝ) b₁,
      ‖iteratedFDerivWithin ℝ n M (U ×ˢ Ico (0 : ℝ) b₁) z‖ ≤ B := by
  have incl : U ×ˢ Ico (0 : ℝ) b₁ ⊆ U ×ˢ Ico (0 : ℝ) b₂ :=
    fun _ h => ⟨h.1,h.2.1,h.2.2.trans_le hB⟩
  refine ⟨hM.mono incl,?_⟩
  intro n hn z hz
  have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast hn
  rw [iteratedFDerivWithin_subset incl (hU.uniqueDiffOn.prod (uniqueDiffOn_Ico 0 b₁))
    (hU.uniqueDiffOn.prod (uniqueDiffOn_Ico 0 b₂)) (hM.of_le hn') hz]
  exact hD n hn z (incl hz)

/-- Add the endpoint, actual cutoff correction, geometric tail and fixed
transition estimates for the original first-low Fourier multiplier. -/
theorem exists_radianTrilinearForm_first_low_bound (R : ℝ) (hR : 0 < R) :
    ∃ H : ℕ, ∀ (χ₀ : ℝ → ℝ) (_ : Measurable χ₀) (_ : ∀ t ≥ 0, ‖χ₀ t‖ ≤ 1)
      (A : E ≃L[ℝ] E) (gap cutoff : ℕ) (_ : 3 ≤ gap) (m M₀ : Joint → ℂ),
      Measurable m → Measurable M₀ → ∀ B B₀ : ℝ, 0 ≤ B → 0 ≤ B₀ →
      (∀ p, ‖m p‖ ≤ B) → (∀ p, ‖M₀ p‖ ≤ B₀) →
      (∀ p, p.2 ≠ 0 → radianRatioRemainderSymbol χ₀ A M₀ m p ≠ 0 →
        ‖p.1‖ ≤ R * ‖p.2‖) →
      ∀ f g h : SchwartzMap E ℂ,
      let endpoint (p : Joint) := radianEndpointAngular M₀ p.1 p.2 * ∑' j, lowEndpointRadianWindows gap j p
      let correction (p : Joint) := ∑' j, radianLowPassCorrectionBlock χ₀ A gap M₀ j p
      let rem := radianFirstLowRemainder χ₀ A M₀ m
      let T (s : {s : ℕ // cutoff ≤ s}) :=
        radianTrilinearForm (radianLowGapSymbol rem s.val) f g h
      let S (k : ℤ) := radianTrilinearForm (radianSignedGapSymbol rem k) f g h
      let mass := (triLpMass f g h 3 3 3).toReal
      ∀ (D C₁ C₂ C₃ C₄ : ℝ),
      ‖radianTrilinearForm endpoint f g h‖ ≤ C₁*D*mass →
      ‖radianTrilinearForm correction f g h‖ ≤ C₂*D*mass →
      ‖∑' s, T s‖ ≤ C₃*D*mass →
      ‖∑ k ∈ Finset.Icc (-(cutoff : ℤ) + 1) (H : ℤ), S k‖ ≤ C₄*D*mass →
      ‖radianTrilinearForm m f g h‖ ≤ (C₁+C₂+C₃+C₄)*D*mass := by
  obtain ⟨H, decomp⟩ := exists_radianTrilinearForm_first_low_gap_decomposition R hR
  refine ⟨H,?_⟩
  intro χ₀ hχ₀ hχ A gap cutoff hgap m M₀ hm hM₀ B B₀ hB hB₀ bM bM₀ hSupport f g h
    endpoint correction rem T S mass D C₁ C₂ C₃ C₄ e₁ e₂ e₃ e₄
  have e := (decomp χ₀ hχ₀ hχ A gap cutoff hgap m M₀ hm hM₀ B B₀ hB hB₀ bM bM₀ hSupport f g h).2
  rw [e]
  change ‖radianTrilinearForm endpoint f g h + radianTrilinearForm correction f g h +
    ((∑' s, T s) + ∑ k ∈ Finset.Icc (-(cutoff : ℤ) + 1) (H : ℤ), S k)‖ ≤ _
  refine (norm_add_le _ _).trans ?_
  calc
    _ ≤ (‖radianTrilinearForm endpoint f g h‖ + ‖radianTrilinearForm correction f g h‖) +
        (‖∑' s, T s‖ + ‖∑ k ∈ Finset.Icc (-(cutoff : ℤ) + 1) (H : ℤ), S k‖) :=
      add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ ≤ (C₁+C₂+C₃+C₄)*D*mass := by nlinarith only [e₁,e₂,e₃,e₄]

end Burnett.A05
