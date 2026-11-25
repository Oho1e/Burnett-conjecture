import Burnett.Analysis.AllScaleTransfer.SignedRadianGapSeries

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.A05

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight
  radialAnnularCutoff_nonzero)

/-- An upper ratio bound on the original symbol gives a uniform upper
bound on the signed gaps that can contribute to the two-window partition. -/
theorem exists_radianSignedGapSymbol_upper (R : ℝ) (hR : 0 < R) :
    ∃ H : ℕ, ∀ (m : Joint → ℂ), (∀ p, m p ≠ 0 → ‖p.1‖ ≤ R * ‖p.2‖) →
      ∀ k : ℤ, (H : ℤ) < k → radianSignedGapSymbol m k = 0 := by
  obtain ⟨H, hH⟩ := pow_unbounded_of_one_lt (4 * R) (show (1 : ℝ) < 2 by norm_num)
  have hH' : 4 * R < (2 : ℝ)^(H : ℤ) := by rw [zpow_natCast]; exact hH
  refine ⟨H, ?_⟩
  intro m hSupport k hk
  funext p
  by_cases hm : m p = 0
  · simp [radianSignedGapSymbol, hm]
  have hZero (j : ℤ) : integerRadialWindow (j + k) p.1 * integerRadialWindow j p.2 = 0 := by
    by_contra hn
    have hLow : integerRadialWindow (j + k) p.1 ≠ 0 :=
      fun h => hn (by rw [h, zero_mul])
    have hHigh : integerRadialWindow j p.2 ≠ 0 := fun h => hn (by rw [h, mul_zero])
    have hLow' := (radialAnnularCutoff_nonzero (by positivity : 0 < (2 : ℝ)^(j + k)) hLow).1
    have hHigh' := (radialAnnularCutoff_nonzero (by positivity : 0 < (2 : ℝ)^j) hHigh).2
    have highPow : 0 < (2 : ℝ)^j := by positivity
    have large : (2 : ℝ)^j * (4 * R) < (2 : ℝ)^j * (2 : ℝ)^k :=
      mul_lt_mul_of_pos_left
        (hH'.trans (zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) hk)) highPow
    have support := hSupport p hm
    have highRatio := mul_lt_mul_of_pos_left hHigh' hR
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] at hLow'
    nlinarith only [hLow', support, highRatio, large]
  simp only [radianSignedGapSymbol, hZero, tsum_zero, Complex.ofReal_zero, zero_mul, Pi.zero_apply]

/-- The original remainder form is the sum of the genuine large-gap tail
and a fixed finite list of signed transition forms. Only an upper ratio
bound is needed for the original symbol. -/
theorem exists_radianTrilinearForm_remainder_gap_split (R : ℝ) (hR : 0 < R) :
    ∃ H : ℕ, ∀ (cutoff : ℕ) (m : Joint → ℂ), AEStronglyMeasurable m volume →
      ∀ (B : ℝ), 0 ≤ B → (∀ p, ‖m p‖ ≤ B) →
      (∀ p, m p ≠ 0 → ‖p.1‖ ≤ R * ‖p.2‖) → ∀ (f g h : SchwartzMap E ℂ),
      let T (s : {s : ℕ // cutoff ≤ s}) :=
        radianTrilinearForm (radianLowGapSymbol m s.val) f g h
      Summable T ∧ radianTrilinearForm m f g h =
        (∑' s, T s) + ∑ k ∈ Finset.Icc (-(cutoff : ℤ) + 1) (H : ℤ),
          radianTrilinearForm (radianSignedGapSymbol m k) f g h := by
  obtain ⟨H, hUpper⟩ := exists_radianSignedGapSymbol_upper R hR
  refine ⟨H, ?_⟩
  intro cutoff m hm B hB hNorm hSupport f g h T
  let S := {s : ℕ // cutoff ≤ s}
  let I := Finset.Icc (-(cutoff : ℤ) + 1) (H : ℤ)
  let F (k : ℤ) := radianTrilinearForm (radianSignedGapSymbol m k) f g h
  let e : S ⊕ (↑I : Type) → ℤ := Sum.elim (fun s : S => -(s.val : ℤ)) Subtype.val
  have he : Function.Injective e := by
    intro a b eq
    cases a with
    | inl s =>
      cases b with
      | inl t =>
        change -(s.val : ℤ) = -(t.val : ℤ) at eq
        exact congrArg Sum.inl (Subtype.ext (by omega))
      | inr k =>
        change -(s.val : ℤ) = k.val at eq
        have hs : cutoff ≤ s.val := s.property
        have hk := (Finset.mem_Icc.mp k.property).1
        omega
    | inr k =>
      cases b with
      | inl s =>
        change k.val = -(s.val : ℤ) at eq
        have hs : cutoff ≤ s.val := s.property
        have hk := (Finset.mem_Icc.mp k.property).1
        omega
      | inr l =>
        change k.val = l.val at eq
        exact congrArg Sum.inr (Subtype.ext eq)
  have hOutside (k : ℤ) (hk : k ∉ Set.range e) : F k = 0 := by
    by_cases hSmall : k ≤ -(cutoff : ℤ)
    · have hk0 : 0 ≤ -k := by omega
      let s := (-k).toNat
      have hs : (s : ℤ) = -k := Int.toNat_of_nonneg hk0
      have hCut : cutoff ≤ s := by omega
      exact (hk ⟨Sum.inl ⟨s, hCut⟩, by change -(s : ℤ) = k; omega⟩).elim
    · have hBig : (H : ℤ) < k := by
        by_contra! h
        have hMem : k ∈ I := Finset.mem_Icc.mpr ⟨by omega, h⟩
        exact hk ⟨Sum.inr ⟨k, hMem⟩, rfl⟩
      unfold F
      rw [hUpper m hSupport k hBig]
      simp [radianTrilinearForm, radianTrilinearWeight]
  have hAll : HasSum F (radianTrilinearForm m f g h) :=
    radianTrilinearForm_hasSum_signed_gaps m hm B hB hNorm f g h
  have hSplit : HasSum (F ∘ e) (radianTrilinearForm m f g h) :=
    (he.hasSum_iff hOutside).mpr hAll
  have hTail : Summable ((F ∘ e) ∘ Sum.inl) :=
    hSplit.summable.comp_injective Sum.inl_injective
  have hTransition : Summable ((F ∘ e) ∘ Sum.inr) := Summable.of_finite
  have hEq := hSplit.tsum_eq.symm.trans (hTail.tsum_sum hTransition)
  have hTailEq (s : S) : (F ∘ e) (Sum.inl s) = T s := by
    change radianTrilinearForm (radianSignedGapSymbol m (-(s.val : ℤ))) f g h = _
    rw [radianSignedGapSymbol_neg_nat]
  have hTransitionEq : (∑' k : (↑I : Type), (F ∘ e) (Sum.inr k)) =
      ∑ k ∈ I, F k := by
    rw [tsum_fintype]
    change (∑ k ∈ I.attach, F k) = _
    rw [Finset.sum_attach I F]
  have hT : ((F ∘ e) ∘ Sum.inl) = T := funext hTailEq
  refine ⟨hT ▸ hTail, ?_⟩
  rw [hEq, hTransitionEq]
  exact congrArg (fun z => z + ∑ k ∈ I, F k) (tsum_congr hTailEq)

end Burnett.A05
