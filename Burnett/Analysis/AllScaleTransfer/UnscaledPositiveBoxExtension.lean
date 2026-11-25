import Burnett.Analysis.AllScaleTransfer.PositiveActualCapBoxExtension

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric Burnett.Analysis CapFourier
open scoped ContDiff

private theorem compact_radialJetAnnulus (lo hi : ℝ) :
    IsCompact (radialJetAnnulus lo hi : Set Frequency) :=
  (isCompact_closedBall (0 : Frequency) hi).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    (fun _ hp => mem_closedBall_zero_iff.mpr hp.2)

/-- The unscaled positive-ratio remainder on a fixed annular chart has
the same box extension and geometric derivative bounds as the cap chart. -/
theorem exists_unscaled_positive_annular_box_extension
    {lo hi : ℝ} (hlo : 0 < lo)
    {K V : Set FrequencyPair} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (hAnn : V ⊆ radialJetAnnulus lo hi ×ˢ radialJetAnnulus lo hi)
    {U : Set LowRatio.Angles} (hU : IsOpen U)
    (angular : FrequencyPair → LowRatio.Angles)
    (hAngular : ContDiffOn ℝ ∞ angular V) (hMap : MapsTo angular V U)
    {b : ℝ} (hb : 0 < b) (χ₀ : ℝ → ℝ) (oneχ₀ : χ₀ 0 = 1)
    (plateau : ∀ ρ ∈ Ioo (0 : ℝ) b, χ₀ ρ = 1) :
    ∃ (C : ℝ) (s₀ : ℕ), 0 ≤ C ∧
      ∀ (M : LowRatio.Point → ℂ) (A : ℝ), 0 ≤ A →
      ContDiffOn ℝ 100 M (U ×ˢ Ico (0 : ℝ) b) →
      (∀ n ≤ 100, ∀ z ∈ U ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n M (U ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) →
      ∃ g : ℕ → BoxSpace → ℂ,
        (∀ s, ContDiff ℝ 99 (g s)) ∧
        (∀ s n, n ≤ 40 → ∀ z, ‖iteratedFDeriv ℝ n (g s) z‖ ≤ (C * A) * radialGapDecay s) ∧
        (∀ s, s₀ ≤ s → ∀ ζ υ : Frequency, (ζ,υ) ∈ K →
          g s (joinedInputs ζ υ) =
            normalizedGapRemainder (ContinuousLinearEquiv.refl ℝ Frequency) (angular ∘ boxToPair)
              M χ₀ s (joinedInputs ζ υ)) ∧
        ∀ s, s₀ ≤ s → ∀ ζ υ : Frequency, (ζ,υ) ∈ V →
          gapRatio (ContinuousLinearEquiv.refl ℝ Frequency) s ζ υ ∈ Ioo (0 : ℝ) b := by
  let I := ContinuousLinearEquiv.refl ℝ Frequency
  let r := physicalRadialRatio I.toContinuousLinearMap
  let O : Set FrequencyPair := {pq | pq.1 ≠ 0} ∩ {pq | pq.2 ≠ 0}
  have hO : IsOpen O := (isOpen_ne_fun continuous_fst continuous_const).inter
    (isOpen_ne_fun continuous_snd continuous_const)
  have inside : radialJetAnnulus lo hi ×ˢ radialJetAnnulus lo hi ⊆ O := by
    intro pq hp
    exact ⟨norm_pos_iff.mp (hlo.trans_le hp.1.1),norm_pos_iff.mp (hlo.trans_le hp.2.1)⟩
  have smooth : ContDiffOn ℝ ∞ r O := by
    intro pq h
    exact (physicalRadialRatio_contDiffAt I.toContinuousLinearMap h.1 h.2).contDiffWithinAt
  have hCompact := (compact_radialJetAnnulus lo hi).prod (compact_radialJetAnnulus lo hi)
  obtain ⟨B,hB,hRatio⟩ := exists_compact_contDiffOn_jet_bound hCompact hO inside smooth 40
  obtain ⟨β,C₀,s₀,_,_,_,_,hC₀,H⟩ :=
    exists_fixed_chart_positive_gap_extension hK hV hKV hU angular hAngular hMap B hB hb
  let D := max 1 ‖boxToPair.toContinuousLinearMap‖
  have hD : 1 ≤ D := le_max_left _ _
  let C := C₀ * D^40
  refine ⟨C,s₀,by unfold C; positivity,?_⟩
  intro M A hA hM hJet
  obtain ⟨hR,hRj⟩ := LowRatio.remainder_jets_of_oneSidedC100 hU M χ₀ oneχ₀ plateau hM A hJet
  have pos (z : FrequencyPair) (hz : z ∈ V) : 0 < r z := by
    have h := inside (hAnn hz)
    exact div_pos (norm_pos_iff.mpr h.1) (norm_pos_iff.mpr h.2)
  obtain ⟨g,hg,hgj,hPositive,hEq⟩ := H r (LowRatio.remainder M χ₀) A hA
    (smooth.mono (hAnn.trans inside)) pos (fun n hn z hz => hRatio n hn z (hAnn hz)) hR
    (fun n hn z hz => hRj n (hn.trans (by decide : 40 ≤ 99)) z hz)
  let G (s : ℕ) := g s ∘ boxToPair
  refine ⟨G,fun s => (hg s).1.comp boxToPair.contDiff,?_,?_,?_⟩
  · intro s n hn z
    have hn' : (n : WithTop ℕ∞) ≤ 99 := by exact_mod_cast hn.trans (by decide : 40 ≤ 99)
    change ‖iteratedFDeriv ℝ n (g s ∘ boxToPair.toContinuousLinearMap) z‖ ≤ _
    rw [boxToPair.toContinuousLinearMap.iteratedFDeriv_comp_right (hg s).1 z hn']
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ ≤ ((C₀ * A) * radialGapDecay s) * ‖boxToPair.toContinuousLinearMap‖^n :=
        mul_le_mul_of_nonneg_right (hgj s n hn (boxToPair z)) (pow_nonneg (norm_nonneg _) _)
      _ ≤ ((C₀ * A) * radialGapDecay s) * D^40 := by
        apply mul_le_mul_of_nonneg_left _ (by unfold radialGapDecay; positivity)
        exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) n).trans (pow_le_pow_right₀ hD hn)
      _ = _ := by unfold C; ring
  · intro s hs ζ υ hp
    change g s (boxToPair (joinedInputs ζ υ)) = _
    rw [boxToPair_joined, hEq s hs (ζ,υ) hp]
    simp only [normalizedGapRemainder, firstInput_joined, secondInput_joined, gapRatio, r,
      physicalRadialRatio, Function.comp_apply, boxToPair_joined]
    rfl
  · intro s hs ζ υ hp
    exact hPositive s hs (ζ,υ) hp

end Burnett.A05.BoxFourier
