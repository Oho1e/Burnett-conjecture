import Burnett.Analysis.AllScaleTransfer.SphereAtlas
import Burnett.Analysis.AllScaleTransfer.RadianFactorwiseTruncation

set_option autoImplicit false
set_option maxRecDepth 8400
set_option maxHeartbeats 9000000

noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory Burnett.A05 Burnett.A05.BoxFourier
open Burnett.A02.FrequencySplit (E Joint triLpMass)
open Burnett.Analysis CapFourier ProjectiveNullCaps
open Burnett.Analysis.LowRatio (Point)
open scoped ContDiff

/-- The unscaled all-scale estimate on the eight signed sphere charts
with the same constant for the full form and every finite factorwise
dyadic truncation. The three low-slot traces are taken at ratio zero. -/
theorem exists_wardUnscaledTrilinearForm_full_truncated_bound
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ b : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 7*κ/4 < b) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : Joint → ℂ) (B : ℝ), 0 ≤ B → Measurable m → (∀ p, ‖m p‖ ≤ B) →
      (∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p) →
      ∀ D : ℝ, 0 ≤ D →
      let low (i : Fin 3) := radianFourBranchSymbol ϑ κ (radianLowSlotView m i) 0
      let comparable := radianFourBranchSymbol ϑ κ m 3
      (∀ slot : Fin 3, ∃ (M : WardPairChart → Point → ℂ) (M₀ : Joint → ℂ),
        (∀ i, ContDiffOn ℝ 100 (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b)) ∧
        (∀ i n, n ≤ 100 → ∀ z ∈ wardPairChartDomain i ×ˢ Ico (0 : ℝ) b,
          ‖iteratedFDerivWithin ℝ n (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b) z‖ ≤ D) ∧
        (∀ i pq, pq ∈ wardPairChartAnnulus i →
          M₀ (endpointDirection pq.1,endpointDirection pq.2) = M i (wardPairChartAngles i pq,0)) ∧
        ∀ i pq, pq ∈ wardPairChartAnnulus i → ∀ t : ℝ, 0 < t →
          let ρ := t*(‖pq.1‖/‖pq.2‖)
          ρ ∈ Ioo (0 : ℝ) b → low slot (t • pq.1,pq.2) = M i (wardPairChartAngles i pq,ρ)) →
      (∃ G : ℤ → BoxSpace → ℂ,
        let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
        (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) 5)) ∧
        (∀ k ∈ I, ∀ n ≤ 100, ∀ z ∈ ball (0 : BoxSpace) 5, ‖iteratedFDeriv ℝ n (G k) z‖ ≤ D) ∧
        ∀ k ∈ I, ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
          G k (joinedInputs ζ υ) = comparable ((2 : ℝ)^k • ζ,υ)) →
      (∀ f g h : SchwartzMap E ℂ, ‖radianTrilinearForm m f g h‖ ≤ C*D*(triLpMass f g h 3 3 3).toReal) ∧
      ∀ (I J L : Finset ℤ) (a b' c : ℤ → ℂ),
        (∀ j ∈ I, ‖a j‖ ≤ 1) → (∀ j ∈ J, ‖b' j‖ ≤ 1) → (∀ j ∈ L, ‖c j‖ ≤ 1) →
        ∀ f g h : SchwartzMap E ℂ,
          ‖radianTrilinearForm m (finiteIntegerRadialTruncation I a f)
            (finiteIntegerRadialTruncation J b' g) (finiteIntegerRadialTruncation L c h)‖ ≤
              C*D*(triLpMass f g h 3 3 3).toReal := by
  let χ := descendingProfile κ (7*κ/4)
  have hχGap : κ < 7*κ/4 := by linarith only [hκ]
  have hχRange : ∀ t ≥ 0, ‖χ t‖ ≤ 1 := by
    intro t _
    have h := descendingProfile_range κ (7*κ/4) t
    rw [Real.norm_of_nonneg h.1]
    exact h.2
  obtain ⟨N,C,hC,full⟩ := exists_unscaled_radianTrilinearForm_bound
    wardPairChartAnnulus wardPairChartDomain wardPairChartAngles wardPairChartAnnulus_open wardPairChartDomain_open
    wardPairChartAnnulus_covers wardPairChartAnnulus_subset wardPairChartAngles_smooth wardPairChartAngles_mapsTo
    ϑ hϑ.continuous.measurable hRange hCut hFlat κ hκ hκsmall κ b hκ hb
    χ (descendingProfile_contDiff _ _) hχRange
    (fun t _ ht => descendingProfile_eq_one hχGap ht) (fun t ht => descendingProfile_eq_zero hχGap ht)
  obtain ⟨T,hT,trunc⟩ := exists_radianTrilinearForm_factorwise_truncation_bound
  refine ⟨N,(1+T)*C,by positivity,?_⟩
  intro m B hB hm hMag hHom D hD low comparable lowProfiles boxProfiles
  obtain ⟨G,hSmooth,hBound,hSource⟩ := boxProfiles
  have e := full m B hB hm hMag hHom D hD lowProfiles
    ⟨G,hSmooth,(fun k hk n hn => hBound k hk n (hn.trans (by decide))),hSource⟩
  have hCD : 0 ≤ C*D := mul_nonneg hC hD
  have fullCoeff : C*D ≤ ((1+T)*C)*D := calc
    _ = 1*(C*D) := (one_mul _).symm
    _ ≤ (1+T)*(C*D) := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hT) hCD
    _ = _ := by ring
  have truncCoeff : T*(C*D) ≤ ((1+T)*C)*D :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hCD).trans_eq (by ring)
  refine ⟨fun f g h => (e f g h).trans (mul_le_mul_of_nonneg_right fullCoeff (by positivity)),?_⟩
  intro I J L a b' c ha hb' hc f g h
  exact (trunc m (C*D) hCD e I J L a b' c ha hb' hc f g h).trans
    (mul_le_mul_of_nonneg_right truncCoeff (by positivity))

end Burnett.C02
