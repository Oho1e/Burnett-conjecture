-- The annular cutoff and jet argument in the positive ratio window.
import Burnett.Analysis.AllScaleTransfer.FixedAnnularCutoff
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.A05.BoxFourier

open Set Filter Burnett.Analysis
open scoped ContDiff Topology Nat

private theorem norm_pair_jet_eq_max
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {V : Set E} (hV : IsOpen V) {f : E → F} {g : E → G}
    (hf : ContDiffOn ℝ 99 f V) (hg : ContDiffOn ℝ 99 g V)
    {x : E} (hx : x ∈ V) {j : ℕ} (hj : j ≤ 99) :
    ‖iteratedFDeriv ℝ j (fun z => (f z, g z)) x‖ =
      max ‖iteratedFDeriv ℝ j f x‖ ‖iteratedFDeriv ℝ j g x‖ := by
  have hj' : (j : WithTop ℕ∞) ≤ 99 := by exact_mod_cast hj
  have h := ((hf.of_le hj').ftaylorSeriesWithin hV.uniqueDiffOn).prodMk
    ((hg.of_le hj').ftaylorSeriesWithin hV.uniqueDiffOn)
  rw [← iteratedFDerivWithin_of_isOpen j hV hx, ← iteratedFDerivWithin_of_isOpen (f := f) j hV hx,
    ← iteratedFDerivWithin_of_isOpen (f := g) j hV hx,
    ← h.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hV.uniqueDiffOn hx,
    ContinuousMultilinearMap.opNorm_prod]
  rfl

private theorem norm_smul_jet_forty_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {V : Set E}
    (hV : IsOpen V) {f : E → ℝ} {g : E → F}
    (hf : ContDiffOn ℝ 99 f V) (hg : ContDiffOn ℝ 99 g V)
    {x : E} (hx : x ∈ V) {j : ℕ} (hj : j ≤ 40) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (bf : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f x‖ ≤ B)
    (bg : ∀ i ≤ j, ‖iteratedFDeriv ℝ i g x‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun z => f z • g z) x‖ ≤ (2 : ℝ)^40 * B * C := by
  have hj' : (j : WithTop ℕ∞) ≤ 99 := by exact_mod_cast (hj.trans (by decide : 40 ≤ 99))
  rw [← iteratedFDerivWithin_of_isOpen j hV hx]
  refine (norm_iteratedFDerivWithin_smul_le hf hg hV.uniqueDiffOn hx hj').trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B * C := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [iteratedFDerivWithin_of_isOpen i hV hx, iteratedFDerivWithin_of_isOpen (j - i) hV hx]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (bf i hi') (by positivity))
        (bg (j - i) (Nat.sub_le j i)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^j * B * C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      norm_cast
      rw [Nat.sum_range_choose]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hB) hC

/-- Extend the actual remainder from positive ratios on a fixed annular
chart. The gap threshold follows from the unscaled ratio budget and sends
the whole open chart to the positive window. -/
theorem exists_fixed_chart_positive_gap_extension {K V : Set FrequencyPair}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {U : Set LowRatio.Angles} (hU : IsOpen U) (angular : FrequencyPair → LowRatio.Angles)
    (hAngular : ContDiffOn ℝ ∞ angular V) (mapAngular : MapsTo angular V U)
    (B : ℝ) (hB : 0 ≤ B) {b : ℝ} (hb : 0 < b) :
    ∃ (β : FrequencyPair → ℝ) (C : ℝ) (s₀ : ℕ),
      ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ V ∧
      (∀ z ∈ K, β z = 1) ∧ 0 ≤ C ∧
      ∀ (r : FrequencyPair → ℝ) (R : LowRatio.Point → ℂ) (A : ℝ),
        0 ≤ A → ContDiffOn ℝ ∞ r V → (∀ z ∈ V, 0 < r z) →
        (∀ n ≤ 40, ∀ z ∈ V, ‖iteratedFDeriv ℝ n r z‖ ≤ B) →
        ContDiffOn ℝ 99 R (LowRatio.Window U 0 b) →
        (∀ n ≤ 40, ∀ w ∈ LowRatio.Window U 0 b, ‖iteratedFDeriv ℝ n R w‖ ≤ A) →
        ∃ g : ℕ → FrequencyPair → ℂ,
          (∀ s, ContDiff ℝ 99 (g s) ∧ tsupport (g s) ⊆ tsupport β) ∧
          (∀ s n, n ≤ 40 → ∀ z, ‖iteratedFDeriv ℝ n (g s) z‖ ≤ (C * A) * radialGapDecay s) ∧
          (∀ s, s₀ ≤ s → ∀ z ∈ V, radialGapDecay s * r z ∈ Ioo (0 : ℝ) b) ∧
          ∀ s, s₀ ≤ s → ∀ z ∈ K, g s z =
            (radialGapDecay s * r z) • R (angular z, radialGapDecay s * r z) := by
  have hOrder : (99 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  let W := LowRatio.Window U 0 b
  have hW : IsOpen W := hU.prod isOpen_Ioo
  obtain ⟨β, sβ, cβ, tβ, oneβ⟩ := exists_fixed_annular_cutoff hK hV hKV
  obtain ⟨Kβ, hKβ, bβ⟩ :=
    exists_compact_contDiffOn_jet_bound cβ isOpen_univ (subset_univ _) sβ.contDiffOn 40
  obtain ⟨Kang, _, bang⟩ :=
    exists_compact_contDiffOn_jet_bound cβ hV tβ hAngular 40
  let D := max 1 (max Kang B)
  have hD : 1 ≤ D := le_max_left _ _
  have hDn : 0 ≤ D := zero_le_one.trans hD
  have lim : Tendsto (fun s : ℕ => radialGapDecay s * B) atTop (𝓝 0) := by
    simpa only [radialGapDecay, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const B
  obtain ⟨s₀, hSmall⟩ := eventually_atTop.mp (lim.eventually (gt_mem_nhds hb))
  let C : ℝ := 2^40 * (2^40 * Kβ * B) * ((40 ! : ℕ) * D^40)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨β, C, s₀, sβ, cβ, tβ, oneβ, hC, ?_⟩
  intro r R A hA sr rn br sR bR
  let ρ (s : ℕ) (z : FrequencyPair) := radialGapDecay s * r z
  let Θ (s : ℕ) (z : FrequencyPair) : LowRatio.Point := (angular z, ρ s z)
  let f (s : ℕ) (z : FrequencyPair) := β z • (r z • R (Θ s z))
  let g (s : ℕ) : FrequencyPair → ℂ := if s₀ ≤ s then (radialGapDecay s) • f s else 0
  have hGapPos (s : ℕ) : 0 < radialGapDecay s := by unfold radialGapDecay; positivity
  have hGap (s : ℕ) : 0 ≤ radialGapDecay s := (hGapPos s).le
  have gap_le_one (s : ℕ) : radialGapDecay s ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have smooth_ρ (s : ℕ) : ContDiffOn ℝ 99 (ρ s) V :=
    contDiffOn_const.mul (sr.of_le hOrder)
  have mapΘ (s : ℕ) (hs : s₀ ≤ s) : MapsTo (Θ s) V W := by
    intro z hz
    have hzB : r z ≤ B := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (rn z hz).le] using br 0 (by decide) z hz
    refine ⟨mapAngular hz, mul_pos (hGapPos s) (rn z hz), ?_⟩
    exact (mul_le_mul_of_nonneg_left hzB (hGap s)).trans_lt (hSmall s hs)
  have smooth_Θ (s : ℕ) : ContDiffOn ℝ 99 (Θ s) V :=
    (hAngular.of_le hOrder).prodMk (smooth_ρ s)
  have smoothF (s : ℕ) (hs : s₀ ≤ s) : ContDiff ℝ 99 (f s) := by
    have localSmooth : ContDiffOn ℝ 99 (f s) V :=
      ((sβ.of_le hOrder).contDiffOn).smul ((sr.of_le hOrder).smul
        (sR.comp (smooth_Θ s) (mapΘ s hs)))
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ V
    · exact localSmooth.contDiffAt (hV.mem_nhds hz)
    · have hEvent : f s =ᶠ[𝓝 z] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (tβ h))] with y hy
        change β y = 0 at hy
        simp [f, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hEvent
  have suppF (s : ℕ) : tsupport (f s) ⊆ tsupport β := tsupport_smul_subset_left _ _
  have budgetF (s : ℕ) (hs : s₀ ≤ s) {n : ℕ} (hn : n ≤ 40) (z : FrequencyPair) :
      ‖iteratedFDeriv ℝ n (f s) z‖ ≤ C * A := by
    by_cases hz : z ∈ tsupport β
    · have hzV : z ∈ V := tβ hz
      have sComp := sR.comp (smooth_Θ s) (mapΘ s hs)
      have bρ (j : ℕ) (hj : j ≤ 40) : ‖iteratedFDeriv ℝ j (ρ s) z‖ ≤ B := by
        have hj' : (j : WithTop ℕ∞) ≤ ∞ := by
          exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
        change ‖iteratedFDeriv ℝ j (fun w => radialGapDecay s • r w) z‖ ≤ B
        rw [iteratedFDeriv_const_smul_apply' (a := radialGapDecay s)
          ((sr.of_le hj').contDiffAt (hV.mem_nhds hzV)), norm_smul, Real.norm_of_nonneg (hGap s)]
        exact (mul_le_mul_of_nonneg_left (br j hj z hzV) (hGap s)).trans
          (mul_le_of_le_one_left hB (gap_le_one s))
      have bΘ (j : ℕ) (hj : j ≤ 40) (jpos : 1 ≤ j) :
          ‖iteratedFDeriv ℝ j (Θ s) z‖ ≤ D^j := by
        rw [norm_pair_jet_eq_max hV (hAngular.of_le hOrder) (smooth_ρ s) hzV
          (hj.trans (by decide : 40 ≤ 99))]
        exact (max_le_max (bang j hj z hz) (bρ j hj)).trans
          ((le_max_right 1 (max Kang B)).trans (by
            calc
              D = D^1 := (pow_one _).symm
              _ ≤ D^j := pow_le_pow_right₀ hD jpos))
      have bComp (j : ℕ) (hj : j ≤ 40) : ‖iteratedFDeriv ℝ j (R ∘ Θ s) z‖ ≤
          ((40 ! : ℕ) : ℝ) * D^40 * A := by
        have hj' : (j : WithTop ℕ∞) ≤ 99 := by exact_mod_cast (hj.trans (by decide : 40 ≤ 99))
        have h := norm_iteratedFDerivWithin_comp_le sR (smooth_Θ s) hj'
          hW.uniqueDiffOn hV.uniqueDiffOn (mapΘ s hs) hzV
          (C := A) (D := D)
          (fun i hi => by
            rw [iteratedFDerivWithin_of_isOpen i hW (mapΘ s hs hzV)]
            exact bR i (hi.trans hj) _ (mapΘ s hs hzV))
          (fun i hpos hi => by
            rw [iteratedFDerivWithin_of_isOpen i hV hzV]
            exact bΘ i (hi.trans hj) hpos)
        rw [iteratedFDerivWithin_of_isOpen j hV hzV] at h
        calc
          _ ≤ (j ! : ℕ) * A * D^j := h
          _ ≤ ((40 ! : ℕ) : ℝ) * A * D^40 := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hA)
              (pow_le_pow_right₀ hD hj) (pow_nonneg hDn _) (by positivity)
          _ = _ := by ring
      have bMid (j : ℕ) (hj : j ≤ 40) : ‖iteratedFDeriv ℝ j (fun w => r w • R (Θ s w)) z‖ ≤
          (2 : ℝ)^40 * B * (((40 ! : ℕ) : ℝ) * D^40 * A) :=
        norm_smul_jet_forty_le hV (sr.of_le hOrder) sComp hzV hj hB
          (by positivity) (fun i hi => br i (hi.trans hj) z hzV)
          (fun i hi => bComp i (hi.trans hj))
      have bProd := norm_smul_jet_forty_le hV ((sβ.of_le hOrder).contDiffOn)
        ((sr.of_le hOrder).smul sComp) hzV hn hKβ
        (show 0 ≤ (2 : ℝ)^40 * B * (((40 ! : ℕ) : ℝ) * D^40 * A) by positivity)
        (fun i hi => bβ i (hi.trans hn) z hz) (fun i hi => bMid i (hi.trans hn))
      convert bProd using 1
      dsimp [C]
      ring
    · have h0 : iteratedFDeriv ℝ n (f s) z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hz (suppF s (tsupport_iteratedFDeriv_subset n h)))
      rw [h0, norm_zero]
      exact mul_nonneg hC hA
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro s
    by_cases hs : s₀ ≤ s
    · dsimp only [g]
      rw [if_pos hs]
      exact ⟨contDiff_const.smul (smoothF s hs),
        (tsupport_smul_subset_right (fun _ : FrequencyPair => radialGapDecay s) (f s)).trans (suppF s)⟩
    · dsimp only [g]
      rw [if_neg hs]
      exact ⟨contDiff_const, by simp only [tsupport, Function.support_zero, closure_empty, empty_subset]⟩
  · intro s n hn z
    by_cases hs : s₀ ≤ s
    · have hn' : (n : WithTop ℕ∞) ≤ 99 := by exact_mod_cast (hn.trans (by decide : 40 ≤ 99))
      dsimp only [g]
      rw [if_pos hs]
      change ‖iteratedFDeriv ℝ n (fun x => radialGapDecay s • f s x) z‖ ≤ _
      rw [iteratedFDeriv_const_smul_apply' (a := radialGapDecay s)
        ((smoothF s hs).contDiffAt.of_le hn'), norm_smul, Real.norm_of_nonneg (hGap s)]
      exact (mul_le_mul_of_nonneg_left (budgetF s hs hn z) (hGap s)).trans_eq (mul_comm _ _)
    · dsimp only [g]
      rw [if_neg hs]
      change ‖iteratedFDeriv ℝ n (fun _ : FrequencyPair => (0 : ℂ)) z‖ ≤ _
      rw [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
      exact mul_nonneg (mul_nonneg hC hA) (hGap s)
  · exact fun s hs z hz => (mapΘ s hs hz).2
  · intro s hs z hz
    simp [g, hs, f, oneβ z hz, Θ, ρ, mul_assoc]

end Burnett.A05.BoxFourier
