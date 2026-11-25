import Burnett.Analysis.AllScaleTransfer.PositiveRatioTrace
import Burnett.Analysis.AllScaleTransfer.FixedAnnularCutoff

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric Filter Nat Burnett.Analysis
open scoped ContDiff Topology

theorem fixedShift_norm_smul_jet_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {V : Set E} (hV : IsOpen V)
    {f : E → ℝ} {g : E → F}
    (hf : ContDiffOn ℝ 100 f V) (hg : ContDiffOn ℝ 100 g V)
    {z : E} (hz : z ∈ V) {n : ℕ} (hn : n ≤ 40) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (bf : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f z‖ ≤ B)
    (bg : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g z‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun x => f x • g x) z‖ ≤ (2 : ℝ)^40 * B * C := by
  have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (hn.trans (by decide : 40 ≤ 100))
  rw [← iteratedFDerivWithin_of_isOpen n hV hz]
  refine (norm_iteratedFDerivWithin_smul_le hf hg hV.uniqueDiffOn hz hn').trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B * C := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [iteratedFDerivWithin_of_isOpen i hV hz, iteratedFDerivWithin_of_isOpen (n - i) hV hz]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (bf i hi') (by positivity))
        (bg (n - i) (Nat.sub_le n i)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^n * B * C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      norm_cast
      rw [Nat.sum_range_choose]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hB) hC

private theorem snd_cutoff_jet {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (z : LowRatio.Point) :
    ‖iteratedFDeriv ℝ n (fun x : LowRatio.Point => f x.2) z‖ ≤
      ‖iteratedFDeriv ℝ n f z.2‖ := by
  let L := ContinuousLinearMap.snd ℝ LowRatio.Angles ℝ
  change ‖iteratedFDeriv ℝ n (f ∘ L) z‖ ≤ ‖iteratedFDeriv ℝ n f (L z)‖
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
  rw [L.iteratedFDeriv_comp_right hf z hn]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change ‖p.2‖ ≤ 1 * ‖p‖
    rw [one_mul, Prod.norm_def]
    exact le_max_right _ _
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

/-- The original positive-ratio product ρ R, evaluated by its numerator.
The auxiliary cutoff confines evaluation to the one-sided chart. -/
def cutoffRemainderNumerator (M : LowRatio.Point → ℂ) (χ η : ℝ → ℝ)
    (z : LowRatio.Point) : ℂ :=
  η z.2 • (M z - χ z.2 • M (z.1, 0))

/-- At finite signed gaps the undivided numerator retains the original
C100 regularity. The fixed ratio cutoff is one on the full active range
and has support strictly below the upper bound of the source window. -/
theorem exists_cutoffRemainderNumerator_jets {U : Set LowRatio.Angles} (hU : IsOpen U)
    {u b : ℝ} (hu : 0 < u) (hub : u < b) (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ∃ (η : ℝ → ℝ) (C : ℝ), ContDiff ℝ ∞ η ∧ 0 ≤ C ∧
      (∀ r ∈ Icc 0 u, η r = 1) ∧ (∀ r, b ≤ r → η r = 0) ∧
      ∀ (M : LowRatio.Point → ℂ) (A : ℝ), 0 ≤ A →
        ContDiffOn ℝ 100 M (U ×ˢ Ico 0 b) →
        (∀ n ≤ 100, ∀ z ∈ U ×ˢ Ico 0 b,
          ‖iteratedFDerivWithin ℝ n M (U ×ˢ Ico 0 b) z‖ ≤ A) →
        ContDiffOn ℝ 100 (cutoffRemainderNumerator M χ η) (U ×ˢ Ioi 0) ∧
        ∀ n ≤ 40, ∀ z ∈ U ×ˢ Ioi 0,
          ‖iteratedFDeriv ℝ n (cutoffRemainderNumerator M χ η) z‖ ≤ C * A := by
  let rOut : ℝ := (u+b)/2
  have hout : u < rOut := by dsimp [rOut]; linarith
  have hOutB : rOut < b := by dsimp [rOut]; linarith
  let η : ContDiffBump (0 : ℝ) := ⟨u,rOut,hu,hout⟩
  have sη : ContDiff ℝ ∞ (η : ℝ → ℝ) := η.contDiff
  have zeroη (r : ℝ) (hr : rOut ≤ r) : η r = 0 := by
    apply η.zero_of_le_dist
    rw [dist_zero_right, Real.norm_of_nonneg ((hu.trans hout).le.trans hr)]
    exact hr
  have oneη (r : ℝ) (hr : r ∈ Icc 0 u) : η r = 1 := by
    apply η.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff, Real.norm_of_nonneg hr.1]
    exact hr.2
  obtain ⟨Jχ, hJχ, bχ⟩ := exists_compact_contDiffOn_jet_bound
    (K := Icc 0 b) isCompact_Icc isOpen_univ (subset_univ _) hχ.contDiffOn 40
  obtain ⟨Jη, hJη, bη⟩ := exists_compact_contDiffOn_jet_bound
    (K := Icc 0 b) isCompact_Icc isOpen_univ (subset_univ _) sη.contDiffOn 40
  let C := (2 : ℝ)^40 * Jη * (1 + (2 : ℝ)^40 * Jχ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨η,C,sη,hC,oneη,fun r hr => zeroη r (hOutB.le.trans hr),?_⟩
  intro M A hA sM bM
  let W := LowRatio.Window U 0 b
  let S := U ×ˢ Ico 0 b
  have hW : IsOpen W := hU.prod isOpen_Ioo
  have hWS : W ⊆ S := fun _ hz => ⟨hz.1,hz.2.1.le,hz.2.2⟩
  let f := cutoffRemainderNumerator M χ η
  let q : LowRatio.Point → ℂ := fun z => χ z.2 • LowRatio.zeroRatioTraceExtension M z
  let N : LowRatio.Point → ℂ := M - q
  have sMW : ContDiffOn ℝ 100 M W := sM.mono hWS
  have bMW (n : ℕ) (hn : n ≤ 40) (z : LowRatio.Point) (hz : z ∈ W) :
      ‖iteratedFDeriv ℝ n M z‖ ≤ A := by
    have H := bM n (hn.trans (by decide : 40 ≤ 100)) z (hWS hz)
    rw [← iteratedFDerivWithin_inter_open hW hz, inter_eq_right.mpr hWS,
      iteratedFDerivWithin_of_isOpen n hW hz] at H
    exact H
  obtain ⟨sTrace,bTrace⟩ := LowRatio.zeroRatioTraceExtension_jets_of_oneSidedC100
    hU (hu.trans hub) 0 b M A hA sM bM
  have hOrder : (100 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have sχW : ContDiffOn ℝ 100 (fun z : LowRatio.Point => χ z.2) W :=
    ((hχ.of_le hOrder).comp contDiff_snd).contDiffOn
  have sηW : ContDiffOn ℝ 100 (fun z : LowRatio.Point => η z.2) W :=
    ((sη.of_le hOrder).comp contDiff_snd).contDiffOn
  have sq : ContDiffOn ℝ 100 q W := sχW.smul sTrace
  have sN : ContDiffOn ℝ 100 N W := sMW.sub sq
  have sf : ContDiffOn ℝ 100 f W := sηW.smul sN
  have eventZero (z : LowRatio.Point) (hz : b ≤ z.2) : f =ᶠ[𝓝 z] 0 := by
    have hOpen : IsOpen {z : LowRatio.Point | rOut < z.2} := isOpen_lt continuous_const continuous_snd
    filter_upwards [hOpen.mem_nhds (hOutB.trans_le hz)] with y hy
    change rOut < y.2 at hy
    simp only [f, cutoffRemainderNumerator, zeroη _ hy.le, zero_smul, Pi.zero_apply]
  refine ⟨?_,?_⟩
  · intro z hz
    by_cases hzb : z.2 < b
    · exact (sf.contDiffAt (hW.mem_nhds ⟨hz.1,hz.2,hzb⟩)).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq (eventZero z (le_of_not_gt hzb))).contDiffWithinAt
  · intro n hn z hz
    by_cases hzb : z.2 < b
    · have hzW : z ∈ W := ⟨hz.1,hz.2,hzb⟩
      have hzI : z.2 ∈ Icc 0 b := ⟨hz.2.le,hzb.le⟩
      have bq (i : ℕ) (hi : i ≤ 40) : ‖iteratedFDeriv ℝ i q z‖ ≤ (2 : ℝ)^40 * Jχ * A :=
        fixedShift_norm_smul_jet_le hW sχW sTrace hzW hi hJχ hA
          (fun j hj => (snd_cutoff_jet hχ j z).trans (bχ j (hj.trans hi) _ hzI))
          (fun j hj => bTrace j (hj.trans (hi.trans (by decide : 40 ≤ 100))) z hzW)
      have bN (i : ℕ) (hi : i ≤ 40) :
          ‖iteratedFDeriv ℝ i N z‖ ≤ (1 + (2 : ℝ)^40 * Jχ) * A := by
        have hi' : (i : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (hi.trans (by decide : 40 ≤ 100))
        have aM := (sMW.contDiffAt (hW.mem_nhds hzW)).of_le hi'
        have aq := (sq.contDiffAt (hW.mem_nhds hzW)).of_le hi'
        change ‖iteratedFDeriv ℝ i (M + -q) z‖ ≤ _
        have aq' : ContDiffAt ℝ i (-q) z := aq.neg
        rw [iteratedFDeriv_add_apply aM aq', iteratedFDeriv_neg_apply]
        calc
          _ ≤ ‖iteratedFDeriv ℝ i M z‖ + ‖iteratedFDeriv ℝ i q z‖ := by
            simpa only [norm_neg] using
              (norm_add_le (iteratedFDeriv ℝ i M z) (-iteratedFDeriv ℝ i q z))
          _ ≤ A + (2 : ℝ)^40 * Jχ * A := add_le_add (bMW i hi z hzW) (bq i hi)
          _ = _ := by ring
      have H := fixedShift_norm_smul_jet_le hW sηW sN hzW hn hJη
        (show 0 ≤ (1 + (2 : ℝ)^40 * Jχ) * A by positivity)
        (fun i hi => (snd_cutoff_jet sη i z).trans (bη i (hi.trans hn) _ hzI))
        (fun i hi => bN i (hi.trans hn))
      change ‖iteratedFDeriv ℝ n (fun y : LowRatio.Point => η y.2 • N y) z‖ ≤ C * A
      exact H.trans_eq (by dsimp [C]; ring)
    · have hfSupp : z ∉ tsupport f :=
        notMem_tsupport_iff_eventuallyEq.mpr (eventZero z (le_of_not_gt hzb))
      have zeroJet : iteratedFDeriv ℝ n f z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hz => hfSupp (tsupport_iteratedFDeriv_subset n hz))
      rw [zeroJet, norm_zero]
      exact mul_nonneg hC hA

end Burnett.A05.BoxFourier
