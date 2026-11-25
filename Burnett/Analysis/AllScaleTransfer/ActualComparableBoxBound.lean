import Burnett.Analysis.AllScaleTransfer.ActualComparableBoxPartition
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option maxHeartbeats 6700000

noncomputable section

namespace Burnett.A05

open Filter Finset Metric MeasureTheory Set
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff Topology

private theorem ae_second_frequency_ne_zero :
    ∀ᵐ p ∂(volume : Measure Joint), p.2 ≠ (0 : E) := by
  have h : ∀ᵐ q ∂(volume : Measure E), q ≠ (0 : E) := by simp [ae_iff]
  rw [Measure.volume_eq_prod E E]
  exact (Measure.ae_prod_iff_ae_ae ((isOpen_ne_fun continuous_snd continuous_const).measurableSet)).2
    (Eventually.of_forall fun _ => h)

private theorem fixedShiftMask_continuous (d : SchwartzMap E ℂ) (k j : ℤ) :
    Continuous (radianFixedShiftBoxBlock d (fun _ => 1) k j) := by
  have smoothBump : ContDiff ℝ ∞ (radialBallBump : E → ℝ) := radialBallBump.contDiff
  have low (r : ℝ) : Continuous (radialLowCutoff r) :=
    smoothBump.continuous.comp (continuous_const.smul continuous_id)
  have narrow (i : ℤ) : Continuous (fun p : E => (integerRadialWindow i p : ℂ)) :=
    Complex.continuous_ofReal.comp ((low _).sub (low _))
  unfold radianFixedShiftBoxBlock
  exact continuous_const.mul (((narrow (j+k)).comp continuous_fst).mul
    ((narrow j).comp continuous_snd) |>.mul
    (d.continuous.comp (continuous_const.smul (continuous_fst.add continuous_snd).neg)))

private theorem joined_active_mem_box (P : ℝ) (hP : 4 < P)
    (ζ υ : E) (hζ : ‖ζ‖ < 2) (hυ : ‖υ‖ < 2) :
    joinedInputs ζ υ ∈ ball (0 : BoxSpace) P := by
  have hSquare : ‖joinedInputs ζ υ‖^2 = ‖ζ‖^2 + ‖υ‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq ζ, EuclideanSpace.norm_sq_eq υ,
      Fintype.sum_sum_type]
    rfl
  have norm4 : ‖joinedInputs ζ υ‖ ≤ 4 := by
    nlinarith only [hSquare, sq_nonneg (‖ζ‖-2), sq_nonneg (‖υ‖-2),
      mul_nonneg (norm_nonneg ζ) (sub_nonneg.mpr hζ.le),
      mul_nonneg (norm_nonneg υ) (sub_nonneg.mpr hυ.le), hζ, hυ,
      sq_nonneg (‖joinedInputs ζ υ‖-4)]
  exact mem_ball_zero_iff.mpr (norm4.trans_lt hP)

/-- The actual comparable symbol in the two-frequency representation of the
paper. Each G k is the extension of its normalized signed-offset profile,
with equality on the active two radial windows. -/
theorem exists_radianComparable_box_bound {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (P κ L U : ℝ) (hP : 4 < P) (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (hL : 0 < L) (hU : 0 < U) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (A : E ≃L[ℝ] E) (m : Joint → ℂ),
      (∀ p, m p ≠ 0 →
        let w := -(p.1+p.2)
        comparableSlotWeight ϑ κ (A p.1) (A p.2) (A w) ≠ 0 ∧
        (L*‖p.1‖ ≤ ‖A p.1‖ ∧ ‖A p.1‖ ≤ U*‖p.1‖) ∧
        (L*‖p.2‖ ≤ ‖A p.2‖ ∧ ‖A p.2‖ ≤ U*‖p.2‖) ∧
        (L*‖w‖ ≤ ‖A w‖ ∧ ‖A w‖ ≤ U*‖w‖)) →
      (∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p) →
      AEStronglyMeasurable m volume →
      let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
      ∀ (G : ℤ → BoxSpace → ℂ) (B : ℝ), 0 ≤ B →
      (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) P)) →
      (∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) P, ‖iteratedFDeriv ℝ n (G k) z‖ ≤ B) →
      (∀ k ∈ I, ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
        G k (joinedInputs ζ υ) = m ((2 : ℝ)^k • ζ, υ)) →
      ∀ f g w : SchwartzMap E ℂ,
        ‖radianTrilinearForm m f g w‖ ≤ C * B * (triLpMass f g w 3 3 3).toReal := by
  obtain ⟨N, partition⟩ := exists_comparable_fixedShift_box_partition hCut hFlat
    κ L U hκ hκsmall hL hU
  let d := comparableRadialThirdProfile κ L U hκ hL hU
  obtain ⟨C, hC, bound⟩ := exists_radianFixedShift_box_forms_bound P hP d
  let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
  refine ⟨N, (I.card : ℝ)*C, by positivity, ?_⟩
  intro A m hSupp hHom hMeas I' G B hB hSmooth hJets hMatches f g w
  let F (k : (↑I : Type)) (p : Joint) := ∑' j : ℤ, radianFixedShiftBoxBlock d (G k) k j p
  let Mask (k j : ℤ) := radianFixedShiftBoxBlock d (fun _ => 1) k j
  have zero_outside {Q : Finset ℤ} {p : Joint} (hQ : ∀ j ∉ Q, integerRadialWindow j p.2 = 0)
      (k : ℤ) (G' : BoxSpace → ℂ) (j : ℤ) (hj : j ∉ Q) :
      radianFixedShiftBoxBlock d G' k j p = 0 := by
    simp only [radianFixedShiftBoxBlock, hQ j hj, Complex.ofReal_zero, mul_zero, zero_mul]
  have actual (k : (↑I : Type)) (j : ℤ) (p : Joint) :
      radianFixedShiftBoxBlock d (G k) k j p = m p * Mask k j p := by
    by_cases hFirst : integerRadialWindow (j+(k : ℤ)) p.1 = 0
    · simp only [radianFixedShiftBoxBlock, Mask, hFirst, Complex.ofReal_zero, mul_zero, zero_mul]
    by_cases hSecond : integerRadialWindow j p.2 = 0
    · simp only [radianFixedShiftBoxBlock, Mask, hSecond, Complex.ofReal_zero, mul_zero, zero_mul]
    let ζ := (2 : ℝ)^(-(j+(k : ℤ))) • p.1
    let υ := (2 : ℝ)^(-j) • p.2
    have active1 : endpointHighProfile ζ ≠ 0 := by
      dsimp only [ζ]
      rw [endpointHighProfile_eq_integerRadialWindow]
      exact_mod_cast hFirst
    have active2 : endpointHighProfile υ ≠ 0 := by
      dsimp only [υ]
      rw [endpointHighProfile_eq_integerRadialWindow]
      exact_mod_cast hSecond
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hRecon : (2 : ℝ)^j • ((2 : ℝ)^(k : ℤ) • ζ, υ) = p := by
      apply Prod.ext
      · change (2 : ℝ)^j • ((2 : ℝ)^(k : ℤ) • ((2 : ℝ)^(-(j+(k : ℤ))) • p.1)) = p.1
        rw [smul_smul, smul_smul, ← zpow_add₀ h2, ← zpow_add₀ h2, add_neg_cancel, zpow_zero, one_smul]
      · change (2 : ℝ)^j • ((2 : ℝ)^(-j) • p.2) = p.2
        rw [smul_smul, ← zpow_add₀ h2, add_neg_cancel, zpow_zero, one_smul]
    have profile : G k (joinedInputs ζ υ) = m p :=
      (hMatches k k.property ζ υ active1 active2).trans
        ((hHom ((2 : ℝ)^j) (by positivity) _).symm.trans (congrArg m hRecon))
    change G k (joinedInputs ζ υ) * _ = m p * (1 * _)
    rw [profile, one_mul]
  have expressed (k : (↑I : Type)) (p : Joint) :
      F k p = m p * ∑' j : ℤ, Mask k j p := by
    unfold F
    rw [← tsum_mul_left]
    exact tsum_congr fun j => actual k j p
  have measureMask (k : ℤ) : Measurable (fun p => ∑' j : ℤ, Mask k j p) := by
    apply measurable_of_tendsto_metrizable' (atTop : Filter (Finset ℤ))
      (f := fun Q p => ∑ j ∈ Q, Mask k j p)
    · intro Q
      exact (continuous_finset_sum Q (fun j _ => fixedShiftMask_continuous d k j)).measurable
    · rw [tendsto_pi_nhds]
      intro p
      obtain ⟨Q, _, hQ⟩ := exists_integerRadialWindow_support_card_le_three p.2
      have hz (j : ℤ) (hj : j ∉ Q) : Mask k j p = 0 := zero_outside hQ k (fun _ => 1) j hj
      have hSum : HasSum (fun j : ℤ => Mask k j p) (∑' j : ℤ, Mask k j p) :=
        (summable_of_ne_finset_zero hz).hasSum
      exact hSum
  have measured (k : (↑I : Type)) : AEStronglyMeasurable (F k) volume := by
    rw [funext (expressed k)]
    exact hMeas.mul (measureMask k).aestronglyMeasurable
  let D := SchwartzMap.seminorm ℝ 0 0 endpointHighProfile
  let W := SchwartzMap.seminorm ℝ 0 0 d
  let Bblock := B*(D*D*W)
  have bD : 0 ≤ D := apply_nonneg _ _
  have bW : 0 ≤ W := apply_nonneg _ _
  have bBlock : 0 ≤ Bblock := by unfold Bblock; positivity
  have block_bound (k : (↑I : Type)) (j : ℤ) (p : Joint) :
      ‖radianFixedShiftBoxBlock d (G k) k j p‖ ≤ Bblock := by
    by_cases hFirst : integerRadialWindow (j+(k : ℤ)) p.1 = 0
    · simpa only [radianFixedShiftBoxBlock, hFirst, Complex.ofReal_zero, mul_zero, zero_mul,
        norm_zero] using bBlock
    by_cases hSecond : integerRadialWindow j p.2 = 0
    · simpa only [radianFixedShiftBoxBlock, hSecond, Complex.ofReal_zero, mul_zero, zero_mul,
        norm_zero] using bBlock
    let ζ := (2 : ℝ)^(-(j+(k : ℤ))) • p.1
    let υ := (2 : ℝ)^(-j) • p.2
    have active1 : endpointHighProfile ζ ≠ 0 := by
      dsimp only [ζ]
      rw [endpointHighProfile_eq_integerRadialWindow]
      exact_mod_cast hFirst
    have active2 : endpointHighProfile υ ≠ 0 := by
      dsimp only [υ]
      rw [endpointHighProfile_eq_integerRadialWindow]
      exact_mod_cast hSecond
    have inBox := joined_active_mem_box P hP ζ υ (endpointHighProfile_properties.2.2 _ active1).2
      (endpointHighProfile_properties.2.2 _ active2).2
    have bG : ‖G k (joinedInputs ζ υ)‖ ≤ B := by
      simpa only [norm_iteratedFDeriv_zero] using hJets k k.property 0 (by decide) _ inBox
    have bA : ‖(integerRadialWindow (j+(k : ℤ)) p.1 : ℂ)‖ ≤ D := by
      rw [← endpointHighProfile_eq_integerRadialWindow]
      exact endpointHighProfile.norm_le_seminorm ℝ _
    have bB : ‖(integerRadialWindow j p.2 : ℂ)‖ ≤ D := by
      rw [← endpointHighProfile_eq_integerRadialWindow]
      exact endpointHighProfile.norm_le_seminorm ℝ _
    dsimp only [radianFixedShiftBoxBlock, Bblock]
    simp only [norm_mul]
    exact mul_le_mul bG
      (mul_le_mul (mul_le_mul bA bB (norm_nonneg _) bD) (d.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity))
      (by positivity) hB
  have sum_bound (k : (↑I : Type)) (p : Joint) : ‖F k p‖ ≤ 3*Bblock := by
    obtain ⟨Q,hCard,hZero⟩ := exists_integerRadialWindow_support_card_le_three p.2
    dsimp only [F]
    rw [tsum_eq_sum (s := Q) (zero_outside hZero k (G k))]
    calc
      _ ≤ ∑ j ∈ Q, Bblock := norm_sum_le_of_le _ (fun j _ => block_bound k j p)
      _ = (Q.card : ℝ)*Bblock := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) bBlock
  have pointwise : ∀ᵐ p ∂(volume : Measure Joint), HasSum (fun k : (↑I : Type) => F k p) (m p) := by
    filter_upwards [ae_second_frequency_ne_zero] with p hq
    have hSum : (∑ k : (↑I : Type), F k p) = m p := by
      simp only [expressed, ← Finset.mul_sum]
      change m p * (∑ k ∈ I.attach, ∑' j : ℤ, Mask k j p) = m p
      rw [Finset.sum_attach I (fun k => ∑' j : ℤ, Mask k j p)]
      by_cases hz : m p = 0
      · rw [hz, zero_mul]
      · obtain ⟨hc, hpA, hqA, hwA⟩ := hSupp p hz
        have hOne : (∑ k ∈ I, ∑' j : ℤ, Mask k j p) = 1 :=
          partition A p.1 p.2 hq hc hpA hqA hwA
        rw [hOne, mul_one]
    rw [← hSum]
    exact hasSum_fintype (fun k : (↑I : Type) => F k p)
  have integrated := radianTrilinearForm_hasSum_of_symbol_expansion F m
    (fun _ => 3*Bblock) measured Summable.of_finite sum_bound pointwise f g w
  have hEq := integrated.tsum_eq
  rw [tsum_fintype] at hEq
  change (∑ k ∈ I.attach, radianFixedShiftBoxForm d (G k) k f g w) =
    radianTrilinearForm m f g w at hEq
  rw [Finset.sum_attach I (fun k => radianFixedShiftBoxForm d (G k) k f g w)] at hEq
  rw [← hEq]
  exact (bound I G B hB hSmooth hJets f g w).2

end Burnett.A05
