import Burnett.Analysis.AllScaleTransfer.RadianDyadicRemainderTail

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A05

open Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight
  integrable_radianTrilinearWeight_of_bounded)
open scoped Topology

/-- At signed gap k the first radial window is indexed by j+k and the
second by j, at the same frequencies as the original Fourier form. -/
def radianSignedGapSymbol (m : Joint → ℂ) (k : ℤ) (p : Joint) : ℂ :=
  ((∑' j : ℤ, integerRadialWindow (j + k) p.1 * integerRadialWindow j p.2 : ℝ) : ℂ) * m p

theorem radianSignedGapSymbol_neg_nat (m : Joint → ℂ) (s : ℕ) :
    radianSignedGapSymbol m (-(s : ℤ)) = radianLowGapSymbol m s := by
  funext p
  simp only [radianSignedGapSymbol, radianLowGapSymbol, sub_eq_add_neg]

private theorem integerRadialWindow_continuous (j : ℤ) : Continuous (integerRadialWindow j) := by
  have heq : (fun ξ : E => (endpointHighProfile ((2 : ℝ)^(-j) • ξ)).re) = integerRadialWindow j := by
    funext ξ
    rw [endpointHighProfile_eq_integerRadialWindow, Complex.ofReal_re]
  rw [← heq]
  exact Complex.continuous_re.comp
    (endpointHighProfile.continuous.comp (continuous_const.smul continuous_id))

private theorem norm_integerRadialWindow_le (j : ℤ) (ξ : E) :
    ‖integerRadialWindow j ξ‖ ≤ SchwartzMap.seminorm ℝ 0 0 endpointHighProfile := by
  have h := endpointHighProfile.norm_le_seminorm ℝ ((2 : ℝ)^(-j) • ξ)
  rwa [endpointHighProfile_eq_integerRadialWindow, Complex.norm_real] at h

/-- The exact two-window radial partition can be grouped by signed gap
inside the actual Fourier integral. At a frequency pair at most nine
window pairs are active, giving a majorant with no scale count. -/
theorem radianTrilinearForm_hasSum_signed_gaps
    (m : Joint → ℂ) (hm : AEStronglyMeasurable m volume) (B : ℝ) (hB : 0 ≤ B)
    (hNorm : ∀ p, ‖m p‖ ≤ B) (f g h : SchwartzMap E ℂ) :
    HasSum (fun k : ℤ => radianTrilinearForm (radianSignedGapSymbol m k) f g h)
      (radianTrilinearForm m f g h) := by
  let W (k j : ℤ) (p : Joint) :=
    integerRadialWindow (j + k) p.1 * integerRadialWindow j p.2
  let F := radianSignedGapSymbol m
  let L := SchwartzMap.seminorm ℝ 0 0 endpointHighProfile
  have hL : 0 ≤ L := by unfold L; positivity
  let C := (L * L) * B
  have hC : 0 ≤ C := by unfold C; positivity
  have hLocalHigh (p : Joint) : ∃ Q : Finset ℤ, Q.card ≤ 3 ∧
      ∀ j ∉ Q, ∀ k, W k j p = 0 := by
    obtain ⟨Q, hQ, hZero⟩ := exists_integerRadialWindow_support_card_le_three p.2
    exact ⟨Q, hQ, fun j hj k => by simp only [W, hZero j hj, mul_zero]⟩
  have hFinite (k : ℤ) (p : Joint) : Summable (fun j => W k j p) := by
    obtain ⟨Q, _, hZero⟩ := hLocalHigh p
    exact summable_of_ne_finset_zero (fun j hj => hZero j hj k)
  have hMask (k : ℤ) : Measurable (fun p => ∑' j, W k j p) := by
    apply measurable_of_tendsto_metrizable' (atTop : Filter (Finset ℤ))
      (f := fun Q p => ∑ j ∈ Q, W k j p)
    · intro Q
      exact (continuous_finset_sum Q (fun j _ =>
        ((integerRadialWindow_continuous _).comp continuous_fst).mul
          ((integerRadialWindow_continuous _).comp continuous_snd))).measurable
    · rw [tendsto_pi_nhds]
      intro p
      have hs : HasSum (fun j => W k j p) (∑' j, W k j p) := (hFinite k p).hasSum
      exact hs
  have hMeas (k : ℤ) : AEStronglyMeasurable (F k) volume :=
    (Complex.continuous_ofReal.measurable.comp (hMask k)).aestronglyMeasurable.mul hm
  have hTerm (k j : ℤ) (p : Joint) : ‖(W k j p : ℂ) * m p‖ ≤ C := by
    simp only [W, norm_mul, Complex.norm_real]
    exact mul_le_mul (mul_le_mul (norm_integerRadialWindow_le _ _)
      (norm_integerRadialWindow_le _ _) (norm_nonneg _) hL)
      (hNorm _) (norm_nonneg _) (mul_nonneg hL hL)
  have hSingle (k : ℤ) (p : Joint) : ‖F k p‖ ≤ 3 * C := by
    obtain ⟨Q, hQ, hZero⟩ := hLocalHigh p
    have hEq : F k p = ∑ j ∈ Q, (W k j p : ℂ) * m p := by
      change ((∑' j, W k j p : ℝ) : ℂ) * m p = _
      rw [tsum_eq_sum (s := Q) (fun j hj => hZero j hj k), Complex.ofReal_sum, Finset.sum_mul]
    rw [hEq]
    calc
      _ ≤ ∑ j ∈ Q, C := norm_sum_le_of_le _ (fun j _ => hTerm k j p)
      _ = (Q.card : ℝ) * C := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hQ) hC
  have hLocalGaps (p : Joint) : ∃ I : Finset ℤ, I.card ≤ 9 ∧ ∀ k ∉ I, F k p = 0 := by
    obtain ⟨P, hP, hZeroP⟩ := exists_integerRadialWindow_support_card_le_three p.1
    obtain ⟨Q, hQ, hZeroQ⟩ := exists_integerRadialWindow_support_card_le_three p.2
    let gap (ij : ℤ × ℤ) := ij.1 - ij.2
    let I := (P ×ˢ Q).image gap
    refine ⟨I, ?_, ?_⟩
    · change ((P ×ˢ Q).image gap).card ≤ 9
      exact Finset.card_image_le.trans (by
        rw [Finset.card_product]
        exact Nat.mul_le_mul hP hQ)
    · intro k hk
      have hz (j : ℤ) : W k j p = 0 := by
        by_cases hjq : j ∈ Q
        · have hjp : j + k ∉ P := by
            intro hp
            apply hk
            refine Finset.mem_image.mpr ⟨(j + k, j), Finset.mem_product.mpr ⟨hp, hjq⟩, ?_⟩
            change j + k - j = k
            omega
          simp only [W, hZeroP _ hjp, zero_mul]
        · simp only [W, hZeroQ _ hjq, mul_zero]
      change ((∑' j, W k j p : ℝ) : ℂ) * m p = 0
      simp only [hz, tsum_zero, Complex.ofReal_zero, zero_mul]
  have hPartial (J : Finset ℤ) (p : Joint) : ‖∑ k ∈ J, F k p‖ ≤ 9 * (3 * C) := by
    obtain ⟨I, hI, hZero⟩ := hLocalGaps p
    have hEq : (∑ k ∈ J, F k p) = ∑ k ∈ J ∩ I, F k p := by
      refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
      intro k hk hkn
      exact hZero k (fun hi => hkn (Finset.mem_inter.mpr ⟨hk, hi⟩))
    rw [hEq]
    have hCard : (J ∩ I).card ≤ 9 := (Finset.card_le_card Finset.inter_subset_right).trans hI
    calc
      _ ≤ ∑ k ∈ J ∩ I, (3 * C) := norm_sum_le_of_le _ (fun k _ => hSingle k p)
      _ = ((J ∩ I).card : ℝ) * (3 * C) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) (by positivity)
  have hAxis : ∀ᵐ p ∂(volume : Measure Joint), p.1 ≠ 0 ∧ p.2 ≠ 0 := by
    have hE : ∀ᵐ ξ ∂(volume : Measure E), ξ ≠ (0 : E) := by simp [ae_iff]
    rw [Measure.volume_eq_prod E E]
    apply (Measure.ae_prod_iff_ae_ae
      ((isOpen_ne_fun continuous_fst continuous_const).measurableSet.inter
        (isOpen_ne_fun continuous_snd continuous_const).measurableSet)).2
    filter_upwards [hE] with ξ hξ
    filter_upwards [hE] with η hη
    exact ⟨hξ, hη⟩
  have hPoint : ∀ᵐ p ∂(volume : Measure Joint), HasSum (fun k => F k p) (m p) := by
    filter_upwards [hAxis] with p hp
    let G (ij : ℤ × ℤ) := integerRadialWindow ij.1 p.1 * integerRadialWindow ij.2 p.2
    obtain ⟨P, _, hZeroP⟩ := exists_integerRadialWindow_support_card_le_three p.1
    obtain ⟨Q, _, hZeroQ⟩ := exists_integerRadialWindow_support_card_le_three p.2
    have hFinitePair : Summable G := by
      apply summable_of_ne_finset_zero (s := P ×ˢ Q)
      intro ij hij
      by_cases hi : ij.1 ∈ P
      · have hj : ij.2 ∉ Q := fun hz => hij (Finset.mem_product.mpr ⟨hi, hz⟩)
        simp only [G, hZeroQ _ hj, mul_zero]
      · simp only [G, hZeroP _ hi, zero_mul]
    have hPair : HasSum G 1 := by
      simpa only [if_neg hp.1, if_neg hp.2, one_mul] using
        (integerRadialWindow_hasSum p.1).mul (integerRadialWindow_hasSum p.2) hFinitePair
    let e : ℤ × ℤ ≃ ℤ × ℤ :=
      { toFun := fun kj => (kj.2 + kj.1, kj.2)
        invFun := fun ij => (ij.1 - ij.2, ij.2)
        left_inv := fun kj => Prod.ext (by dsimp; omega) rfl
        right_inv := fun ij => Prod.ext (by dsimp; omega) rfl }
    have hGapPair : HasSum (fun kj : ℤ × ℤ => W kj.1 kj.2 p) 1 := e.hasSum_iff.mpr hPair
    have hGap : HasSum (fun k => ∑' j, W k j p) 1 :=
      hGapPair.prod_fiberwise (fun k => (hFinite k p).hasSum)
    have hComplex := (Complex.hasSum_ofReal.mpr hGap).mul_right (m p)
    simpa only [F, radianSignedGapSymbol, Complex.ofReal_one, one_mul] using hComplex
  let K := radianWeight (fun _ => 1) f g h
  have hOne : radianTrilinearWeight (fun _ => (1 : ℂ)) f g h = K := by
    funext p
    change (1 : ℂ) * K p = K p
    exact one_mul _
  have hK : Integrable K := by
    rw [← hOne]
    exact integrable_radianTrilinearWeight_of_bounded _
      aestronglyMeasurable_const 1 (fun p => norm_one.le) f g h
  have hInt (k : ℤ) : Integrable (radianTrilinearWeight (F k) f g h) :=
    integrable_radianTrilinearWeight_of_bounded (F k) (hMeas k) (3 * C) (hSingle k) f g h
  have hT : Tendsto (fun J : Finset ℤ => ∫ p, (∑ k ∈ J, F k p) * K p) atTop
      (𝓝 (∫ p, m p * K p)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p => (9 * (3 * C)) * ‖K p‖)
    · exact Eventually.of_forall (fun J =>
        (J.aestronglyMeasurable_fun_sum (fun k _ => hMeas k)).mul hK.1)
    · exact Eventually.of_forall (fun J => Eventually.of_forall (fun p => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hPartial J p) (norm_nonneg _)))
    · exact hK.norm.const_mul _
    · filter_upwards [hPoint] with p hs
      change Tendsto (fun J : Finset ℤ => ∑ k ∈ J, F k p) atTop (𝓝 (m p)) at hs
      exact hs.mul tendsto_const_nhds
  have hEq (J : Finset ℤ) : (∑ k ∈ J, radianTrilinearForm (F k) f g h) =
      (tau ^ 8)⁻¹ • ∫ p, (∑ k ∈ J, F k p) * K p := by
    unfold radianTrilinearForm
    rw [← Finset.smul_sum, ← integral_finset_sum _ (fun k _ => hInt k)]
    simp only [radianTrilinearWeight, K, Finset.sum_mul]
  change Tendsto (fun J : Finset ℤ => ∑ k ∈ J, radianTrilinearForm (F k) f g h) atTop _
  rw [funext hEq]
  exact hT.const_smul ((tau ^ 8)⁻¹ : ℝ)

end Burnett.A05
