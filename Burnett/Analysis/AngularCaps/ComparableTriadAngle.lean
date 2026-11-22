import Burnett.Analysis.AngularCaps.FarAngularPhase

set_option autoImplicit false
set_option maxHeartbeats 7500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open scoped RealInnerProductSpace

/-- The manuscript's fourth weight, complementary to the three low weights. -/
def comparableSlotWeight (ϑ : ℝ → ℝ) (κ : ℝ) (p q r : Vec) : ℝ :=
  1-lowSlotWeight ϑ κ p q r-lowSlotWeight ϑ κ q r p-lowSlotWeight ϑ κ r p q

theorem lowSlotWeight_swap_high (ϑ : ℝ → ℝ) (κ : ℝ) (p q r : Vec) :
    lowSlotWeight ϑ κ p q r = lowSlotWeight ϑ κ p r q := by
  simp only [lowSlotWeight, add_comm (‖q‖^2) (‖r‖^2)]

theorem lowSlotWeight_high_adjoint (ϑ : ℝ → ℝ) (κ : ℝ) (p q r : Vec) :
    lowSlotWeight ϑ κ (-p) (-r) (-q) = lowSlotWeight ϑ κ p q r := by
  simp only [lowSlotWeight,norm_neg,add_comm (‖r‖^2) (‖q‖^2)]

theorem angularNearWeight_swap_high (ϑ : ℝ → ℝ) (δ : ℝ) (p q r : Vec) :
    angularNearWeight ϑ δ p r q = angularNearWeight ϑ δ p q r := by
  unfold angularNearWeight
  rw [mul_comm]

theorem angularNearWeight_high_adjoint (ϑ : ℝ → ℝ) (δ : ℝ) (p q r : Vec) :
    angularNearWeight ϑ δ (-p) (-r) (-q) = angularNearWeight ϑ δ p q r := by
  simp only [angularNearWeight,projectiveWedgeSq_neg_left,projectiveWedgeSq_neg_right]
  rw [mul_comm]

theorem comparableSlotWeight_rotate (ϑ : ℝ → ℝ) (κ : ℝ) (p q r : Vec) :
    comparableSlotWeight ϑ κ p q r = comparableSlotWeight ϑ κ q r p := by
  unfold comparableSlotWeight
  ring

theorem comparableSlotWeight_swap_first (ϑ : ℝ → ℝ) (κ : ℝ) (p q r : Vec) :
    comparableSlotWeight ϑ κ p q r = comparableSlotWeight ϑ κ q p r := by
  unfold comparableSlotWeight
  rw [lowSlotWeight_swap_high ϑ κ q p r,lowSlotWeight_swap_high ϑ κ p r q,
    lowSlotWeight_swap_high ϑ κ r q p]
  ring

private theorem triad_sum_rotate {p q r : Vec} (hSum : p+q+r = 0) : q+r+p = 0 := by
  calc
    _ = p+q+r := by abel
    _ = 0 := hSum

private theorem lowSlotWeight_two_first_exclusive {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16)
    {p q r : Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hSum : p+q+r = 0)
    (hLow : lowSlotWeight ϑ κ p q r ≠ 0) : lowSlotWeight ϑ κ q r p = 0 := by
  by_contra hqLow
  have hq' : lowSlotWeight ϑ κ q p r ≠ 0 := by
    rw [lowSlotWeight_swap_high]
    exact hqLow
  have hP := lowSlotWeight_nonzero_small hCut hκ hκsmall hSum hq hLow
  have hS : q+p+r = 0 := by simpa only [add_comm q p] using hSum
  have hQ := lowSlotWeight_nonzero_small hCut hκ hκsmall hS hp hq'
  have hAlpha : 0 < 2*κ := by linarith only [hκ]
  have hSmaller : 2*κ*‖p‖ < ‖p‖ := by
    have h := mul_lt_mul_of_pos_right (show 2*κ < 1 by linarith only [hκsmall]) (norm_pos_iff.mpr hp)
    simpa only [one_mul] using h
  have hLt := (mul_lt_mul_of_pos_left hSmaller hAlpha).trans hSmaller
  exact hLt.not_ge (hP.trans (mul_le_mul_of_nonneg_left hQ hAlpha.le))

theorem lowSlotWeight_nonzero_other_two_zero {ϑ : ℝ → ℝ} (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16)
    {p q r : Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hSum : p+q+r = 0)
    (hLow : lowSlotWeight ϑ κ p q r ≠ 0) :
    lowSlotWeight ϑ κ q r p = 0 ∧ lowSlotWeight ϑ κ r p q = 0 := by
  refine ⟨lowSlotWeight_two_first_exclusive hCut hκ hκsmall hp hq hSum hLow,?_⟩
  have hS : p+r+q = 0 := by simpa only [add_right_comm] using hSum
  have hL : lowSlotWeight ϑ κ p r q ≠ 0 := by
    rw [← lowSlotWeight_swap_high]
    exact hLow
  rw [lowSlotWeight_swap_high]
  exact lowSlotWeight_two_first_exclusive hCut hκ hκsmall hp hr hS hL

theorem lowSlotWeight_nonzero_high_norm_ratio {ϑ : ℝ → ℝ} (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16)
    {p q r : Vec} (hq : q ≠ 0) (hSum : p+q+r = 0)
    (hLow : lowSlotWeight ϑ κ p q r ≠ 0) :
    1-2*κ ≤ ‖r‖/‖q‖ ∧ ‖r‖/‖q‖ ≤ 1+2*κ := by
  have hSmall := lowSlotWeight_nonzero_small hCut hκ hκsmall hSum hq hLow
  have hTri := high_norm_diff_of_triad hSum
  have hpos := norm_pos_iff.mpr hq
  constructor
  · apply (le_div_iff₀ hpos).mpr
    linarith only [hSmall,hTri.1]
  · apply (div_le_iff₀ hpos).mpr
    linarith only [hSmall,hTri.2]

theorem triad_cutoff_partition_nonnegative {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hUnit : ∀ t : ℝ, 0 ≤ t → 0 ≤ ϑ t ∧ ϑ t ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16)
    {p q r : Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hSum : p+q+r = 0) :
    0 ≤ lowSlotWeight ϑ κ p q r ∧ 0 ≤ lowSlotWeight ϑ κ q r p ∧ 0 ≤ lowSlotWeight ϑ κ r p q ∧
      0 ≤ comparableSlotWeight ϑ κ p q r ∧
      lowSlotWeight ϑ κ p q r + lowSlotWeight ϑ κ q r p + lowSlotWeight ϑ κ r p q +
        comparableSlotWeight ϑ κ p q r = 1 := by
  have hRange (x y z : Vec) : 0 ≤ lowSlotWeight ϑ κ x y z ∧ lowSlotWeight ϑ κ x y z ≤ 1 :=
    hUnit _ (div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))))
  have hLowSum : lowSlotWeight ϑ κ p q r + lowSlotWeight ϑ κ q r p + lowSlotWeight ϑ κ r p q ≤ 1 := by
    by_cases hP : lowSlotWeight ϑ κ p q r = 0
    · by_cases hQ : lowSlotWeight ϑ κ q r p = 0
      · simpa only [hP,hQ,zero_add] using (hRange r p q).2
      · have hR := (lowSlotWeight_nonzero_other_two_zero hCut hκ hκsmall hq hr hp
          (triad_sum_rotate hSum) hQ).1
        simpa only [hP,hR,zero_add,add_zero] using (hRange q r p).2
    · obtain ⟨hQ,hR⟩ := lowSlotWeight_nonzero_other_two_zero hCut hκ hκsmall hp hq hr hSum hP
      simpa only [hQ,hR,add_zero] using (hRange p q r).2
  refine ⟨(hRange p q r).1,(hRange q r p).1,(hRange r p q).1,?_ ,?_⟩
  · unfold comparableSlotWeight
    linarith only [hLowSum]
  · unfold comparableSlotWeight
    ring

theorem comparableSlotWeight_nonzero_first_ratio {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16)
    {p q r : Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hSum : p+q+r = 0)
    (hComp : comparableSlotWeight ϑ κ p q r ≠ 0) : (κ/2)*‖q‖ < ‖p‖ := by
  by_contra! hNot
  have hDen : 0 < κ^2*(‖q‖^2+‖r‖^2) :=
    mul_pos (pow_pos hκ _) (add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr hq) _) (sq_nonneg _))
  have hLo := div_nonneg (sq_nonneg ‖p‖) hDen.le
  have hHi : ‖p‖^2/(κ^2*(‖q‖^2+‖r‖^2)) ≤ 1/4 := (div_le_iff₀ hDen).mpr (by
    have hSq := pow_le_pow_left₀ (norm_nonneg p) hNot 2
    nlinarith only [hSq,mul_nonneg (sq_nonneg κ) (sq_nonneg ‖r‖)])
  have hLP : lowSlotWeight ϑ κ p q r = 1 := hFlat _ hLo hHi
  have hNZ : lowSlotWeight ϑ κ p q r ≠ 0 := by rw [hLP]; exact one_ne_zero
  obtain ⟨hLQ,hLR⟩ := lowSlotWeight_nonzero_other_two_zero hCut hκ hκsmall hp hq hr hSum hNZ
  exact hComp (by simp [comparableSlotWeight,hLP,hLQ,hLR])

private theorem comparable_triad_pairing_ratio_bound {m : Form} (hm : Symmetric m) {κ ε : ℝ}
    (hκ : 0 < κ) (hε : 0 ≤ ε) {p q r : Vec} (hp : p ≠ 0) (hq : q ≠ 0)
    (hSum : p+q+r = 0) (hPQ : (κ/2)*‖p‖ ≤ ‖q‖) (hQP : (κ/2)*‖q‖ ≤ ‖p‖)
    (hpC : InRelativeCone m ε p) (hqC : InRelativeCone m ε q) (hrC : InRelativeCone m ε r) :
    |pairing m p q|/(‖p‖*‖q‖) ≤ 6*ε/κ := by
  have hR : quadratic m r = quadratic m p+quadratic m q+2*pairing m p q := by
    rw [triad_third_eq_neg_add hSum,quadratic_neg,quadratic_add hm]
  have hMix : 2*pairing m p q = quadratic m r-quadratic m p-quadratic m q := by
    linarith only [hR]
  have hAbsTwo : 2*|pairing m p q| = |2*pairing m p q| := by
    rw [abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ 2 from zero_le_two)]
  have hRmp : |quadratic m r-quadratic m p| ≤ |quadratic m r|+|quadratic m p| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (quadratic m r) (-quadratic m p)
  have hAbs : |quadratic m r-quadratic m p-quadratic m q| ≤
      |quadratic m r|+|quadratic m p|+|quadratic m q| := by
    have h : |quadratic m r-quadratic m p-quadratic m q| ≤
        |quadratic m r-quadratic m p|+|quadratic m q| := by
      simpa only [sub_eq_add_neg,abs_neg] using
        abs_add_le (quadratic m r-quadratic m p) (-quadratic m q)
    exact h.trans (add_le_add_right hRmp _)
  have hMag : 2*|pairing m p q| ≤ ε*‖r‖^2 + ε*‖p‖^2 + ε*‖q‖^2 := by
    rw [hAbsTwo,hMix]
    exact hAbs.trans (add_le_add (add_le_add hrC hpC) hqC)
  have hSqR : ‖r‖^2 ≤ 2*(‖p‖^2+‖q‖^2) := by
    have h := pow_le_pow_left₀ (norm_nonneg r) (high_norm_diff_of_triad hSum).2 2
    nlinarith only [h,sq_nonneg (‖p‖-‖q‖)]
  have hMag' : 2*|pairing m p q| ≤ 3*ε*(‖p‖^2+‖q‖^2) := by
    have h := mul_le_mul_of_nonneg_left hSqR hε
    linarith only [hMag,h]
  have hProdP := mul_le_mul_of_nonneg_right hPQ (norm_nonneg p)
  have hProdQ := mul_le_mul_of_nonneg_right hQP (norm_nonneg q)
  have hProd : κ*(‖p‖^2+‖q‖^2) ≤ 4*(‖p‖*‖q‖) := by
    linarith only [hProdP,hProdQ]
  have hκMag := mul_le_mul_of_nonneg_left hMag' hκ.le
  have hεProd := mul_le_mul_of_nonneg_left hProd (show 0 ≤ 3*ε from mul_nonneg (by norm_num) hε)
  have hCount : κ*|pairing m p q| ≤ 6*ε*(‖p‖*‖q‖) := by
    linarith only [hκMag,hεProd]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hp) (norm_pos_iff.mpr hq))).mpr
  apply (mul_le_mul_iff_right₀ hκ).mp
  refine hCount.trans_eq ?_
  field_simp [hκ.ne']

/-- On the actual comparable weight, the three signed near-cone frequencies
have all squared projective separations bounded by a constant times ε/κ. -/
theorem exists_uniform_comparable_nearNull_wedge {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (Burnett.RicciSymbol.TensorFrame.LorentzFrame m)) :
    ∃ B : ℝ, 0 < B ∧ ∀ m ∈ K, ∀ κ : ℝ, 0 < κ → κ < 1/16 →
      ∀ ε : ℝ, 0 ≤ ε → ∀ ϑ : ℝ → ℝ,
      (∀ t : ℝ, 1 ≤ t → ϑ t = 0) → (∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1) →
      ∀ p q r : Vec, p+q+r = 0 → p ≠ 0 → q ≠ 0 → r ≠ 0 →
        InRelativeCone m ε p → InRelativeCone m ε q → InRelativeCone m ε r →
        comparableSlotWeight ϑ κ p q r ≠ 0 →
        projectiveWedgeSq p q ≤ B*ε/κ ∧
          projectiveWedgeSq q r ≤ B*ε/κ ∧ projectiveWedgeSq r p ≤ B*ε/κ := by
  obtain ⟨A,hA,hUniform⟩ := exists_uniform_projectiveWedgeSq_le_nearNullPairing hK hFrame
  refine ⟨7*A,mul_pos (by norm_num) hA,?_⟩
  intro m hm κ hκ hκsmall ε hε ϑ hCut hFlat
  have hε' : ε ≤ ε/κ := (le_div_iff₀ hκ).mpr (by
    have h := mul_le_mul_of_nonneg_left (show κ ≤ 1 by linarith only [hκsmall]) hε
    simpa only [mul_one] using h)
  have hWedge (p q r : Vec) (hSum : p+q+r = 0) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
      (hpC : InRelativeCone m ε p) (hqC : InRelativeCone m ε q) (hrC : InRelativeCone m ε r)
      (hComp : comparableSlotWeight ϑ κ p q r ≠ 0) :
      projectiveWedgeSq p q ≤ (7*A)*ε/κ := by
    have hQP := comparableSlotWeight_nonzero_first_ratio hCut hFlat hκ hκsmall hp hq hr hSum hComp
    have hPQ := comparableSlotWeight_nonzero_first_ratio hCut hFlat hκ hκsmall hq hp hr
      (by simpa only [add_comm q p] using hSum) (by rwa [← comparableSlotWeight_swap_first])
    have hM := comparable_triad_pairing_ratio_bound ((hFrame m hm).elim lorentzFrame_symm)
      hκ hε hp hq hSum hPQ.le hQP.le hpC hqC hrC
    have hUpper := hUniform m hm p q hp hq ε hpC hqC
    have hεM : ε+|pairing m p q|/(‖p‖*‖q‖) ≤ 7*ε/κ := by
      have h₁ : 6*ε/κ = 6*(ε/κ) := by ring
      have h₂ : 7*ε/κ = 7*(ε/κ) := by ring
      linarith only [hε',hM,h₁,h₂]
    refine hUpper.trans ((mul_le_mul_of_nonneg_left hεM hA.le).trans_eq ?_)
    ring
  intro p q r hSum hp hq hr hpC hqC hrC hComp
  have hCompQ : comparableSlotWeight ϑ κ q r p ≠ 0 := by
    rwa [← comparableSlotWeight_rotate]
  have hCompR : comparableSlotWeight ϑ κ r p q ≠ 0 := by
    rwa [← comparableSlotWeight_rotate]
  exact ⟨hWedge p q r hSum hp hq hr hpC hqC hrC hComp,
    hWedge q r p (triad_sum_rotate hSum) hq hr hp hqC hrC hpC hCompQ,
    hWedge r p q (triad_sum_rotate (triad_sum_rotate hSum)) hr hp hq hrC hpC hqC hCompR⟩

end Burnett.Analysis.ProjectiveNullCaps
