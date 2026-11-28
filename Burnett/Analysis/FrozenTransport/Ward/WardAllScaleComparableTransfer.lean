import Burnett.Analysis.AllScaleTransfer.ActualComparableBoxBound
import Burnett.Analysis.AllScaleTransfer.RadianFourBranchProperties
import Burnett.Analysis.AllScaleTransfer.FixedAnnularCutoff
import Burnett.Analysis.AngularCaps.SmoothCapProfiles

set_option autoImplicit false
set_option maxRecDepth 6100
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory Burnett.A02.FrequencySplit Burnett.A05 Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff Topology BigOperators

def wardSignedThird (x : Joint) : E := -(x.1 + x.2)

def wardTriadDomain : Set Joint := {x | x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ wardSignedThird x ≠ 0}

private theorem wardSignedThird_smooth : ContDiff ℝ ∞ wardSignedThird := (contDiff_fst.add contDiff_snd).neg

theorem wardTriadDomain_open : IsOpen wardTriadDomain :=
  (isOpen_ne_fun continuous_fst continuous_const).inter
    ((isOpen_ne_fun continuous_snd continuous_const).inter
      (isOpen_ne_fun wardSignedThird_smooth.continuous continuous_const))

private def wardExtendedTriadSymbol (F : Joint → ℂ) : Joint → ℂ := by
  classical
  exact wardTriadDomain.piecewise F 0

/-- The comparable component of the actual four-branch partition on the
signed triad, with the singular axes filled by zero. -/
def wardComparableSymbol (ϑ : ℝ → ℝ) (κ : ℝ) (F : Joint → ℂ) : Joint → ℂ :=
  radianFourBranchSymbol ϑ κ (wardExtendedTriadSymbol F) 3

private theorem wardComparableSymbol_eq (ϑ : ℝ → ℝ) (κ : ℝ) (F : Joint → ℂ) (x : Joint) :
    wardComparableSymbol ϑ κ F x = (comparableSlotWeight ϑ κ x.1 x.2 (wardSignedThird x) : ℂ) *
      wardExtendedTriadSymbol F x := rfl

theorem wardComparableSymbol_smooth (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (κ : ℝ) (hκ : κ ≠ 0) (F : Joint → ℂ) (hF : ContDiffOn ℝ ∞ F wardTriadDomain) :
    ContDiffOn ℝ ∞ (wardComparableSymbol ϑ κ F) wardTriadDomain := by
  classical
  have hlo (P Q R : Joint → E) (hp : ContDiff ℝ ∞ P) (hq : ContDiff ℝ ∞ Q) (hr : ContDiff ℝ ∞ R)
      (hQ : ∀ x ∈ wardTriadDomain, Q x ≠ 0) :
      ContDiffOn ℝ ∞ (fun x => lowSlotWeight ϑ κ (P x) (Q x) (R x)) wardTriadDomain := by
    apply hϑ.comp_contDiffOn
    apply (hp.norm_sq ℝ).contDiffOn.div
    · exact ((contDiff_const (c := κ^2)).mul ((hq.norm_sq ℝ).add (hr.norm_sq ℝ))).contDiffOn
    · intro x hx
      exact mul_ne_zero (pow_ne_zero 2 hκ)
        (add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr (hQ x hx)) 2) (sq_nonneg _)).ne'
  have hg : ContDiffOn ℝ ∞ (fun x : Joint => comparableSlotWeight ϑ κ x.1 x.2 (wardSignedThird x))
      wardTriadDomain := by
    exact (((contDiffOn_const (c := (1 : ℝ))).sub
      (hlo Prod.fst Prod.snd wardSignedThird contDiff_fst contDiff_snd wardSignedThird_smooth (fun _ hx => hx.2.1))).sub
      (hlo Prod.snd wardSignedThird Prod.fst contDiff_snd wardSignedThird_smooth contDiff_fst (fun _ hx => hx.2.2))).sub
      (hlo wardSignedThird Prod.fst Prod.snd wardSignedThird_smooth contDiff_fst contDiff_snd (fun _ hx => hx.1))
  apply ((Complex.ofRealCLM.contDiff.comp_contDiffOn hg).mul hF).congr
  intro x hx
  rw [wardComparableSymbol_eq, wardExtendedTriadSymbol, piecewise_eq_of_mem _ _ _ hx]
  rfl

private def wardComparableBump (κ : ℝ) (p : E) : ℝ :=
  1 - descendingProfile (κ^2 / 64) (κ^2 / 16) (‖p‖^2)

private theorem wardComparableBump_smooth (κ : ℝ) : ContDiff ℝ ∞ (wardComparableBump κ) :=
  contDiff_const.sub ((descendingProfile_contDiff _ _).comp (contDiff_norm_sq ℝ))

private theorem wardComparableBump_thresholds (κ : ℝ) (hκ : 0 < κ) : κ^2 / 64 < κ^2 / 16 := by
  nlinarith only [sq_pos_of_pos hκ]

private theorem wardComparableBump_zero (κ : ℝ) (hκ : 0 < κ) (p : E) (hp : ‖p‖^2 ≤ κ^2 / 64) :
    wardComparableBump κ p = 0 := by
  rw [wardComparableBump, descendingProfile_eq_one (wardComparableBump_thresholds κ hκ) hp, sub_self]

private theorem wardComparableBump_one (κ : ℝ) (hκ : 0 < κ) (p : E) (hp : κ / 4 ≤ ‖p‖) :
    wardComparableBump κ p = 1 := by
  have hSq := pow_le_pow_left₀ (div_nonneg hκ.le (by norm_num)) hp 2
  have h : κ^2 / 16 ≤ ‖p‖^2 := by nlinarith only [hSq]
  rw [wardComparableBump, descendingProfile_eq_zero (wardComparableBump_thresholds κ hκ) h, sub_zero]

private def wardComparableWindow (κ : ℝ) (x : Joint) : ℝ :=
  wardComparableBump κ x.1 * wardComparableBump κ x.2 * wardComparableBump κ (wardSignedThird x)

private def wardComparableNearAxis (κ : ℝ) : Set Joint :=
  {x | ‖x.1‖^2 < κ^2 / 64 ∨ ‖x.2‖^2 < κ^2 / 64 ∨ ‖wardSignedThird x‖^2 < κ^2 / 64}

private theorem wardComparableNearAxis_open (κ : ℝ) : IsOpen (wardComparableNearAxis κ) :=
  (isOpen_lt (continuous_fst.norm.pow 2) continuous_const).union
    ((isOpen_lt (continuous_snd.norm.pow 2) continuous_const).union
      (isOpen_lt (wardSignedThird_smooth.continuous.norm.pow 2) continuous_const))

private theorem wardComparableNearAxis_of_not_mem (κ : ℝ) (hκ : 0 < κ) {x : Joint}
    (hx : x ∉ wardTriadDomain) : x ∈ wardComparableNearAxis κ := by
  have hPos : 0 < κ^2 / 64 := by positivity
  by_cases h₁ : x.1 = 0
  · exact Or.inl (by simpa only [h₁, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hPos)
  by_cases h₂ : x.2 = 0
  · exact Or.inr (Or.inl (by simpa only [h₂, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hPos))
  have h₃ : wardSignedThird x = 0 := by by_contra h; exact hx ⟨h₁,h₂,h⟩
  exact Or.inr (Or.inr (by simpa only [h₃, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hPos))

private def wardComparablePaddedSymbol (ϑ : ℝ → ℝ) (κ : ℝ) (F : Joint → ℂ) (x : Joint) : ℂ :=
  (wardComparableWindow κ x : ℂ) * wardComparableSymbol ϑ κ F x

private theorem wardComparablePaddedSymbol_smooth (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (κ : ℝ) (hκ : 0 < κ) (F : Joint → ℂ) (hF : ContDiffOn ℝ ∞ F wardTriadDomain) :
    ContDiff ℝ ∞ (wardComparablePaddedSymbol ϑ κ F) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ wardTriadDomain
  · have hW : ContDiff ℝ ∞ (wardComparableWindow κ) :=
      (((wardComparableBump_smooth κ).comp contDiff_fst).mul ((wardComparableBump_smooth κ).comp contDiff_snd)).mul
        ((wardComparableBump_smooth κ).comp wardSignedThird_smooth)
    exact ((Complex.ofRealCLM.contDiff.comp hW).contDiffOn.mul
      (wardComparableSymbol_smooth ϑ hϑ κ hκ.ne' F hF)).contDiffAt (wardTriadDomain_open.mem_nhds hx)
  · have hv : ContDiffOn ℝ ∞ (wardComparablePaddedSymbol ϑ κ F) (wardComparableNearAxis κ) := by
      apply (contDiffOn_const (c := (0 : ℂ))).congr
      intro y hy
      have hw : wardComparableWindow κ y = 0 := by
        rcases hy with h | h | h
        · simp only [wardComparableWindow, wardComparableBump_zero κ hκ _ h.le, zero_mul]
        · simp only [wardComparableWindow, wardComparableBump_zero κ hκ _ h.le, mul_zero, zero_mul]
        · simp only [wardComparableWindow, wardComparableBump_zero κ hκ _ h.le, mul_zero]
      rw [wardComparablePaddedSymbol, hw, Complex.ofReal_zero, zero_mul]
    exact hv.contDiffAt ((wardComparableNearAxis_open κ).mem_nhds (wardComparableNearAxis_of_not_mem κ hκ hx))

private theorem wardComparablePaddedSymbol_agrees (ϑ : ℝ → ℝ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) (F : Joint → ℂ)
    (x : Joint) (hq : (1 / 2 : ℝ) ≤ ‖x.2‖) :
    wardComparablePaddedSymbol ϑ κ F x = wardComparableSymbol ϑ κ F x := by
  by_cases h : wardComparableSymbol ϑ κ F x = 0
  · simp only [wardComparablePaddedSymbol, h, mul_zero]
  have hc : comparableSlotWeight ϑ κ x.1 x.2 (wardSignedThird x) ≠ 0 := by
    intro hc
    exact h (by rw [wardComparableSymbol_eq, hc, Complex.ofReal_zero, zero_mul])
  have hq₀ : 0 < ‖x.2‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hq
  have hB := comparableSlotWeight_signed_triad_bounds hCut hFlat hκ hSmall (norm_pos_iff.mp hq₀) hc
  have hInner : κ / 4 ≤ κ / 2 * ‖x.2‖ := by linarith only [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ κ / 2)]
  have hP := hInner.trans hB.1.1
  have hR : κ / 4 ≤ ‖wardSignedThird x‖ := hInner.trans hB.2.1
  have hQ := (by linarith only [hSmall] : κ / 4 ≤ 1 / 2).trans hq
  simp only [wardComparablePaddedSymbol, wardComparableWindow, wardComparableBump_one κ hκ _ hP,
    wardComparableBump_one κ hκ _ hQ, wardComparableBump_one κ hκ _ hR, mul_one, Complex.ofReal_one, one_mul]

/-- The actual complementary branch has a smooth compact-box extension at
each of the finite relative shifts, and hence an unscaled L³ trilinear bound. -/
theorem exists_wardComparableForm_bound (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) (F : Joint → ℂ)
    (hF : ContDiffOn ℝ ∞ F wardTriadDomain)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain, F (t • x) = F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g h : SchwartzMap E ℂ,
      ‖radianTrilinearForm (wardComparableSymbol ϑ κ F) f g h‖ ≤ C * (triLpMass f g h 3 3 3).toReal := by
  classical
  let A := ContinuousLinearEquiv.refl ℝ E
  let m := wardComparableSymbol ϑ κ F
  have hm : Measurable m := measurable_radianFourBranchSymbol ϑ hϑ.continuous.measurable κ _
    ((hF.continuousOn.measurable_piecewise continuousOn_const wardTriadDomain_open.measurableSet)) 3
  have homExt (t : ℝ) (ht : 0 < t) (x : Joint) : wardExtendedTriadSymbol F (t • x) = wardExtendedTriadSymbol F x := by
    have he : t • x ∈ wardTriadDomain ↔ x ∈ wardTriadDomain := by
      simp only [wardTriadDomain, mem_setOf_eq, wardSignedThird, Prod.smul_fst, Prod.smul_snd,
        ← smul_add, ← smul_neg, smul_ne_zero_iff_right ht.ne']
    by_cases hx : x ∈ wardTriadDomain
    · rw [wardExtendedTriadSymbol, piecewise_eq_of_mem _ _ _ (he.mpr hx), piecewise_eq_of_mem _ _ _ hx, hHom t ht x hx]
    · rw [wardExtendedTriadSymbol, piecewise_eq_of_notMem _ _ _ (mt he.mp hx), piecewise_eq_of_notMem _ _ _ hx]
      rfl
  have hHomM : ∀ t : ℝ, 0 < t → ∀ x : Joint, m (t • x) = m x :=
    radianFourBranchSymbol_homogeneous ϑ κ (wardExtendedTriadSymbol F) homExt 3
  have hs (x : Joint) (hx : m x ≠ 0) : comparableSlotWeight ϑ κ x.1 x.2 (wardSignedThird x) ≠ 0 := by
    intro h
    apply hx
    change wardComparableSymbol ϑ κ F x = 0
    rw [wardComparableSymbol_eq, h, Complex.ofReal_zero, zero_mul]
  obtain ⟨N,C,hC,hBound⟩ := exists_radianComparable_box_bound hCut hFlat 5 κ 1 1
    (by norm_num) hκ hSmall zero_lt_one zero_lt_one
  let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let G (k : ℤ) (x : BoxSpace) := wardComparablePaddedSymbol ϑ κ F ((2 : ℝ)^k • (boxToPair x).1, (boxToPair x).2)
  have hGSmooth (k : ℤ) : ContDiff ℝ ∞ (G k) :=
    (wardComparablePaddedSymbol_smooth ϑ hϑ κ hκ F hF).comp
      ((contDiff_const.smul (contDiff_fst.comp boxToPair.contDiff)).prodMk (contDiff_snd.comp boxToPair.contDiff))
  have hBudget (k : ℤ) := exists_compact_contDiffOn_jet_bound
    (isCompact_closedBall (0 : BoxSpace) 5) isOpen_univ (subset_univ _) (hGSmooth k).contDiffOn 40
  choose D hD hJets using hBudget
  let B := ∑ k ∈ I, D k
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => hD _)
  have hGJet (k : ℤ) (hk : k ∈ I) (n : ℕ) (hn : n ≤ 40) (x : BoxSpace) (hx : x ∈ ball 0 5) :
      ‖iteratedFDeriv ℝ n (G k) x‖ ≤ B := by
    exact (hJets k n hn x (ball_subset_closedBall hx)).trans
      (Finset.single_le_sum (f := D) (fun _ _ => hD _) hk)
  have hMatch (k : ℤ) (_ : k ∈ I) (ζ υ : E) (_ : endpointHighProfile ζ ≠ 0) (hυ : endpointHighProfile υ ≠ 0) :
      G k (joinedInputs ζ υ) = m ((2 : ℝ)^k • ζ, υ) := by
    simp only [G, boxToPair_joined]
    exact wardComparablePaddedSymbol_agrees ϑ hCut hFlat κ hκ hSmall F _ (endpointHighProfile_properties.2.2 υ hυ).1.le
  refine ⟨C * B, mul_nonneg hC hB, hBound A m ?_ hHomM hm.aestronglyMeasurable G B hB
    (fun k _ => ((hGSmooth k).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn) hGJet hMatch⟩
  intro x hx
  simpa only [A, ContinuousLinearEquiv.refl_apply, one_mul, le_refl, and_self, and_true, wardSignedThird] using hs x hx

end Burnett.C02
