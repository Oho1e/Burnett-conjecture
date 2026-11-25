import Burnett.Analysis.AllScaleTransfer.ActualComparableAxialLocalization
import Burnett.Analysis.AllScaleTransfer.ActualComparableBoxBound
import Burnett.Analysis.AllScaleTransfer.FiniteShiftRemainderNumerator

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A05

open Set Metric Filter
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier
open scoped ContDiff Topology

/-- The axial window becomes smooth across zero after the actual radial
cutoff confines it to the fixed annulus. -/
def annularAxialCapWindow (α a b : ℝ) (x : E) : ℝ :=
  comparableThirdCutoff a b 1 x * axialCapWindow α x

theorem annularAxialCapWindow_contDiff (α : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContDiff ℝ ∞ (annularAxialCapWindow α a b) := by
  obtain ⟨sCut,hCut⟩ := comparableThirdCutoff_smooth_support ha hab (by norm_num : (0 : ℝ) < 1)
  have hOpen : IsOpen {x : E | x ≠ (0 : E)} := isOpen_ne_fun continuous_id continuous_const
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · have z : (0 : E) ∉ tsupport (comparableThirdCutoff a b 1) := by
      intro h
      have h0 := (hCut h).1
      rw [norm_zero,mul_one] at h0
      linarith
    have ev : annularAxialCapWindow α a b =ᶠ[𝓝 (0 : E)] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp z] with y hy
      change comparableThirdCutoff a b 1 y = 0 at hy
      simp only [annularAxialCapWindow,hy,zero_mul,Pi.zero_apply]
    rw [hx]
    exact contDiffAt_const.congr_of_eventuallyEq ev
  · exact sCut.contDiffAt.mul ((axialCapWindow_contDiffOn α).contDiffAt (hOpen.mem_nhds hx))

/-- One scalar cutoff multiplying the original comparable box profile,
with the third slot evaluated at the normalized negative frequency sum. -/
def comparableAxialBoxWindow (α a b : ℝ) (k : ℤ) (z : BoxSpace) : ℝ :=
  let ζ := firstInput z
  let υ := secondInput z
  annularAxialCapWindow α (1/2) 2 ζ * annularAxialCapWindow α (1/2) 2 υ *
    annularAxialCapWindow α a b (-((2 : ℝ)^k • ζ+υ))

theorem comparableAxialBoxWindow_contDiff (α : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (k : ℤ) : ContDiff ℝ ∞ (comparableAxialBoxWindow α a b k) := by
  have s₁ : ContDiff ℝ ∞ (firstInput : BoxSpace → E) := contDiff_fst.comp boxToPair.contDiff
  have s₂ : ContDiff ℝ ∞ (secondInput : BoxSpace → E) := contDiff_snd.comp boxToPair.contDiff
  have s₃ : ContDiff ℝ ∞ (fun z : BoxSpace => -((2 : ℝ)^k • firstInput z+secondInput z)) :=
    ((contDiff_const.smul s₁).add s₂).neg
  have sR := annularAxialCapWindow_contDiff α (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 2)
  exact ((sR.comp s₁).mul (sR.comp s₂)).mul ((annularAxialCapWindow_contDiff α ha hab).comp s₃)

theorem comparableAxialBoxWindow_joined (α a b : ℝ) (k : ℤ) (ζ υ : E) :
    let p : Joint := ((2 : ℝ)^k • ζ,υ)
    let w := -(p.1+p.2)
    comparableAxialBoxWindow α a b k (joinedInputs ζ υ) =
      (comparableThirdCutoff (1/2) 2 1 ζ * comparableThirdCutoff (1/2) 2 1 υ *
        comparableThirdCutoff a b 1 w) * axialComparableWindow α p := by
  intro p w
  simp only [comparableAxialBoxWindow,firstInput_joined,secondInput_joined,annularAxialCapWindow]
  unfold axialComparableWindow axialCapPairWindow
  have he : axialCapWindow α p.1 = axialCapWindow α ζ :=
    axialCapWindow_pos_smul α ((2 : ℝ)^k) (by positivity) ζ
  rw [he]
  change (_ * axialCapWindow α ζ) * (_ * axialCapWindow α υ) *
    (comparableThirdCutoff a b 1 w * axialCapWindow α w) =
      (_ * _ * comparableThirdCutoff a b 1 w) *
        (axialCapWindow α ζ * axialCapWindow α υ * axialCapWindow α w)
  ring

/-- Multiplying the given normalized C100 boxes by the literal three
windows preserves a common order-zero-through-40 jet bound. -/
theorem exists_comparable_axial_box_budget (I : Finset ℤ) (α a b P : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℤ → BoxSpace → ℂ) (Q : ℝ), 0 ≤ Q →
        (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) P)) →
        (∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) P,
          ‖iteratedFDeriv ℝ n (G k) z‖ ≤ Q) →
        let H (k : ℤ) (z : BoxSpace) := comparableAxialBoxWindow α a b k z • G k z
        (∀ k ∈ I, ContDiffOn ℝ 100 (H k) (ball (0 : BoxSpace) P)) ∧
        ∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) P,
          ‖iteratedFDeriv ℝ n (H k) z‖ ≤ C * Q := by
  have smooth (k : ℤ) := comparableAxialBoxWindow_contDiff α ha hab k
  have chooseBudget (k : ℤ) := exists_compact_contDiffOn_jet_bound
    (isCompact_closedBall (0 : BoxSpace) P) isOpen_univ (subset_univ _)
    (smooth k).contDiffOn 40
  choose D hD bD using chooseBudget
  let S := ∑ k ∈ I, D k
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => hD k)
  refine ⟨(2 : ℝ)^40 * S, mul_nonneg (by positivity) hS,?_⟩
  intro G Q hQ sG bG H
  have sr (k : ℤ) : ContDiffOn ℝ 100 (comparableAxialBoxWindow α a b k) (ball (0 : BoxSpace) P) :=
    ((smooth k).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  refine ⟨fun k hk => (sr k).smul (sG k hk),?_⟩
  intro k hk n hn z hz
  have hS' : D k ≤ S := Finset.single_le_sum (fun i _ => hD i) hk
  exact fixedShift_norm_smul_jet_le isOpen_ball (sr k) (sG k hk) hz hn hS hQ
    (fun i hi => (bD k i (hi.trans hn) z (ball_subset_closedBall hz)).trans hS')
    (fun i hi => bG k hk i (hi.trans hn) z hz)

end Burnett.A05
