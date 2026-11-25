import Burnett.Analysis.AllScaleTransfer.ActualCapAxialWindows
import Burnett.Analysis.AllScaleTransfer.EndpointAngularTraceSeries
import Burnett.Analysis.AllScaleTransfer.FixedAnnularCutoff
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option maxHeartbeats 3300000
noncomputable section

namespace Burnett.A05

open Set Metric Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier (exists_compact_contDiffOn_jet_bound)
open Burnett.Analysis.ProjectiveNullCaps
open Burnett.Analysis.LowRatio (Angles Point)
open scoped ContDiff RealInnerProductSpace Nat

/-- On either signed unit chart the squared axial coordinate is one minus
the squared norm of the other three coordinates. -/
def axialCapAngleWindow (α : ℝ) (u : EndpointAngle) : ℝ :=
  descendingProfile (-(α^2)) (-((α/2)^2)) (‖u‖^2 - 1)

theorem axialCapAngleWindow_eq (α : ℝ) {p : E} (hp : p ≠ 0) :
    axialCapAngleWindow α (endpointTail (endpointDirection p)) = axialCapWindow α p := by
  have hu : ‖endpointDirection p‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere hp)
  have h := endpointTail_norm_sq (endpointDirection p)
  rw [hu,one_pow] at h
  have key : ‖endpointTail (endpointDirection p)‖^2 - 1 = -((endpointDirection p 0)^2) := by
    linarith only [h]
  rw [axialCapAngleWindow,axialCapWindow,key]

def axialCapChartWindow (α : ℝ) (z : Point) : ℝ :=
  axialCapAngleWindow α z.1.1 * axialCapAngleWindow α z.1.2

def axialLocalizeChart (α : ℝ) (M : Point → ℂ) (z : Point) : ℂ :=
  axialCapChartWindow α z • M z

theorem axialLocalizeChart_eval (α : ℝ) (M : Point → ℂ) {p q : E}
    (hp : p ≠ 0) (hq : q ≠ 0) (ρ : ℝ) :
    let z : Point := ((endpointTail (endpointDirection p),endpointTail (endpointDirection q)), ρ)
    axialLocalizeChart α M z = (axialCapPairWindow α (p,q) : ℂ) * M z := by
  intro z
  have h : axialCapChartWindow α z = axialCapPairWindow α (p,q) := by
    simp only [z,axialCapChartWindow,axialCapPairWindow,axialCapAngleWindow_eq α hp,axialCapAngleWindow_eq α hq]
  rw [axialLocalizeChart,h,Algebra.smul_def]
  rfl

private theorem axialCapChartWindow_smooth (α : ℝ) : ContDiff ℝ ∞ (axialCapChartWindow α) := by
  have s : ContDiff ℝ ∞ (fun u : EndpointAngle => ‖u‖^2) := by
    simpa only [id_eq,real_inner_self_eq_norm_sq] using
      (contDiff_id.inner ℝ contDiff_id : ContDiff ℝ ∞ (fun u : EndpointAngle => inner ℝ u u))
  have q : ContDiff ℝ ∞ (axialCapAngleWindow α) :=
    (descendingProfile_contDiff _ _).comp (s.sub (contDiff_const (c := (1:ℝ))))
  exact (q.comp (contDiff_fst.fst : ContDiff ℝ ∞ (fun z : Point => z.1.1))).mul
    (q.comp (contDiff_fst.snd : ContDiff ℝ ∞ (fun z : Point => z.1.2)))

/-- The fixed angular window preserves the one-sided C¹⁰⁰ chart budget up to
one constant from the cutoff and the original bounded chart. -/
theorem exists_axialLocalizeChart_oneSidedC100_bound (α r b : ℝ) (U : Set Angles)
    (hU : IsOpen U) (hUbound : U ⊆ closedBall (0 : Angles) r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Point → ℂ) (A : ℝ), 0 ≤ A →
      ContDiffOn ℝ 100 M (U ×ˢ Ico (0 : ℝ) b) →
      (∀ n ≤ 100, ∀ z ∈ U ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n M (U ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) →
      ContDiffOn ℝ 100 (axialLocalizeChart α M) (U ×ˢ Ico (0 : ℝ) b) ∧
      ∀ n ≤ 100, ∀ z ∈ U ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (axialLocalizeChart α M) (U ×ˢ Ico (0 : ℝ) b) z‖ ≤ C*A := by
  let S := U ×ˢ Ico (0 : ℝ) b
  let K := closedBall (0 : Angles) r ×ˢ Icc (0 : ℝ) b
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hSK : S ⊆ K := fun _ hz => ⟨hUbound hz.1,Ico_subset_Icc_self hz.2⟩
  have uniqueS : UniqueDiffOn ℝ S := hU.uniqueDiffOn.prod (uniqueDiffOn_Ico 0 b)
  let β := axialCapChartWindow α
  have hβ : ContDiff ℝ ∞ β := axialCapChartWindow_smooth α
  obtain ⟨B,hB,jets⟩ := exists_compact_contDiffOn_jet_bound hK isOpen_univ (subset_univ _) hβ.contDiffOn 100
  have hβ100 : ContDiffOn ℝ 100 β S := (hβ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  refine ⟨2^100*B,by positivity,?_⟩
  intro M A hA hM hMJets
  refine ⟨hβ100.smul hM,?_⟩
  intro n hn z hz
  have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast hn
  change ‖iteratedFDerivWithin ℝ n (fun y => β y • M y) S z‖ ≤ _
  refine (norm_iteratedFDerivWithin_smul_le hβ100 hM uniqueS hz hn').trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*B*A := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hβi : ContDiffAt ℝ i β z := (hβ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
      rw [iteratedFDerivWithin_eq_iteratedFDeriv uniqueS hβi hz]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (jets i (hi'.trans hn) z (hSK hz)) (by positivity))
        (hMJets (n-i) ((Nat.sub_le _ _).trans hn) z hz) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^n*B*A := by
      rw [← Finset.sum_mul,← Finset.sum_mul]
      norm_cast
      rw [Nat.sum_range_choose]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hB) hA

end Burnett.A05
