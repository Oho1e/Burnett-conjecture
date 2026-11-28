import Burnett.Analysis.AllScaleTransfer.SphereAtlas
import Burnett.Analysis.FrozenTransport.Ward.WardLowGaugePhaseProfiles
import Burnett.Analysis.AllScaleTransfer.ActualUnscaledFirstLow
import Burnett.Analysis.AllScaleTransfer.FixedAnnularCutoff

set_option autoImplicit false
set_option maxRecDepth 6600
set_option maxHeartbeats 11000000
noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory Burnett.A02.FrequencySplit
open Burnett.A05 Burnett.A05.BoxFourier Burnett.Analysis.CapFourier
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight)
open scoped ContDiff

/-- The actual first-low cutoff in angular coordinates and ratio, including
its smooth continuation across the endpoint where the ratio vanishes. -/
def wardLowNormalizedCutoff (ϑ : ℝ → ℝ) (κ : ℝ) (x : WardLowPoint) : ℝ :=
  ϑ (x.2.2^2 / (κ^2 * (1 + ‖x.2.1 + x.2.2 • x.1‖^2)))

theorem wardLowNormalizedCutoff_smooth (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (κ : ℝ) (hκ : κ ≠ 0) : ContDiff ℝ ∞ (wardLowNormalizedCutoff ϑ κ) := by
  apply hϑ.comp
  apply (contDiff_snd.snd.pow 2).div
  · exact (contDiff_const (c := κ^2)).mul ((contDiff_const (c := (1 : ℝ))).add
      ((contDiff_snd.fst.add (contDiff_snd.snd.smul contDiff_fst)).norm_sq ℝ))
  · intro x
    exact mul_ne_zero (pow_ne_zero _ hκ) (by positivity)

theorem endpointDirection_pos_smul (t : ℝ) (ht : 0 < t) (x : E) :
    endpointDirection (t • x) = endpointDirection x := by
  unfold endpointDirection
  rw [norm_smul, Real.norm_of_nonneg ht.le, smul_smul, mul_inv_rev,
    mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]

theorem wardLowSignedThird_eq (p q : E) (hp : p ≠ 0) (hq : q ≠ 0) :
    -(p + q) = ‖q‖ • (-(endpointDirection q + (‖p‖ / ‖q‖) • endpointDirection p)) := by
  have hp₀ := norm_ne_zero_iff.mpr hp
  have hq₀ := norm_ne_zero_iff.mpr hq
  have hP : ‖p‖ • endpointDirection p = p := smul_inv_smul₀ hp₀ p
  have hQ : ‖q‖ • endpointDirection q = q := smul_inv_smul₀ hq₀ q
  have hMul : ‖q‖ * (‖p‖ / ‖q‖) = ‖p‖ := by rw [mul_comm, div_mul_cancel₀ _ hq₀]
  rw [smul_neg, smul_add, hQ, smul_smul, hMul, hP, add_comm]

theorem wardLowNormalizedCutoff_eq_lowSlotWeight (ϑ : ℝ → ℝ) (κ : ℝ)
    (p q : E) (hp : p ≠ 0) (hq : q ≠ 0) :
    wardLowNormalizedCutoff ϑ κ (endpointDirection p, endpointDirection q, ‖p‖ / ‖q‖) =
      lowSlotWeight ϑ κ p q (-(p + q)) := by
  have hq₀ := norm_ne_zero_iff.mpr hq
  have hNorm : ‖-(p + q)‖ = ‖q‖ * ‖endpointDirection q + (‖p‖ / ‖q‖) • endpointDirection p‖ := by
    conv_lhs => rw [wardLowSignedThird_eq p q hp hq, norm_smul, norm_neg,
      Real.norm_of_nonneg (norm_nonneg q)]
  unfold wardLowNormalizedCutoff lowSlotWeight
  rw [hNorm]
  apply congrArg ϑ
  set s := ‖endpointDirection q + (‖p‖ / ‖q‖) • endpointDirection p‖
  by_cases hk : κ = 0
  · simp [hk]
  have hDen : 1 + s^2 ≠ 0 := by positivity
  have hDen' : ‖q‖^2 + (‖q‖ * s)^2 ≠ 0 := by positivity
  field_simp

abbrev WardRatioDomain := Burnett.Analysis.LowRatio.Point

/-- The same two unit directions read from the finite signed sphere atlas. -/
def wardRatioChartLift (i : WardPairChart) (x : WardRatioDomain) : WardLowPoint :=
  (wardSphereChartLift i.1 x.1.1, wardSphereChartLift i.2 x.1.2, x.2)

private def wardRatioChartNeighborhood : Set WardRatioDomain :=
  (ball (0 : EndpointAngle) 1 ×ˢ ball (0 : EndpointAngle) 1) ×ˢ Ioo (-1 / 3 : ℝ) (1 / 3)

private theorem wardRatioChartNeighborhood_open : IsOpen wardRatioChartNeighborhood :=
  (isOpen_ball.prod isOpen_ball).prod isOpen_Ioo

private theorem wardRatioChartLift_smooth (i : WardPairChart) :
    ContDiffOn ℝ ∞ (wardRatioChartLift i) wardRatioChartNeighborhood := by
  exact (((wardSphereChartLift_smooth i.1).comp contDiff_fst.fst.contDiffOn fun _ hx => hx.1.1).prodMk
    (((wardSphereChartLift_smooth i.2).comp contDiff_fst.snd.contDiffOn fun _ hx => hx.1.2).prodMk
      contDiff_snd.contDiffOn))

private def wardRatioChartCompact : Set WardRatioDomain :=
  (closedBall (0 : EndpointAngle) wardChartRadius ×ˢ closedBall (0 : EndpointAngle) wardChartRadius)
    ×ˢ Icc (0 : ℝ) (1 / 4)

private theorem wardRatioChartCompact_compact : IsCompact wardRatioChartCompact :=
  ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod isCompact_Icc

private theorem wardRatioChartCompact_subset : wardRatioChartCompact ⊆ wardRatioChartNeighborhood := by
  intro x hx
  exact ⟨⟨mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx.1.1).trans_lt wardChartRadius_lt_one),
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx.1.2).trans_lt wardChartRadius_lt_one)⟩,
    ⟨(by norm_num : (-1 / 3 : ℝ) < 0).trans_le hx.2.1,
      hx.2.2.trans_lt (by norm_num)⟩⟩

private theorem wardRatioChartDomain_subset (i : WardPairChart) :
    wardPairChartDomain i ×ˢ Ico (0 : ℝ) (1 / 4) ⊆ wardRatioChartCompact :=
  fun _ hx => ⟨⟨ball_subset_closedBall hx.1.1, ball_subset_closedBall hx.1.2⟩, Ico_subset_Icc_self hx.2⟩

theorem wardRatioChartLift_angle (i : WardPairChart) (x : Joint) (hx : x ∈ wardPairChartAnnulus i)
    (r : ℝ) : wardRatioChartLift i (wardPairChartAngles i x, r) =
      (endpointDirection x.1, endpointDirection x.2, r) := by
  simp only [wardRatioChartLift, wardPairChartAngles,
    wardSphereChartLift_angle i.1 x.1 hx.1, wardSphereChartLift_angle i.2 x.2 hx.2]

/-- All the one-sided angular derivatives actually used by the all-scale
low endpoint, with one finite bound for the same coefficient in every chart. -/
theorem exists_wardRatioChartBudget (F : WardLowPoint → ℂ) (U : Set WardLowPoint)
    (hF : ContDiffOn ℝ ∞ F U)
    (hU : ∀ x : WardLowPoint, ‖x.1‖ = 1 → ‖x.2.1‖ = 1 → |x.2.2| < 1 / 3 → x ∈ U) :
    ∃ D : ℝ, 0 ≤ D ∧
      (∀ i, ContDiffOn ℝ 100 (F ∘ wardRatioChartLift i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) (1 / 4))) ∧
      ∀ i n, n ≤ 100 → ∀ x ∈ wardPairChartDomain i ×ˢ Ico (0 : ℝ) (1 / 4),
        ‖iteratedFDerivWithin ℝ n (F ∘ wardRatioChartLift i)
          (wardPairChartDomain i ×ˢ Ico (0 : ℝ) (1 / 4)) x‖ ≤ D := by
  have hLift (i : WardPairChart) : MapsTo (wardRatioChartLift i) wardRatioChartNeighborhood U := by
    intro x hx
    have hRatio : |x.2| < 1 / 3 := abs_lt.mpr
      ⟨by simpa only [neg_div] using hx.2.1, hx.2.2⟩
    exact hU _
      (wardSphereChartLift_norm_eq_one i.1 x.1.1 (mem_ball_zero_iff.mp hx.1.1))
      (wardSphereChartLift_norm_eq_one i.2 x.1.2 (mem_ball_zero_iff.mp hx.1.2)) hRatio
  have hSmooth (i : WardPairChart) : ContDiffOn ℝ ∞ (F ∘ wardRatioChartLift i) wardRatioChartNeighborhood :=
    hF.comp (wardRatioChartLift_smooth i) (hLift i)
  have hEach (i : WardPairChart) := exists_compact_contDiffOn_jet_bound wardRatioChartCompact_compact
    wardRatioChartNeighborhood_open wardRatioChartCompact_subset (hSmooth i) 100
  choose D hD hJet using hEach
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_, ?_⟩
  · intro i
    exact ((hSmooth i).of_le (WithTop.coe_le_coe.mpr le_top)).mono
      ((wardRatioChartDomain_subset i).trans wardRatioChartCompact_subset)
  · intro i n hn x hx
    have hxK := wardRatioChartDomain_subset i hx
    have hDiff : ContDiffAt ℝ n (F ∘ wardRatioChartLift i) x :=
      ((hSmooth i).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
        (wardRatioChartNeighborhood_open.mem_nhds (wardRatioChartCompact_subset hxK))
    have hu := (wardPairChartDomain_open i).uniqueDiffOn.prod (uniqueDiffOn_Ico (0 : ℝ) (1 / 4))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hu hDiff hx]
    exact (hJet i n hn x hxK).trans (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i))

end Burnett.C02
