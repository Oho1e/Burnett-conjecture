import Burnett.Analysis.AllScaleTransfer.SignedAnnularCharts
import Burnett.Analysis.AllScaleTransfer.ActualUnscaledEstimate
import Mathlib.Analysis.Calculus.ContDiff.WithLp

set_option autoImplicit false
set_option maxRecDepth 4900
set_option maxHeartbeats 8700000
noncomputable section

namespace Burnett.C02

open Set Metric Burnett.A02.FrequencySplit
open Burnett.A05 Burnett.A05.BoxFourier Burnett.Analysis.CapFourier
open Burnett.Analysis.LowRatio (Angles)
open scoped BigOperators ContDiff

abbrev WardSphereChart := Fin 4 × Bool
abbrev WardPairChart := WardSphereChart × WardSphereChart

private def moveAxis (a : Fin 4) : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 4) a)

private theorem moveAxis_head (a : Fin 4) (x : E) : moveAxis a x 0 = x a := by
  change x ((Equiv.swap (0 : Fin 4) a).symm 0) = _
  rw [Equiv.symm_swap, Equiv.swap_apply_left]

def wardChartRadius : ℝ := Real.sqrt (1 - (1 / 4 : ℝ)^2)

private theorem wardChartRadius_pos : 0 < wardChartRadius := Real.sqrt_pos.2 (by norm_num)

theorem wardChartRadius_lt_one : wardChartRadius < 1 := by
  dsimp [wardChartRadius]
  exact (Real.sqrt_lt (by norm_num) (by norm_num : (0 : ℝ) ≤ 1)).2 (by norm_num)

/-- Four coordinate axes with both signed lifts cover the same sphere.
The annular overlap is cut strictly inside the chart where the square-root
lift is smooth. -/
def wardSphereChartAnnulus (s : WardSphereChart) : Set E :=
  {x | (1 / 4 : ℝ) < ‖x‖ ∧ ‖x‖ < 3 ∧ (1 / 4 : ℝ) * ‖x‖ < signedAxis s.2 (moveAxis s.1 x)}

def wardPairChartAnnulus (s : WardPairChart) : Set Joint :=
  wardSphereChartAnnulus s.1 ×ˢ wardSphereChartAnnulus s.2

def wardPairChartDomain (_s : WardPairChart) : Set Angles :=
  ball (0 : EndpointAngle) wardChartRadius ×ˢ ball (0 : EndpointAngle) wardChartRadius

def wardSphereChartAngle (s : WardSphereChart) (x : E) : EndpointAngle :=
  endpointTail (endpointDirection (moveAxis s.1 x))

def wardPairChartAngles (s : WardPairChart) (p : Joint) : Angles :=
  (wardSphereChartAngle s.1 p.1, wardSphereChartAngle s.2 p.2)

def wardSphereChartLift (s : WardSphereChart) (x : EndpointAngle) : E :=
  (moveAxis s.1).symm (signedChartLift s.2 x)

theorem wardSphereChartLift_norm_eq_one (s : WardSphereChart) (x : EndpointAngle)
    (hx : ‖x‖ < 1) : ‖wardSphereChartLift s x‖ = 1 := by
  rw [wardSphereChartLift, LinearIsometryEquiv.norm_map]
  exact mem_sphere_zero_iff_norm.mp (signedChartLift_unitSphere s.2 hx).1

theorem wardSphereChartLift_smooth (s : WardSphereChart) :
    ContDiffOn ℝ ∞ (wardSphereChartLift s) (ball 0 1) := by
  apply (moveAxis s.1).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
  apply (contDiffOn_piLp 2).mpr
  intro i
  have hHead : ContDiffOn ℝ ∞ (fun u : EndpointAngle => Real.sqrt (1 - ‖u‖^2)) (ball 0 1) := by
    apply ((contDiff_const (c := (1 : ℝ))).sub (contDiff_norm_sq ℝ)).contDiffOn.sqrt
    intro u hu
    have ht := (sq_lt_sq₀ (norm_nonneg u) zero_le_one).mpr (mem_ball_zero_iff.mp hu)
    simp only [one_pow] at ht
    exact (sub_pos.mpr ht).ne'
  refine Fin.cases ?_ (fun j => ?_) i
  · cases s.2
    · exact hHead.neg
    · exact hHead
  · exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffOn

private theorem ward_sphere_annulus_open (s : WardSphereChart) : IsOpen (wardSphereChartAnnulus s) := by
  have hA : Continuous (fun x : E => signedAxis s.2 (moveAxis s.1 x)) := by
    have hC := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 4)).continuous.comp (moveAxis s.1).continuous
    cases hs : s.2
    · simpa only [signedAxis, hs, if_false, Bool.false_eq_true] using hC.neg
    · simpa only [signedAxis, hs, if_true] using hC
  exact (isOpen_lt continuous_const continuous_norm).inter
    ((isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt (continuous_const.mul continuous_norm) hA))

theorem wardPairChartAnnulus_open (s : WardPairChart) : IsOpen (wardPairChartAnnulus s) :=
  (ward_sphere_annulus_open s.1).prod (ward_sphere_annulus_open s.2)

theorem wardPairChartDomain_open (s : WardPairChart) : IsOpen (wardPairChartDomain s) :=
  isOpen_ball.prod isOpen_ball

theorem wardPairChartAnnulus_subset (s : WardPairChart) :
    wardPairChartAnnulus s ⊆ radialJetAnnulus (1 / 4) 3 ×ˢ radialJetAnnulus (1 / 4) 3 :=
  fun _ h => ⟨⟨h.1.1.le, h.1.2.1.le⟩, ⟨h.2.1.le, h.2.2.1.le⟩⟩

private theorem exists_margin_coordinate (x : E) (hx : x ≠ 0) :
    ∃ i : Fin 4, (1 / 4 : ℝ) * ‖x‖ < |x i| := by
  classical
  by_contra! h
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hSq : ‖x‖^2 ≤ ∑ _ : Fin 4, ((1 / 4 : ℝ) * ‖x‖)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    have hQ := pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    simpa only [Real.norm_eq_abs] using hQ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hSq
  nlinarith only [hSq, sq_pos_of_pos hn]

private theorem ward_sphere_cover (x : E) (hx : x ∈ radialJetAnnulus (1 / 2) 2) :
    ∃ s : WardSphereChart, x ∈ wardSphereChartAnnulus s := by
  have hn : 0 < ‖x‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hx.1
  obtain ⟨a, ha⟩ := exists_margin_coordinate x (norm_pos_iff.mp hn)
  have hl : (1 / 4 : ℝ) < ‖x‖ := (by norm_num : (1 / 4 : ℝ) < 1 / 2).trans_le hx.1
  have hh : ‖x‖ < 3 := hx.2.trans_lt (by norm_num)
  by_cases hs : 0 ≤ x a
  · refine ⟨(a,true), hl, hh, ?_⟩
    simpa only [signedAxis, if_true, moveAxis_head, abs_of_nonneg hs] using ha
  · refine ⟨(a,false), hl, hh, ?_⟩
    simpa only [signedAxis, if_false, Bool.false_eq_true, moveAxis_head, abs_of_neg (lt_of_not_ge hs)] using ha

theorem wardPairChartAnnulus_covers :
    radialJetAnnulus (1 / 2) 2 ×ˢ radialJetAnnulus (1 / 2) 2 ⊆ ⋃ s, wardPairChartAnnulus s := by
  intro x hx
  obtain ⟨s, hs⟩ := ward_sphere_cover x.1 hx.1
  obtain ⟨t, ht⟩ := ward_sphere_cover x.2 hx.2
  exact mem_iUnion.mpr ⟨(s,t), hs, ht⟩

private theorem ward_sphere_angle_smooth (s : WardSphereChart) :
    ContDiffOn ℝ ∞ (wardSphereChartAngle s) (wardSphereChartAnnulus s) := by
  apply endpointTail.contDiff.comp_contDiffOn
  apply endpointDirection_contDiffOn.comp (moveAxis s.1).toContinuousLinearEquiv.contDiff.contDiffOn
  intro x hx
  exact (moveAxis s.1).map_ne_zero_iff.mpr
    (norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans hx.1))

theorem wardPairChartAngles_smooth (s : WardPairChart) :
    ContDiffOn ℝ ∞ (wardPairChartAngles s) (wardPairChartAnnulus s) := by
  exact ((ward_sphere_angle_smooth s.1).comp contDiff_fst.contDiffOn fun _ hp => hp.1).prodMk
    ((ward_sphere_angle_smooth s.2).comp contDiff_snd.contDiffOn fun _ hp => hp.2)

private theorem signedDirection_margin (s : WardSphereChart) (x : E) (hx : x ∈ wardSphereChartAnnulus s) :
    (1 / 4 : ℝ) < signedAxis s.2 (endpointDirection (moveAxis s.1 x)) := by
  have hn : 0 < ‖x‖ := (by norm_num : (0 : ℝ) < 1 / 4).trans hx.1
  have hScale : signedAxis s.2 (endpointDirection (moveAxis s.1 x)) =
      ‖x‖⁻¹ * signedAxis s.2 (moveAxis s.1 x) := by
    cases hs : s.2
    · simp only [endpointDirection, signedAxis, if_false, Bool.false_eq_true,
        LinearIsometryEquiv.norm_map, PiLp.smul_apply, smul_eq_mul, mul_neg]
    · simp only [endpointDirection, signedAxis, if_true, LinearIsometryEquiv.norm_map,
        PiLp.smul_apply, smul_eq_mul]
  rw [hScale, inv_mul_eq_div]
  exact (lt_div_iff₀ hn).mpr hx.2.2

private theorem ward_sphere_angle_ball (s : WardSphereChart) (x : E)
    (hx : x ∈ wardSphereChartAnnulus s) : wardSphereChartAngle s x ∈ ball (0 : EndpointAngle) wardChartRadius := by
  let u := endpointDirection (moveAxis s.1 x)
  have hx₀ : x ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans hx.1)
  have hu : ‖u‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere ((moveAxis s.1).map_ne_zero_iff.mpr hx₀))
  have hMargin := signedDirection_margin s x hx
  have hA : (1 / 4 : ℝ)^2 < (u 0)^2 := by
    have hSq := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      ((by norm_num : (0 : ℝ) < 1 / 4).trans hMargin).le).mpr hMargin
    cases hs : s.2 <;> simpa only [signedAxis, hs, if_false, if_true, Bool.false_eq_true, neg_sq, u] using hSq
  have hT := endpointTail_norm_sq u
  rw [hu, one_pow] at hT
  have hR : wardChartRadius^2 = 1 - (1 / 4 : ℝ)^2 := Real.sq_sqrt (by norm_num)
  apply mem_ball_zero_iff.mpr
  change ‖endpointTail u‖ < wardChartRadius
  exact (sq_lt_sq₀ (norm_nonneg _) wardChartRadius_pos.le).mp (by linarith only [hA, hT, hR])

theorem wardPairChartAngles_mapsTo (s : WardPairChart) :
    MapsTo (wardPairChartAngles s) (wardPairChartAnnulus s) (wardPairChartDomain s) :=
  fun x hx => ⟨ward_sphere_angle_ball s.1 x.1 hx.1, ward_sphere_angle_ball s.2 x.2 hx.2⟩

/-- Reading the two angular variables recovers the exact signed angular
frequency, including in the limits at zero low/high ratio. -/
theorem wardSphereChartLift_angle (s : WardSphereChart) (x : E) (hx : x ∈ wardSphereChartAnnulus s) :
    wardSphereChartLift s (wardSphereChartAngle s x) = endpointDirection x := by
  have hx₀ : x ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans hx.1)
  have hSphere : endpointDirection (moveAxis s.1 x) ∈ sphere (0 : E) 1 :=
    endpointDirection_mem_sphere ((moveAxis s.1).map_ne_zero_iff.mpr hx₀)
  have hMargin := (by norm_num : (0 : ℝ) < 1 / 4).trans (signedDirection_margin s x hx)
  change (moveAxis s.1).symm (signedChartLift s.2 (endpointTail (endpointDirection (moveAxis s.1 x)))) = _
  rw [signedChartLift_endpointTail s.2 hSphere hMargin]
  simp only [endpointDirection, LinearIsometryEquiv.norm_map, map_smul, LinearIsometryEquiv.symm_apply_apply]

end Burnett.C02
