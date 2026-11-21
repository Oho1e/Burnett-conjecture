import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderSymbol
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Bornology Filter Set Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff FourierTransform Topology

theorem firstOrderAnnularKernel_hasFDerivAt (a : E → E → ℂ) (x : E) (j : ℕ)
    (p : SchwartzMap E ℂ) (hp : (p : E → ℂ) = 𝓕⁻ (normalizedFirstOrderAnnulus a x j)) (z : E) :
    HasFDerivAt (firstOrderAnnularKernel a x j)
      (dyadicScale j ^ 6 • fderiv ℝ (p : E → ℂ) (dyadicScale j • z)) z := by
  rw [show firstOrderAnnularKernel a x j = (fun w => dyadicScale j ^ 5 • p (dyadicScale j • w)) from
    funext fun w => by rw [firstOrderAnnularKernel_eq_scaled, ← hp]]
  let s := dyadicScale j
  let T : E →L[ℝ] E := s • ContinuousLinearMap.id ℝ E
  have hT : HasFDerivAt (fun w : E => s • w) T z := T.hasFDerivAt
  have hd := ((p.smooth'.differentiable (by simp) (s • z)).hasFDerivAt.comp z hT).const_smul (s ^ 5)
  change HasFDerivAt (fun w : E => s ^ 5 • p (s • w))
    (s ^ 5 • (fderiv ℝ (p : E → ℂ) (s • z)).comp T) z at hd
  simpa only [T, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, smul_smul,
    ← pow_succ] using hd

private theorem derivative_geo_bound (p : SchwartzMap E (E →L[ℝ] ℂ)) (j : ℕ)
    (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hp : SchwartzMap.seminorm ℝ 7 0 p ≤ C) (z : E) (hz : r ≤ ‖z‖) :
    ‖dyadicScale j ^ 6 • p (dyadicScale j • z)‖ ≤ C * (r ^ 7)⁻¹ * (1/2 : ℝ)^j := by
  have hn := hr.trans_le hz
  have h := scaledSchwartz_high_bound p 6 j z (norm_pos_iff.mp hn)
  have hInv : (‖z‖ ^ 7)⁻¹ ≤ (r ^ 7)⁻¹ :=
    (inv_le_inv₀ (pow_pos hn _) (pow_pos hr _)).mpr (pow_le_pow_left₀ hr.le hz _)
  have hs : 0 ≤ (dyadicScale j)⁻¹ := by unfold dyadicScale; positivity
  calc
    _ ≤ C * (dyadicScale j)⁻¹ * (r ^ 7)⁻¹ := h.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hp hs) hInv (by positivity) (mul_nonneg hC hs))
    _ = _ := by rw [dyadicScale, ← inv_pow, ← one_div]; ring

private theorem derivative_family_bounded (p : E → ℕ → SchwartzMap E ℂ)
    (hp : IsVonNBounded ℝ (Set.range fun q : E × ℕ => p q.1 q.2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x j,
      SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ (p x j)) ≤ C ∧
      SchwartzMap.seminorm ℝ 7 0 (SchwartzMap.fderivCLM ℝ (p x j)) ≤ C := by
  let F (q : E × ℕ) := SchwartzMap.fderivCLM ℝ (p q.1 q.2)
  have hb : IsVonNBounded ℝ (F '' univ) := by
    have h := hp.image (SchwartzMap.fderivCLM ℝ)
    rwa [← Set.range_comp, ← image_univ] at h
  have hB := ((schwartz_withSeminorms ℝ E (E →L[ℝ] ℂ)).image_isVonNBounded_iff_seminorm_bounded F).mp hb
  obtain ⟨C₀,hC₀,h₀⟩ := hB (0,0)
  obtain ⟨C₇,_,h₇⟩ := hB (7,0)
  exact ⟨max C₀ C₇, hC₀.le.trans (le_max_left _ _), fun x j =>
    ⟨(h₀ (x,j) trivial).le.trans (le_max_left _ _), (h₇ (x,j) trivial).le.trans (le_max_right _ _)⟩⟩

/-- The exact infinite frequency sum is differentiable in the relative
coordinate away from zero. Its first derivative gains one inverse power. -/
theorem exists_firstOrderKernel_relativeDerivative_bound {a : E → E → ℂ} (ha : FrequencyOrderOne a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z, z ≠ 0 →
      DifferentiableAt ℝ (firstOrderKernel a x) z ∧ ‖fderiv ℝ (firstOrderKernel a x) z‖ ≤ C * (‖z‖ ^ 6)⁻¹ := by
  obtain ⟨p, hp, hBounded⟩ := exists_boundedInverseProfiles ha
  obtain ⟨A, hA, hProfile⟩ := derivative_family_bounded p hBounded
  obtain ⟨p₀, C, hC, hp₀, hP₀⟩ := exists_normalizedInverseProfiles ha
  refine ⟨66 * A, by positivity, ?_⟩
  intro x z hz
  let r := ‖z‖ / 2
  let U := Metric.ball z r
  have hr : 0 < r := half_pos (norm_pos_iff.mpr hz)
  have hzU : z ∈ U := Metric.mem_ball_self hr
  have hLower (w : E) (hw : w ∈ U) : r ≤ ‖w‖ := by
    have hdist : ‖w-z‖ < r := by simpa only [U, Metric.mem_ball, dist_eq_norm] using hw
    have ht := norm_sub_le w (w-z)
    rw [sub_sub_cancel] at ht
    dsimp only [r] at *
    linarith
  let dp (j : ℕ) := SchwartzMap.fderivCLM ℝ (p x j)
  let B (j : ℕ) := A * (r ^ 7)⁻¹ * (1/2 : ℝ)^j
  have hB : Summable B := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_left _
  have hDeriv (j : ℕ) (w : E) : HasFDerivAt (firstOrderAnnularKernel a x j)
      (dyadicScale j ^ 6 • dp j (dyadicScale j • w)) w := by
    simp only [dp, SchwartzMap.fderivCLM_apply]
    exact firstOrderAnnularKernel_hasFDerivAt a x j (p x j) (hp x j) w
  have hFun : HasFDerivAt (firstOrderKernel a x)
      (∑' j, dyadicScale j ^ 6 • dp j (dyadicScale j • z)) z :=
    hasFDerivAt_tsum_of_isPreconnected hB Metric.isOpen_ball (convex_ball z r).isPreconnected
      (fun j w _ => hDeriv j w)
      (fun j w hw => derivative_geo_bound (dp j) j r A hr hA (hProfile x j).2 w (hLower w hw)) hzU
      ((firstOrderKernel_size a p₀ hp₀ C hC hP₀ x z hz).1.of_norm) hzU
  obtain ⟨hSummable, hSize⟩ := scaledFamily_absoluteSum_le dp 6 (by decide) A hA (hProfile x) z hz
  refine ⟨hFun.differentiableAt, ?_⟩
  rw [hFun.fderiv]
  have hc : A * ((2 : ℝ)^6 + 2) = 66*A := by ring
  rw [hc] at hSize
  exact (norm_tsum_le_tsum_norm hSummable).trans hSize

end Burnett.Analysis.FirstOrderDyadic
