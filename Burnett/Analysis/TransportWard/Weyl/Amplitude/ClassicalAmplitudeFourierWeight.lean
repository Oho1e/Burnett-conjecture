import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalAmplitudePhysicalCutoff

set_option autoImplicit false
set_option maxHeartbeats 5100000
noncomputable section

namespace Burnett.A03

open Bornology Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform Topology

/-- Uniform order one in the Schwartz seminorms of the compact input-base
slices. The estimate is before Fourier transform. -/
def RadianAmplitudeInputOrderOne (A : E → E → SchwartzMap E ℂ) : Prop :=
  ∀ k j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ζ, SchwartzMap.seminorm ℝ k j (A x ζ) ≤ C*(1+‖ζ‖)

/-- A uniformly bounded, normalized Schwartz family remains bounded
after the actual Fourier transform, giving all decay seminorms of its
profiles in eta. -/
theorem exists_radian_amplitude_profile_rapid_bound
    (A : E → E → SchwartzMap E ℂ) (hA : RadianAmplitudeInputOrderOne A) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x η ζ,
      ‖η‖^k * ‖radianSchwartzAmplitudeProfile A x η ζ‖ ≤ C*(1+‖ζ‖) := by
  let N (p : E × E) : SchwartzMap E ℂ := (1+‖p.2‖)⁻¹ • A p.1 p.2
  let L : SchwartzMap E ℂ →L[ℝ] SchwartzMap E ℂ := SchwartzMap.fourierTransformCLM ℝ
  have nb : IsVonNBounded ℝ (range N) := by
    apply (schwartz_withSeminorms ℝ E ℂ).isVonNBounded_iff_seminorm_bounded.mpr
    rintro ⟨i,j⟩
    obtain ⟨C,C0,hC⟩ := hA i j
    refine ⟨C+1,by positivity,?_⟩
    rintro _ ⟨p,rfl⟩
    have wp : 0 < 1+‖p.2‖ := by positivity
    have np : schwartzSeminormFamily ℝ E ℂ (i,j) (N p) =
        (SchwartzMap.seminorm ℝ i j (A p.1 p.2)) / (1+‖p.2‖) := by
      simp only [N,SchwartzMap.schwartzSeminormFamily_apply,map_smul_eq_mul,
        Real.norm_of_nonneg (inv_nonneg.mpr wp.le)]
      rw [div_eq_inv_mul]
    rw [np]
    exact ((div_le_iff₀ wp).mpr (hC p.1 p.2)).trans_lt (lt_add_of_pos_right _ zero_lt_one)
  have lb := nb.image L
  obtain ⟨C,Cp,hC⟩ := (schwartz_withSeminorms ℝ E ℂ).isVonNBounded_iff_seminorm_bounded.mp lb (k,0)
  refine ⟨C,Cp.le,?_⟩
  intro x η ζ
  have m : L (N (x,ζ)) ∈ L '' (range N) := ⟨N (x,ζ),mem_range_self (x,ζ),rfl⟩
  have hn : SchwartzMap.seminorm ℝ k 0 (L (N (x,ζ))) ≤ C := by
    simpa only [SchwartzMap.schwartzSeminormFamily_apply] using (hC _ m).le
  have normal := (SchwartzMap.norm_pow_mul_le_seminorm ℝ (L (N (x,ζ))) k η).trans hn
  have leval : L (N (x,ζ)) η = (1+‖ζ‖)⁻¹ • radianSchwartzAmplitudeProfile A x η ζ := by
    have eq : L (N (x,ζ)) = (1+‖ζ‖)⁻¹ • L (A x ζ) := L.map_smul _ _
    rw [eq,SchwartzMap.smul_apply]
    rfl
  have wp : 0 < 1+‖ζ‖ := by positivity
  rw [leval,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr wp.le)] at normal
  apply (div_le_iff₀ wp).mp
  calc
    _ = ‖η‖^k * ((1+‖ζ‖)⁻¹ * ‖radianSchwartzAmplitudeProfile A x η ζ‖) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ C := normal

/-- First moments of the actual input Fourier profiles follow from the
original Schwartz seminorm estimates and continuity in frequency. -/
theorem exists_radian_amplitude_fourier_bounds
    (A : E → E → SchwartzMap E ℂ) (hA : RadianAmplitudeInputOrderOne A)
    (hC : ∀ x, Measurable (fun p : E × E => radianSchwartzAmplitudeProfile A x p.1 p.2)) :
    ∃ w : E → ℝ, RadianAmplitudeFourierBounds (radianSchwartzAmplitudeProfile A) w := by
  let r := (volume : Measure E).integrablePower
  let l := r+1
  obtain ⟨D,D0,hD⟩ := exists_radian_amplitude_profile_rapid_bound A hA 0
  obtain ⟨F,F0,hF⟩ := exists_radian_amplitude_profile_rapid_bound A hA l
  let C : ℝ := 2^l * (D+F)
  let w (η : E) := C * (1+‖η‖) ^ (-(l : ℝ))
  have C0 : 0 ≤ C := by dsimp only [C]; positivity
  have cw : Continuous w := (continuous_const.mul ((continuous_const.add continuous_norm).rpow_const
    (fun η => Or.inl (by positivity))))
  have τ0 : 0 ≤ tau := mul_nonneg (by norm_num) Real.pi_pos.le
  refine ⟨w,⟨hC,cw.measurable,fun η => ?_,?_,fun x η ζ => ?_⟩⟩
  · exact mul_nonneg C0 (Real.rpow_nonneg (by positivity) _)
  · have c : Continuous (fun η : E => w η * (1+tau*‖η‖)) :=
      cw.mul (continuous_const.add (continuous_const.mul continuous_norm))
    apply ((SchwartzMap.integrable_pow_neg_integrablePower (volume : Measure E)).const_mul
      (C*(1+tau))).mono' c.aestronglyMeasurable
    filter_upwards with η
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg C0 (Real.rpow_nonneg (by positivity) _))
      (by positivity))]
    have e : (1+‖η‖) ^ (-(l : ℝ)) * (1+‖η‖) = (1+‖η‖) ^ (-(r : ℝ)) := by
      calc
        _ = (1+‖η‖) ^ (-(l : ℝ)) * (1+‖η‖) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by
          rw [← Real.rpow_add (by positivity)]
          congr 1
          simp [l]
    have h : 1+tau*‖η‖ ≤ (1+tau)*(1+‖η‖) := by
      nlinarith only [τ0,norm_nonneg η]
    calc
      _ ≤ C * (1+‖η‖) ^ (-(l : ℝ)) * ((1+tau)*(1+‖η‖)) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg C0 (Real.rpow_nonneg (by positivity) _))
      _ = C*(1+tau)*((1+‖η‖) ^ (-(l : ℝ)) * (1+‖η‖)) := by ring
      _ = _ := by rw [e]
  · have g := SchwartzMap.pow_mul_le_of_le_of_pow_mul_le (norm_nonneg η)
      (norm_nonneg (radianSchwartzAmplitudeProfile A x η ζ))
      (show ‖radianSchwartzAmplitudeProfile A x η ζ‖ ≤ D*(1+‖ζ‖) by
        simpa only [pow_zero,one_mul] using hD x η ζ)
      (show ‖η‖^(0+l) * ‖radianSchwartzAmplitudeProfile A x η ζ‖ ≤ F*(1+‖ζ‖) by
        simpa only [zero_add] using hF x η ζ)
    simp only [pow_zero,one_mul] at g
    exact g.trans_eq (by dsimp only [w,C]; ring)

end Burnett.A03
