import Burnett.Analysis.TransportWard.Weyl.Amplitude.RadianJointProfileData
import Burnett.Analysis.TransportWard.Weyl.Amplitude.RadianAmplitudePhaseJets

set_option autoImplicit false
set_option maxHeartbeats 6100000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Finset Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology BigOperators

private theorem norm_affine_projected_phase_jet_le (η : E) (p : RadianParameter) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z : RadianParameter => patchFourierPhase η (p.1+z.1)) 0‖ ≤
      (tau*‖η‖)^i := by
  let L := ContinuousLinearMap.fst ℝ E E
  let P (z : E) := patchFourierPhase η (p.1+z)
  have hP : ContDiff ℝ ∞ P := (radian_base_phase_smooth η).comp (contDiff_const.add contDiff_id)
  change ‖iteratedFDeriv ℝ i (P ∘ L) 0‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hP 0 (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))]
  have equ : iteratedFDeriv ℝ i P (L 0) = iteratedFDeriv ℝ i (patchFourierPhase η) p.1 := by
    simp only [P,map_zero,iteratedFDeriv_comp_add_left,add_zero]
  rw [equ]
  have r := (iteratedFDeriv ℝ i (patchFourierPhase η) p.1).norm_compContinuousLinearMap_le
    (fun _ : Fin i => L)
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at r
  exact r.trans ((mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _)
    (ContinuousLinearMap.norm_fst_le ℝ E E))).trans (norm_radian_base_phase_jet_le η p.1 i))

private theorem rapid_profile_section_smooth
    (F : E → RadianParameter → ℂ) (h : RadianRapidJointProfiles F) (η : E) :
    ContDiff ℝ ∞ (F η) := by
  let L (z : RadianParameter) : E × RadianParameter := (η,z)
  have sL : ContDiff ℝ ∞ L := contDiff_const.prodMk contDiff_id
  change ContDiff ℝ ∞ (Function.uncurry F ∘ L)
  exact h.smooth.comp sL

private theorem shifted_profile_section_smooth (f : RadianParameter → ℂ)
    (hf : ContDiff ℝ ∞ f) (v : E) : ContDiff ℝ ∞ (radianJointProfileShift f v) := by
  let L (z : RadianParameter) := z+((0 : E),v)
  have sL : ContDiff ℝ ∞ L := contDiff_id.add contDiff_const
  have c : ContDiff ℝ ∞ (f ∘ L) := hf.comp sL
  exact c.sub hf

set_option maxHeartbeats 2700000 in
private theorem norm_scaled_phased_joint_profile_shift_le_sum
    (F : E → RadianParameter → ℂ) (h : RadianRapidJointProfiles F) (k : ℕ)
    (η : E) (p : RadianParameter) :
    ‖radianScaledParameterJet (radianPhasedJointProfileShift F η) k p‖ ≤
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun z : RadianParameter => patchFourierPhase η (p.1+z.1)) 0‖ *
        ‖radianScaledParameterJet (radianJointProfileShift (F η) (tau • η)) (k-i) p‖ := by
  let s := radianFrequencyWeight p.2
  let P (z : RadianParameter) := patchFourierPhase η (p.1+z.1)
  let R := radianJointProfileShift (F η) (tau • η)
  let L (z : RadianParameter) := p+radianParameterScale s z
  let D := R ∘ L
  have sF : ContDiff ℝ ∞ (F η) := rapid_profile_section_smooth F h η
  have sR : ContDiff ℝ ∞ R := shifted_profile_section_smooth (F η) sF (tau • η)
  have pIn : ContDiff ℝ ∞ (fun z : RadianParameter => p.1+z.1) := contDiff_const.add contDiff_fst
  have sP : ContDiff ℝ ∞ P := (radian_base_phase_smooth η).comp pIn
  have sL : ContDiff ℝ ∞ L := contDiff_const.add (radianParameterScale s).contDiff
  have sD : ContDiff ℝ ∞ D := sR.comp sL
  have ph : ContDiff ℝ ∞ (fun z : RadianParameter => patchFourierPhase η z.1) :=
    (radian_base_phase_smooth η).comp contDiff_fst
  have sG : ContDiff ℝ ∞ (radianPhasedJointProfileShift F η) := ph.mul sR
  have expand : (fun z => radianPhasedJointProfileShift F η (p+radianParameterScale s z)) =
      (fun z => P z * D z) := by
    funext z
    change patchFourierPhase η (p+radianParameterScale s z).1 * D z = P z * D z
    simp only [radian_parameter_scale_apply,Prod.fst_add,P]
  have eq := radian_parameter_jet_affine _ sG k p s
  rw [expand] at eq
  have ek : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  have eqD (j : ℕ) : iteratedFDeriv ℝ j D 0 = radianScaledParameterJet R j p :=
    radian_parameter_jet_affine R sR j p s
  rw [← show iteratedFDeriv ℝ k (fun z => P z * D z) 0 =
    radianScaledParameterJet (radianPhasedJointProfileShift F η) k p from eq]
  have b := norm_iteratedFDeriv_mul_le sP sD (0 : RadianParameter) ek
  simpa only [eqD] using b

private theorem norm_scaled_phased_joint_profile_shift_point
    (F : E → RadianParameter → ℂ) (h : RadianRapidJointProfiles F) (k : ℕ)
    (η : E) (p : RadianParameter) (W : ℝ) (W0 : 0 ≤ W)
    (estimate : ∀ j : ℕ, j ≤ k → ∀ q,
      ‖radianScaledParameterJet (F η) (j+1) q‖ ≤ W*radianFrequencyWeight q.2) :
    ‖radianScaledParameterJet (radianPhasedJointProfileShift F η) k p‖ ≤
      (∑ j ∈ Finset.range (k+1), (k.choose j : ℝ))*W*(1+tau*‖η‖)^(k+1) := by
  let M := 1+tau*‖η‖
  have τ : 0 ≤ tau := mul_nonneg (by norm_num) Real.pi_pos.le
  have m0 : 0 ≤ M := by dsimp only [M]; positivity
  have leM : tau*‖η‖ ≤ M := le_add_of_nonneg_left zero_le_one
  have vnorm : ‖tau • η‖ = tau*‖η‖ := by rw [norm_smul,Real.norm_of_nonneg τ]
  have sF : ContDiff ℝ ∞ (F η) := rapid_profile_section_smooth F h η
  have a (i : ℕ) : ‖iteratedFDeriv ℝ i (fun z : RadianParameter => patchFourierPhase η (p.1+z.1)) 0‖ ≤ M^i :=
    (norm_affine_projected_phase_jet_le η p i).trans (pow_le_pow_left₀ (mul_nonneg τ (norm_nonneg _)) leM i)
  have b (i : ℕ) (hi : i ≤ k) :
      ‖radianScaledParameterJet (radianJointProfileShift (F η) (tau • η)) i p‖ ≤ W*M^(i+1) := by
    have b := norm_scaled_radian_joint_profile_shift_le (F η) sF i p (tau • η) W W0 (estimate i hi)
    rw [vnorm] at b
    calc
      _ ≤ (W*M^i)*(tau*‖η‖) := b
      _ ≤ (W*M^i)*M := mul_le_mul_of_nonneg_left leM (mul_nonneg W0 (pow_nonneg m0 i))
      _ = W*M^(i+1) := by rw [pow_succ]; exact mul_assoc _ _ _
  have sumBound := norm_scaled_phased_joint_profile_shift_le_sum F h k η p
  apply sumBound.trans
  have normSum : ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun z : RadianParameter => patchFourierPhase η (p.1+z.1)) 0‖ *
      ‖radianScaledParameterJet (radianJointProfileShift (F η) (tau • η)) (k-i) p‖ ≤
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*(W*M^(k+1)) := by
    apply Finset.sum_le_sum
    intro i hi
    have ii : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have bi := b (k-i) (Nat.sub_le ..)
    have ca := mul_le_mul_of_nonneg_left (a i) (Nat.cast_nonneg (k.choose i))
    have nm : 0 ≤ (k.choose i : ℝ)*M^i := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg m0 _)
    calc
      _ ≤ ((k.choose i : ℝ)*M^i)*(W*M^(k-i+1)) := mul_le_mul ca bi (norm_nonneg _) nm
      _ = (k.choose i : ℝ)*(W*(M^i*M^(k-i+1))) := by ring
      _ = _ := by rw [← pow_add,show i+(k-i+1)=k+1 by omega]
  refine normSum.trans_eq ?_
  rw [← Finset.sum_mul,← mul_assoc]

/-- Every actual scaled joint jet of the phase times the diagonal
shift has order zero, with only a polynomial price in the input
Fourier parameter. Its arbitrarily rapid decay is preserved. -/
theorem exists_radian_phased_joint_profile_shift_scaled_bound
    (F : E → RadianParameter → ℂ) (h : RadianRapidJointProfiles F) (k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η p,
      ‖radianScaledParameterJet (radianPhasedJointProfileShift F η) k p‖ ≤
        C*((1+‖η‖) ^ (-(N : ℝ))*(1+tau*‖η‖)^(k+1)) := by
  choose A A0 Ab using fun j : ℕ => h.orderOne j N
  let S := ∑ j ∈ Finset.range (k+2), A j
  let Q := ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)
  have S0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => A0 j)
  have Q0 : 0 ≤ Q := Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)
  refine ⟨Q*S,mul_nonneg Q0 S0,fun η p => ?_⟩
  let W := (1+‖η‖) ^ (-(N : ℝ))
  have W0 : 0 ≤ W := Real.rpow_nonneg (by positivity) _
  have z (i : ℕ) (hi : i ≤ k) (q : RadianParameter) :
      ‖radianScaledParameterJet (F η) (i+1) q‖ ≤ (S*W)*radianFrequencyWeight q.2 := by
    have u : A (i+1) ≤ S := Finset.single_le_sum (f := A)
      (fun j _ => A0 j) (Finset.mem_range.mpr (by omega))
    exact (Ab (i+1) η q).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right u W0) (radian_frequency_weight_pos q.2).le)
  have b := norm_scaled_phased_joint_profile_shift_point F h k η p (S*W) (mul_nonneg S0 W0) z
  exact b.trans_eq (by change Q*(S*W)*(1+tau*‖η‖)^(k+1) = (Q*S)*(W*(1+tau*‖η‖)^(k+1)); ring)

end Burnett.A03
