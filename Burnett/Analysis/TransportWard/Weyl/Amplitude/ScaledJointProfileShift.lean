import Burnett.Analysis.TransportWard.Weyl.Amplitude.WeightedParameterJets
import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalAmplitudeShift

set_option autoImplicit false
set_option maxHeartbeats 7100000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology BigOperators

/-- The exact change in the complete profile at a frequency shift.
The output base coordinate is shared. -/
def radianJointProfileShift (f : RadianParameter → ℂ) (v : E) (p : RadianParameter) : ℂ :=
  f (p+(0,v)) - f p

private def frequencyReweightedParameterJet (f : RadianParameter → ℂ)
    (n : ℕ) (x : E) (s : ℝ) (q : E) : RadianParameterJet n ℂ :=
  (iteratedFDeriv ℝ n f (x,q)).compContinuousLinearMap (fun _ => radianParameterScale s)

private theorem frequency_reweighted_parameter_jet_derivative
    (f : RadianParameter → ℂ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : E) (s : ℝ) (q : E) :
    let J := iteratedFDeriv ℝ n f
    let L := ContinuousLinearMap.inr ℝ E E
    let T := ContinuousMultilinearMap.compContinuousLinearMapL (G := ℂ)
      (fun _ : Fin n => radianParameterScale s)
    HasFDerivAt (frequencyReweightedParameterJet f n x s) (T.comp ((fderiv ℝ J (x,q)).comp L)) q := by
  dsimp only
  let J := iteratedFDeriv ℝ n f
  let L := ContinuousLinearMap.inr ℝ E E
  let T := ContinuousMultilinearMap.compContinuousLinearMapL (G := ℂ)
    (fun _ : Fin n => radianParameterScale s)
  let H (z : E) := (x,0)+L z
  have Hq : H q = (x,q) := by simp [H,L]
  have hJ : ContDiff ℝ ∞ J :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show (⊤ : ℕ∞) + (n : ℕ∞) ≤ ⊤ by simp))
  have d : HasFDerivAt J (fderiv ℝ J (x,q)) (H q) := by
    rw [Hq]
    exact (hJ.differentiable (by norm_num) (x,q)).hasFDerivAt
  have hH : HasFDerivAt H L q := (L.hasFDerivAt).const_add (x,0)
  have eq : frequencyReweightedParameterJet f n x s = T ∘ (J ∘ H) := by
    funext z
    change _ = T (J (H z))
    rw [show H z = (x,z) from by simp [H,L]]
    rfl
  rw [eq]
  exact T.hasFDerivAt.comp q (d.comp q hH)

private theorem norm_frequency_reweighted_parameter_derivative_le
    (f : RadianParameter → ℂ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : E) (s : ℝ) (s0 : 0 ≤ s) (q : E)
    (M : ℝ) (M1 : 1 ≤ M) (ratio : s ≤ M*radianFrequencyWeight q)
    (w : ℝ) (w0 : 0 ≤ w)
    (hfq : ‖radianScaledParameterJet f (n+1) (x,q)‖ ≤ w*radianFrequencyWeight q) :
    ‖fderiv ℝ (frequencyReweightedParameterJet f n x s) q‖ ≤ w*M^n := by
  let J := iteratedFDeriv ℝ n f
  let L := ContinuousLinearMap.inr ℝ E E
  let T := ContinuousMultilinearMap.compContinuousLinearMapL (G := ℂ)
    (fun _ : Fin n => radianParameterScale s)
  let g := radianFrequencyWeight q
  have gp : 0 < g := radian_frequency_weight_pos q
  have mp : 0 ≤ M := zero_le_one.trans M1
  have deriv := (frequency_reweighted_parameter_jet_derivative f hf n x s q).fderiv
  change fderiv ℝ (frequencyReweightedParameterJet f n x s) q = T.comp ((fderiv ℝ J (x,q)).comp L) at deriv
  rw [deriv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  let α : Fin (n+1) → RadianParameter := Fin.cons (L (g⁻¹ • u))
    (fun j => radianParameterScale (s/g) (v j))
  let β : Fin (n+1) → RadianParameter := Fin.cons (L u) (fun j => radianParameterScale s (v j))
  have Lnorm (z : E) : ‖L z‖ = ‖z‖ := by simp [L]
  have a0 : ‖α 0‖ = g⁻¹*‖u‖ := by
    simp only [α,Fin.cons_zero,Lnorm,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr gp.le)]
  have αnext (i : Fin n) : ‖α i.succ‖ ≤ M*‖v i‖ := by
    have hratio : s/g ≤ M := (div_le_iff₀ gp).mpr ratio
    have ctrl := (norm_radian_parameter_scale_le (s/g)).trans
      (max_le M1 (by rw [Real.norm_of_nonneg (div_nonneg s0 gp.le)]; exact hratio))
    exact ((radianParameterScale (s/g)).le_opNorm (v i)).trans
      (mul_le_mul_of_nonneg_right ctrl (norm_nonneg _))
  have ascale : (fun i => radianParameterScale g (α i)) = β := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [α,β,Fin.cons_zero,L,radian_parameter_scale_apply,ContinuousLinearMap.inr_apply,
        smul_smul,mul_inv_cancel₀ gp.ne',one_smul]
    · simp only [α,β,Fin.cons_succ,radian_parameter_scale_mul]
      rw [show g*(s/g) = s by field_simp]
  have val : ((T.comp ((fderiv ℝ J (x,q)).comp L)) u) v =
      radianScaledParameterJet f (n+1) (x,q) α := by
    change (fderiv ℝ J (x,q) (L u)) (fun j => radianParameterScale s (v j)) =
      iteratedFDeriv ℝ (n+1) f (x,q) (fun j => radianParameterScale g (α j))
    rw [ascale,iteratedFDeriv_succ_apply_left]
    simp only [β,Fin.cons_zero,Fin.tail_cons,J]
  rw [val]
  have prod : ∏ i, ‖α i‖ ≤ (g⁻¹*‖u‖)*(M^n*∏ j, ‖v j‖) := by
    rw [Fin.prod_univ_succ,a0]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ ∏ j, M*‖v j‖ := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => αnext j)
      _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hfq' : ‖radianScaledParameterJet f (n+1) (x,q)‖ ≤ w*g := hfq
  have p0 : 0 ≤ ∏ i, ‖α i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have both : ‖radianScaledParameterJet f (n+1) (x,q)‖ * (∏ i, ‖α i‖) ≤
      (w*g)*((g⁻¹*‖u‖)*(M^n*∏ j, ‖v j‖)) :=
    mul_le_mul hfq' prod p0 (mul_nonneg w0 gp.le)
  calc
    _ ≤ ‖radianScaledParameterJet f (n+1) (x,q)‖ * ∏ i, ‖α i‖ := (radianScaledParameterJet f (n+1) (x,q)).le_opNorm α
    _ ≤ (w*g)*((g⁻¹*‖u‖)*(M^n*∏ j, ‖v j‖)) := both
    _ = (g*g⁻¹)*((w*M^n)*‖u‖*∏ j, ‖v j‖) := by ring
    _ = _ := by rw [mul_inv_cancel₀ gp.ne',one_mul]

private theorem radian_scaled_shift_jet_difference
    (f : RadianParameter → ℂ) (hf : ContDiff ℝ ∞ f) (p : RadianParameter) (v : E) (n : ℕ) :
    radianScaledParameterJet (radianJointProfileShift f v) n p =
      frequencyReweightedParameterJet f n p.1 (radianFrequencyWeight p.2) (p.2+v) -
        frequencyReweightedParameterJet f n p.1 (radianFrequencyWeight p.2) p.2 := by
  rcases p with ⟨x,q⟩
  let p : RadianParameter := (x,q)
  change radianScaledParameterJet (radianJointProfileShift f v) n p =
    frequencyReweightedParameterJet f n x (radianFrequencyWeight q) (q+v) -
      frequencyReweightedParameterJet f n x (radianFrequencyWeight q) q
  let G : RadianParameter → ℂ := fun q => f (q+(0,v))
  have g : ContDiff ℝ ∞ G := hf.comp (contDiff_id.add contDiff_const)
  have showEq : radianJointProfileShift f v = G + (-f) := funext fun q => sub_eq_add_neg _ _
  have hg : ContDiffAt ℝ n G p := (g.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
  have hn : ContDiffAt ℝ n (-f) p :=
    (hf.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).neg.contDiffAt
  unfold radianScaledParameterJet
  rw [showEq,iteratedFDeriv_add_apply hg hn,iteratedFDeriv_neg_apply]
  have tr : iteratedFDeriv ℝ n G p = iteratedFDeriv ℝ n f (p+(0,v)) :=
    iteratedFDeriv_comp_add_right n (0,v) p
  have atShift : p+(0,v) = (x,q+v) := by simp [p]
  rw [tr,atShift]
  ext m
  simp only [frequencyReweightedParameterJet,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.add_apply,ContinuousMultilinearMap.neg_apply,sub_eq_add_neg,p]

/-- In the actual jointly differentiated shift, one frequency
direction cancels the symbol weight of order one. The normalization
of the other joint directions costs only a polynomial of the shift. -/
theorem norm_scaled_radian_joint_profile_shift_le
    (f : RadianParameter → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) (p : RadianParameter)
    (v : E) (w : ℝ) (w0 : 0 ≤ w)
    (jet : ∀ q, ‖radianScaledParameterJet f (n+1) q‖ ≤ w*radianFrequencyWeight q.2) :
    ‖radianScaledParameterJet (radianJointProfileShift f v) n p‖ ≤ w*(1+‖v‖)^n*‖v‖ := by
  let M := 1+‖v‖
  let K := frequencyReweightedParameterJet f n p.1 (radianFrequencyWeight p.2)
  let B := closedBall p.2 ‖v‖
  have bp : p.2 ∈ B := mem_closedBall_self (norm_nonneg v)
  have bq : p.2+v ∈ B := by simp [B,mem_closedBall,dist_eq_norm]
  have M1 : 1 ≤ M := le_add_of_nonneg_right (norm_nonneg v)
  have dK (q : E) (_ : q ∈ B) : DifferentiableAt ℝ K q :=
    (frequency_reweighted_parameter_jet_derivative f hf n p.1 (radianFrequencyWeight p.2) q).differentiableAt
  have der (q : E) (hq : q ∈ B) : ‖fderiv ℝ K q‖ ≤ w*M^n := by
    have hd : ‖p.2-q‖ ≤ ‖v‖ := by rw [← dist_eq_norm,dist_comm]; exact hq
    have rr := (radian_frequency_weight_shift_le p.2 q).trans
      (mul_le_mul_of_nonneg_right (add_le_add_left hd 1) (radian_frequency_weight_pos q).le)
    exact norm_frequency_reweighted_parameter_derivative_le f hf n p.1
      (radianFrequencyWeight p.2) (radian_frequency_weight_pos p.2).le q M M1 rr w w0 (jet (p.1,q))
  have b := Convex.norm_image_sub_le_of_norm_fderiv_le dK der (convex_closedBall p.2 ‖v‖) bp bq
  rw [show p.2+v-p.2 = v by abel] at b
  rw [radian_scaled_shift_jet_difference f hf]
  exact b

end Burnett.A03
