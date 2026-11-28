import Burnett.Analysis.TransportWard.Weyl.TaylorJointRemainder
import Burnett.Analysis.TransportWard.Weyl.CoefficientCommutatorTaylor

set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxRecDepth 1800

noncomputable section

namespace Burnett.V03

open Function Set Filter MeasureTheory Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.CarlesonEmbedding (contDiff_integral_of_locally_dominated_jets integrable_schwartz_weighted)
open scoped ContDiff FourierTransform RealInnerProductSpace BigOperators

local notation "P" => RadianParameter
local notation "W" => radianFrequencyWeight

private theorem coefficientFourierFactor_joint_smooth (c : SchwartzMap E ℂ) :
    ContDiff ℝ ∞ (fun z : E × P => coefficientFourierFactor c z.2.1 z.1) := by
  let F := SchwartzMap.fourierTransformCLM ℂ c
  have hX : ContDiff ℝ ∞ (fun z : E × P => z.2.1) := contDiff_fst.comp contDiff_snd
  have hIn : ContDiff ℝ ∞ (fun z : E × P => (tau * inner ℝ z.1 z.2.1 : ℝ)) :=
    contDiff_const.mul (contDiff_fst.inner ℝ hX)
  have hPhase : ContDiff ℝ ∞ (fun z : E × P => patchFourierPhase z.1 z.2.1) := by
    change ContDiff ℝ ∞ (fun z : E × P => Complex.exp (((tau * inner ℝ z.1 z.2.1 : ℝ) : ℂ)*Complex.I))
    exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp hIn).mul contDiff_const)
  exact hPhase.mul (F.smooth'.comp contDiff_fst)

private theorem norm_projected_phase_jet_le (e : E) (p : P) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q : P => patchFourierPhase e q.1) p‖ ≤ (tau * ‖e‖)^n := by
  let L := ContinuousLinearMap.fst ℝ E E
  change ‖iteratedFDeriv ℝ n (patchFourierPhase e ∘ L) p‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (radian_base_phase_smooth e) p
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (patchFourierPhase e) (L p)‖ * ‖L‖^n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (patchFourierPhase e) (L p)).norm_compContinuousLinearMap_le
          (fun _ : Fin n => L)
    _ ≤ ‖iteratedFDeriv ℝ n (patchFourierPhase e) (L p)‖ :=
      mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ E E))
    _ ≤ _ := norm_radian_base_phase_jet_le e (L p) n

def coefficientTaylorIntegrand (a : E → E → ℂ) (c : SchwartzMap E ℂ)
    (η : E) (p : P) : ℂ :=
  coefficientFourierFactor c p.1 η * linearTaylorRemainder (a p.1) p.2 η

theorem coefficientTaylorIntegrand_joint_smooth {a : E → E → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (c : SchwartzMap E ℂ) :
    ContDiff ℝ ∞ (uncurry (coefficientTaylorIntegrand a c)) :=
  (coefficientFourierFactor_joint_smooth c).mul (linearTaylorRemainder_symbol_parameter_smooth ha)

theorem coefficientTaylorIntegrand_order_minus_one {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (c : SchwartzMap E ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : E, ∀ p : P,
      ‖iteratedFDeriv ℝ n (coefficientTaylorIntegrand a c e) p‖ ≤
        (C * ((W e)^(n+3) * ‖(SchwartzMap.fourierTransformCLM ℂ c) e‖)) / W p.2 := by
  choose D hD hB using linearTaylorRemainder_symbol_joint_order_minus_one ha
  let F := SchwartzMap.fourierTransformCLM ℂ c
  let C := ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*tau^j * D (n-j)
  have hτ : 0 ≤ tau := (mul_pos (by norm_num) Real.pi_pos).le
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hτ j)) (hD (n-j))
  refine ⟨C,hC,fun e p => ?_⟩
  let U (q : P) := patchFourierPhase e q.1
  let V (q : P) := linearTaylorRemainder (a q.1) q.2 e
  have hU : ContDiff ℝ ∞ U := (radian_base_phase_smooth e).comp contDiff_fst
  have hV : ContDiff ℝ ∞ V :=
    (linearTaylorRemainder_symbol_parameter_smooth ha.smooth).comp (contDiff_const.prodMk contDiff_id)
  have hUV : ContDiff ℝ ∞ (fun q => U q * V q) := hU.mul hV
  have he : coefficientTaylorIntegrand a c e = (F e) • fun q => U q * V q := by
    funext q
    simp only [coefficientTaylorIntegrand, coefficientFourierFactor,
      F,U,V,Pi.smul_apply,smul_eq_mul,SchwartzMap.fourierTransformCLM_apply]
    ring
  rw [he,iteratedFDeriv_const_smul_apply (hUV.contDiffAt.of_le
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))),norm_smul]
  have hp := radian_frequency_weight_pos p.2
  have hUBound (j : ℕ) : ‖iteratedFDeriv ℝ j U p‖ ≤ tau^j * (W e)^j := by
    refine (norm_projected_phase_jet_le e p j).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (le_add_of_nonneg_left zero_le_one) j) (pow_nonneg hτ _)
  have hProduct : ‖iteratedFDeriv ℝ n (fun q => U q * V q) p‖ ≤ C * (W e)^(n+3) / W p.2 := by
    apply (norm_iteratedFDeriv_mul_le hU hV p (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).trans
    rw [mul_div_assoc]
    dsimp only [C]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hMoment : (W e)^(j+3) ≤ (W e)^(n+3) :=
      pow_le_pow_right₀ (radian_frequency_weight_one_le e) (Nat.add_le_add_right hjn 3)
    have hN : 0 ≤ (n.choose j : ℝ) := Nat.cast_nonneg _
    have hQ : 0 ≤ (n.choose j : ℝ) * tau^j * D (n-j) :=
      mul_nonneg (mul_nonneg hN (pow_nonneg hτ _)) (hD _)
    calc
      _ ≤ (n.choose j : ℝ) * (tau^j * (W e)^j) * (D (n-j) * (W e)^3 / W p.2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hUBound j) hN) (hB (n-j) e p)
          (norm_nonneg _) (mul_nonneg hN
            (mul_nonneg (pow_nonneg hτ _) (pow_nonneg (radian_frequency_weight_pos e).le _)))
      _ = (n.choose j : ℝ) * tau^j * D (n-j) * ((W e)^(j+3) / W p.2) := by
        rw [pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hMoment hp.le) hQ
  exact (mul_le_mul_of_nonneg_left hProduct (norm_nonneg _)).trans_eq (by ring)

end Burnett.V03
