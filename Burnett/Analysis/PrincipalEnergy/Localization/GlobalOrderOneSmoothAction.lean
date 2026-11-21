import Burnett.Analysis.PrincipalEnergy.Localization.UniformCompactH1Pair
import Burnett.Analysis.PrincipalEnergy.Localization.FourierPhaseJets
import Burnett.Analysis.PrincipalEnergy.Localization.IntegratedSymbolJets
import Burnett.Analysis.PrincipalEnergy.Localization.ProductPartialJets

set_option autoImplicit false
set_option maxHeartbeats 5300000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Metric Burnett.Analysis.FirstOrderDyadic Burnett.Fourier
open scoped FourierTransform ContDiff BigOperators

/-- All base jets of the genuine Fourier action exist under the order-one
growth bounds of the pure base derivatives. -/
theorem firstOrderAction_contDiff_of_pureBaseOrder {a : Space → Space → ℂ}
    (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (f : SchwartzMap Space ℂ) :
    ContDiff ℝ ∞ (firstOrderAction a f) := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let P (ξ x : Space) : ℂ := Real.fourierChar (inner ℝ ξ x)
  let U (ξ x : Space) := F ξ • (P ξ x * a x ξ)
  have hP : ContDiff ℝ ∞ (fun p : Space × Space => P p.2 p.1) := by
    dsimp only [P]
    simp only [Real.fourierChar_apply]
    have hInner : ContDiff ℝ ∞ (fun p : Space × Space => inner ℝ p.2 p.1) :=
      contDiff_snd.inner ℝ contDiff_fst
    have hArg : ContDiff ℝ ∞ (fun p : Space × Space => 2 * Real.pi * inner ℝ p.2 p.1) :=
      contDiff_const.mul hInner
    exact ((Complex.ofRealCLM.contDiff.comp hArg).mul contDiff_const).cexp
  have hJoint : ContDiff ℝ ∞ (fun p : Space × Space => U p.2 p.1) :=
    ((F.smooth ⊤).comp contDiff_snd).mul (hP.mul hs)
  have hSmooth (ξ : Space) : ContDiff ℝ ∞ (U ξ) := by
    have hPair : ContDiff ℝ ∞ (fun x : Space => (x,ξ)) := contDiff_id.prodMk contDiff_const
    change ContDiff ℝ ∞ ((fun p : Space × Space => U p.2 p.1) ∘ (fun x : Space => (x,ξ)))
    exact hJoint.comp hPair
  have hMeas (n : ℕ) (x : Space) :
      AEStronglyMeasurable (fun ξ => iteratedFDeriv ℝ n (U ξ) x) (volume : Measure Space) := by
    letI : SecondCountableTopologyEither Space (ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ) :=
      secondCountableTopologyEither_of_left _ _
    have hJ := contDiff_firstPartialJet hJoint n
    have hPair : Continuous (fun ξ : Space => (x,ξ)) := continuous_const.prodMk continuous_id
    change AEStronglyMeasurable
      ((fun p : Space × Space => iteratedFDeriv ℝ n (U p.2) p.1) ∘ (fun ξ => (x,ξ))) volume
    exact (hJ.continuous.comp hPair).aestronglyMeasurable
  choose C hC hc using hb
  have hDom (n : ℕ) (x : Space) : ∃ W : Space → ℝ, Integrable W (volume : Measure Space) ∧
      ∀ ξ y, y ∈ ball x 1 → ‖iteratedFDeriv ℝ n (U ξ) y‖ ≤ W ξ := by
    let T := ∑ j ∈ Finset.range (n+1), C j
    let H : ℝ := 1+2*Real.pi
    have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => hC j)
    have hH : 1 ≤ H := le_add_of_nonneg_right (by positivity : 0 ≤ 2*Real.pi)
    let M := (2:ℝ)^n * H^n * T
    refine ⟨fun ξ => M*((1+‖ξ‖)^(n+1)*‖F ξ‖), (integrable_schwartz_weighted F _).const_mul M,
      fun ξ y _ => ?_⟩
    let W := H*(1+‖ξ‖)
    have hW : 1 ≤ W := one_le_mul_of_one_le_of_one_le hH (le_add_of_nonneg_right (norm_nonneg _))
    have hPa := (fourier_phase_contDiff_and_derivative_bound ξ).1
    have hA : ContDiff ℝ ∞ (fun z => a z ξ) :=
      hs.comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => ξ)))
    have hPt (j : ℕ) (hj : j ≤ n) : ‖iteratedFDeriv ℝ j (P ξ) y‖ ≤ W^n := by
      have hPhase : 2*Real.pi*‖ξ‖ ≤ W := by
        dsimp only [W, H]
        nlinarith only [Real.pi_pos, norm_nonneg ξ]
      exact ((fourier_phase_contDiff_and_derivative_bound ξ).2 j y).trans
        ((pow_le_pow_left₀ (by positivity) hPhase j).trans (pow_le_pow_right₀ hW hj))
    have hAt (j : ℕ) (hj : j ≤ n) : ‖iteratedFDeriv ℝ j (fun z => a z ξ) y‖ ≤ T*(1+‖ξ‖) :=
      (hc j y ξ).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hC k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) (by positivity))
    have hProd : ‖iteratedFDeriv ℝ n (fun z => P ξ z*a z ξ) y‖ ≤ (2:ℝ)^n * W^n * (T*(1+‖ξ‖)) := by
      calc
        _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
            ‖iteratedFDeriv ℝ j (P ξ) y‖ * ‖iteratedFDeriv ℝ (n-j) (fun z => a z ξ) y‖ :=
          norm_iteratedFDeriv_mul_le hPa hA y (by exact_mod_cast le_top)
        _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * W^n * (T*(1+‖ξ‖)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hPt j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
            (Nat.cast_nonneg _)) (hAt (n-j) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
        _ = _ := by
          simp only [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    change ‖iteratedFDeriv ℝ n (fun z => F ξ • (P ξ z*a z ξ)) y‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hPa.mul hA).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul]
    refine (mul_le_mul_of_nonneg_left hProd (norm_nonneg _)).trans_eq ?_
    dsimp only [M, W]
    rw [mul_pow, pow_succ]
    ring
  have hForm : firstOrderAction a f = fun x => ∫ ξ, U ξ x := by
    funext x
    rw [firstOrderAction, Real.fourierIntegralInv_eq]
    apply integral_congr_ae
    filter_upwards with ξ
    change Real.fourierChar (inner ℝ ξ x) • (a x ξ*F ξ) = U ξ x
    simp only [U, P, Circle.smul_def, smul_eq_mul]
    ring
  rw [hForm]
  exact (contDiff_integral_of_locally_dominated_jets (volume : Measure Space)
    U hSmooth hMeas hDom).1

end Burnett.Analysis.CarlesonEmbedding
