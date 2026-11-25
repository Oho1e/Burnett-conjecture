import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableCoefficientTail
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableDyadicScales
import Burnett.Analysis.SignedFourierWindow.AnnularSquareLp

set_option autoImplicit false
set_option maxHeartbeats 4300000
noncomputable section
namespace Burnett.A06

open MeasureTheory Set Metric Finset
open Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open scoped ENNReal NNReal BigOperators

private theorem sq_norm_add (z w : ℂ) :
    ‖z+w‖ₑ^2 ≤ 2*(‖z‖ₑ^2+‖w‖ₑ^2) := by
  have h : ‖z+w‖^2 ≤ 2*(‖z‖^2+‖w‖^2) := by
    calc
      _ ≤ (‖z‖+‖w‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _
      _ ≤ _ := by nlinarith only [sq_nonneg (‖z‖-‖w‖)]
  have e := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _),ENNReal.ofReal_pow (norm_nonneg _),ENNReal.ofReal_pow (norm_nonneg _)] at e
  simpa only [ofReal_norm_eq_enorm,ENNReal.ofReal_ofNat] using e

private theorem eLpNorm_square {V : Type*} [NormedAddCommGroup V] (f : E → V) (μ : Measure E) :
    eLpNorm f 2 μ ^ (2:ℕ) = ∫⁻ x, ‖f x‖ₑ^2 ∂μ := by
  simpa using eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := 2) (by norm_num)

private theorem normalized_annularKernel_integrable (a : SchwartzMap E ℂ) {t : ℝ} (ht : 0<t) (j : ℕ) :
    Integrable (annularKernel a t 0 j) :=
  shiftedSpatialKernel_integrable _ (mul_pos (by positivity) ht) _

private theorem kernelApply_ball_split (K : E → ℂ) (hK : Integrable K) (hKC : Continuous K)
    (F : E → ℂ) (hm : Measurable F) {L : ℝ} (hF : ∀ x, ‖F x‖≤L)
    {B : Set E} (hB : MeasurableSet B) (x : E) :
    kernelApply K F x = kernelApply K (B.indicator F) x + kernelApply K (Bᶜ.indicator F) x := by
  have hf : Integrable (fun y => K (x-y)*F y) := by
    have hk : Integrable (fun y => K (x-y)) :=
      ((volume : Measure E).measurePreserving_sub_left x).integrable_comp_emb
        (Homeomorph.subLeft x).measurableEmbedding |>.mpr hK
    refine (hk.norm.mul_const L).mono' ((hKC.comp (by fun_prop)).measurable.mul hm).aestronglyMeasurable ?_
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hF _) (norm_nonneg _)
  have dom (S : Set E) (y : E) : K (x-y)*S.indicator F y =
      S.indicator (fun z => K (x-z)*F z) y := by
    by_cases hy : y∈S <;> simp [hy]
  unfold kernelApply
  simp_rw [dom]
  rw [← integral_add (hf.indicator hB) (hf.indicator hB.compl)]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y∈B <;> simp [hy]

/-- The actual physical Fourier-annular filters of an L∞ input have a
uniform Carleson square mass on every ball and any finite set of the smaller
scales. The input need not have a global L² bound. -/
theorem exists_annularCoefficient_ball_square_packing (a : SchwartzMap E ℂ)
    (ha : HasCompactSupport (a : E → ℂ)) (hAnn : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ F : E → ℂ, Measurable F → ∀ L : ℝ≥0, (∀ x, ‖F x‖≤L) →
      ∀ (center : E) {R t : ℝ}, 0<R → 0<t → ∀ (J : Finset ℕ),
      (∀ j ∈ J, dyadicScale t j ≤ R) →
      (∫⁻ x in ball center R, ∑ j ∈ J, ‖kernelApply (annularKernel a t 0 j) F x‖ₑ^2) ≤
        C*(L : ℝ≥0∞)^2*volume (ball center R) := by
  obtain ⟨D,hD,squareBound⟩ := annular_square_all_Lp a ha hAnn 2 (by norm_num)
  let ψ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  let M := ENNReal.ofReal (∫ z : E, ‖z‖*‖ψ z‖)
  refine ⟨2*(16*D^2+2*M^2),by finiteness,?_⟩
  intro F hm L hF center R t hR ht J hJ
  let B := ball center R
  let B₂ := ball center (2*R)
  let f := B₂.indicator F
  let g := B₂ᶜ.indicator F
  let K j := annularKernel a t 0 j
  let S (x : E) := ∑ j ∈ J, ‖kernelApply (K j) f x‖ₑ^2
  let Q j := ENNReal.ofReal (dyadicScale t j/R)
  let e : Fin J.card ↪ ℕ := (J.orderEmbOfFin rfl).toEmbedding
  have hFₑ (x : E) : ‖F x‖ₑ ≤ (L : ℝ≥0∞) := by
    simpa only [ofReal_norm_eq_enorm,ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hF x)
  have hf : MemLp f 2 volume := by
    letI : IsFiniteMeasure ((volume : Measure E).restrict B₂) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    apply (memLp_indicator_iff_restrict measurableSet_ball).mpr
    exact MemLp.of_bound hm.aestronglyMeasurable (L : ℝ) (.of_forall hF)
  have hnear : (∫⁻ x in B, S x) ≤ 16*D^2*(L : ℝ≥0∞)^2*volume B := by
    have hMass : eLpNorm f 2 volume ^ (2:ℕ) ≤ (L : ℝ≥0∞)^2*volume B₂ := by
      rw [eLpNorm_square]
      calc
        _ ≤ ∫⁻ x, B₂.indicator (fun _ => (L : ℝ≥0∞)^2) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x∈B₂
          · simp only [f,indicator_of_mem hx]
            exact pow_le_pow_left' (hFₑ x) 2
          · simp [f,indicator_of_notMem hx]
        _ = _ := by rw [lintegral_indicator measurableSet_ball,lintegral_const,Measure.restrict_apply_univ]
    have hE (x : E) : S x = ‖annularSquare e a t (0 : E) f x‖ₑ^2 := by
      have hmap : (Finset.univ.map e) = J := J.map_orderEmbOfFin_univ rfl
      calc
        _ = ∑ j : Fin J.card, ‖kernelApply (K (e j)) f x‖ₑ^2 :=
          (congrArg (fun P : Finset ℕ => ∑ j ∈ P, ‖kernelApply (K j) f x‖ₑ^2) hmap).symm.trans
            (sum_map _ _ _)
        _ = _ := by
          change _ = ‖Real.sqrt (∑ j : Fin J.card, ‖kernelApply (K (e j)) f x‖^2)‖ₑ^2
          rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _),← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
            Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _),ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
          simp only [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm_eq_enorm]
    have hsquare := squareBound t ht 0 J.card e f (by simpa only [ENNReal.ofReal_ofNat] using hf)
    simp only [ENNReal.ofReal_ofNat,norm_zero,add_zero,ENNReal.ofReal_one,mul_one] at hsquare
    have hdoub : volume B₂ = (16 : ℝ≥0∞)*volume B := by
      change volume (ball center (2*R)) = (16 : ℝ≥0∞)*volume (ball center R)
      rw [Measure.addHaar_ball_mul_of_pos volume center (by norm_num : (0:ℝ)<2) R,
        ← Measure.addHaar_ball_center volume center R,finrank_euclideanSpace_fin]
      norm_num
    calc
      _ ≤ ∫⁻ x, S x := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
      _ = eLpNorm (annularSquare e a t 0 f) 2 volume ^ (2:ℕ) := by simp_rw [hE,eLpNorm_square]
      _ ≤ (D*eLpNorm f 2 volume)^2 := pow_le_pow_left' hsquare 2
      _ ≤ _ := by
        rw [mul_pow]
        exact (mul_le_mul_left' hMass _).trans_eq (by rw [hdoub]; ac_rfl)
  have htailSum : (∑ j ∈ J, Q j^2) ≤ 2 := by
    have hr := coefficientWindow_square_ratios_sum_le J ht hR hJ
    have he := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)] at he
    have hQ (j : ℕ) : ENNReal.ofReal ((dyadicScale t j/R)^2) = Q j^2 := by
      rw [ENNReal.ofReal_pow (by unfold dyadicScale; positivity : 0 ≤ dyadicScale t j/R)]
    simpa only [hQ,ENNReal.ofReal_ofNat] using he
  have hsplit (j : ℕ) (x : E) : kernelApply (K j) F x =
      kernelApply (K j) f x+kernelApply (K j) g x := by
    exact kernelApply_ball_split _ (normalized_annularKernel_integrable a ht j)
      (by unfold annularKernel shiftedSpatialKernel; fun_prop) F hm hF measurableSet_ball x
  have hfar (j : ℕ) (x : E) (hx : x∈B) : ‖kernelApply (K j) g x‖ₑ ≤ (L : ℝ≥0∞)*Q j*M := by
    have hs : 0<dyadicScale t j := by unfold dyadicScale; positivity
    let T := ∫ z : E, ‖z‖*‖ψ z‖
    have h : ‖kernelApply (K j) g x‖ ≤ (L : ℝ)*(dyadicScale t j/R)*T :=
      coefficientWindow_off_doubled_ball ψ hs hR center x hx F L.2 hF
    calc
      _ ≤ ENNReal.ofReal ((L : ℝ)*(dyadicScale t j/R)*T) := by
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal ((L : ℝ)*(dyadicScale t j/R))*ENNReal.ofReal T :=
        ENNReal.ofReal_mul (p := (L : ℝ)*(dyadicScale t j/R)) (q := T)
          (mul_nonneg L.2 (div_nonneg hs.le hR.le))
      _ = _ := by
        have eq : ENNReal.ofReal ((L : ℝ)*(dyadicScale t j/R)) = (L : ℝ≥0∞)*Q j :=
          (ENNReal.ofReal_mul (p := (L : ℝ)) (q := dyadicScale t j/R) L.2).trans
            (congrArg (fun m => m*Q j) ENNReal.ofReal_coe_nnreal)
        exact congrArg (fun m => m*M) eq
  have hMeas : Measurable S := by
    refine measurable_sum _ fun j _ => ?_
    exact (kernelApply_measurable_ae (K j) (by unfold K annularKernel shiftedSpatialKernel; fun_prop)
      f hf.1).enorm.pow_const _
  calc
    _ ≤ ∫⁻ x in B, 2 * (S x+(L : ℝ≥0∞)^2*M^2*2) := by
      refine setLIntegral_mono' measurableSet_ball ?_
      intro x hx
      have hTerm (j : ℕ) : ‖kernelApply (K j) F x‖ₑ^2 ≤
          2*(‖kernelApply (K j) f x‖ₑ^2+(L : ℝ≥0∞)^2*M^2*Q j^2) := by
        rw [hsplit]
        refine (sq_norm_add _ _).trans (mul_le_mul_left' (add_le_add_left ?_ _) _)
        exact (pow_le_pow_left' (hfar j x hx) 2).trans_eq (by simp only [mul_pow]; ac_rfl)
      refine (sum_le_sum fun j _ => hTerm j).trans ?_
      rw [← mul_sum,sum_add_distrib,← mul_sum]
      exact mul_le_mul_left' (add_le_add_left (mul_le_mul_left' htailSum _) _) _
    _ = 2*((∫⁻ x in B, S x)+(L : ℝ≥0∞)^2*M^2*2*volume B) := by
      rw [lintegral_const_mul' _ _ (by norm_num),lintegral_add_left hMeas,
        lintegral_const,Measure.restrict_apply_univ]
    _ ≤ _ := (mul_le_mul_left' (add_le_add_right hnear _) _).trans_eq (by
      simp only [mul_add,add_mul]; ac_rfl)

end Burnett.A06
