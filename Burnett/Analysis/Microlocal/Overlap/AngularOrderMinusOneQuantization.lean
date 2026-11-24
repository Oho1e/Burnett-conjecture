import Burnett.Analysis.Microlocal.Overlap.CompactBaseZeroFourier
import Burnett.Analysis.Microlocal.CompactFrequencyCutoff
import Burnett.Analysis.Microlocal.BesselLocalization
import Burnett.Analysis.Fourier.SharpProjection
import Burnett.Analysis.Microlocal.SeparableSquareOperators
import Burnett.Geometry.FlatRigidity.WeakCurvature

/-! Actual compact order-minus-one quantization using the current production Fourier API. -/

set_option autoImplicit false
set_option maxRecDepth 2800
set_option maxHeartbeats 2800000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function Filter MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul coeffMul_toLp)
open Burnett.Microlocal.CompactFrequencyCutoff
  (smoothCutoffSymbol compact_spatial_cutoffs_decaying_multiplier isCompactOperator_integral)
open Burnett.Microlocal.SeparablePositive
open Burnett.X02.SobolevTestJet (D)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Topology

open private oscillatoryCutoff continuous_symbolCLM_oscillatoryCutoff
  norm_fourierMultiplier_sub_le continuous_operatorFamily_of_uniform
  from Burnett.Analysis.Microlocal.CompactFrequencyCutoff

/-- The pure spatial estimates of an order-minus-one symbol. -/
def OrderMinusOneBounds (p : E → E → ℂ) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : E,
    (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => p y ξ) x‖ ≤ C

private theorem baseFourierCoefficient_on_compact (p : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hs : ∀ ξ, tsupport (fun x => p x ξ) ⊆ S) (k ξ : E) :
    baseFourierCoefficient p k ξ = ∫ x in S, baseFourierPhase (-k) x * p x ξ := by
  rw [baseFourierCoefficient, Real.fourierIntegral_eq', ← integral_indicator hS.measurableSet]
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx]
    have he : -2 * Real.pi * inner ℝ x k = 2 * Real.pi * inner ℝ (-k) x := by
      rw [inner_neg_left, real_inner_comm x k]
      ring
    simp only [baseFourierPhase, smul_eq_mul, he]
  · have hz : p x ξ = 0 := image_eq_zero_of_notMem_tsupport (f := fun z => p z ξ)
      (fun h => hx (hs ξ h))
    simp only [indicator_of_notMem hx, hz, smul_zero]

private theorem continuous_baseFourierCoefficient_frequency (p : E → E → ℂ) (S : Set E)
    (hS : IsCompact S) (hs : ∀ ξ, tsupport (fun x => p x ξ) ⊆ S)
    (hp : Continuous (uncurry p)) (k : E) : Continuous (baseFourierCoefficient p k) := by
  let F (ξ x : E) := baseFourierPhase (-k) x * p x ξ
  have hF : Continuous (uncurry F) :=
    (baseFourierPhase_continuous_apply continuous_const continuous_snd).mul (hp.comp continuous_swap)
  exact (continuous_parametric_integral_of_continuous (μ := volume) hF hS).congr
    (fun ξ => (baseFourierCoefficient_on_compact p S hS hs k ξ).symm)

private theorem baseFourierCoefficient_eventually_uniform (p : E → E → ℂ) (S : Set E)
    (hS : IsCompact S) (hs : ∀ ξ, tsupport (fun x => p x ξ) ⊆ S)
    (hp : Continuous (uncurry p)) (C : ℝ) (hC : 0 ≤ C) (hB : ∀ x ξ, ‖p x ξ‖ ≤ C)
    (k : E) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ l in 𝓝 k, ∀ ξ, ‖baseFourierCoefficient p l ξ - baseFourierCoefficient p k ξ‖ ≤ ε := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let F (k : E) (x : S) := baseFourierPhase (-k) x.val
  have hF : Continuous (uncurry F) :=
    baseFourierPhase_continuous_apply continuous_fst.neg (continuous_subtype_val.comp continuous_snd)
  let B := C * volume.real S
  have hB₀ : 0 ≤ B := mul_nonneg hC measureReal_nonneg
  let δ := ε / (B + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hU := (Metric.tendstoUniformly_iff.mp (hF.tendstoUniformly F k)) δ hδ
  filter_upwards [hU] with l hl ξ
  have hI (a : E) : IntegrableOn (fun x => baseFourierPhase (-a) x * p x ξ) S :=
    ((baseFourierPhase_continuous_apply continuous_const continuous_id).mul
      (hp.comp (continuous_id.prodMk continuous_const))).continuousOn.integrableOn_compact hS
  rw [baseFourierCoefficient_on_compact p S hS hs l ξ,
    baseFourierCoefficient_on_compact p S hS hs k ξ, ← integral_sub (hI l) (hI k)]
  have hBound : ∀ᵐ x ∂(volume : Measure E).restrict S,
      ‖baseFourierPhase (-l) x * p x ξ - baseFourierPhase (-k) x * p x ξ‖ ≤ δ * C := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
    have hxF : ‖F l ⟨x, hx⟩ - F k ⟨x, hx⟩‖ < δ := by
      simpa only [dist_eq_norm, norm_sub_rev (F k ⟨x, hx⟩) (F l ⟨x, hx⟩)] using hl ⟨x, hx⟩
    rw [← sub_mul, norm_mul]
    exact mul_le_mul hxF.le (hB x ξ) (norm_nonneg _) hδ.le
  have hNorm := norm_integral_le_of_norm_le (integrableOn_const hS.measure_ne_top) hBound
  calc
    _ ≤ volume.real S * (δ * C) := by
      simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul] using hNorm
    _ = δ * B := by unfold B; ring
    _ ≤ δ * (B + 1) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hδ.le
    _ = ε := div_mul_cancel₀ _ (by positivity)

private theorem coefficient_decay (p : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hs : ∀ ξ, tsupport (fun x => p x ξ) ⊆ S) (hp : ContDiff ℝ ∞ (uncurry p))
    (hd : OrderMinusOneBounds p) :
    ∃ g : E → ℝ, Integrable g ∧ (∀ k, 0 ≤ g k) ∧
      ∀ k ξ, (1 + ‖ξ‖) * ‖baseFourierCoefficient p k ξ‖ ≤ g k := by
  let w (x ξ : E) := (1 + ‖ξ‖) • p x ξ
  have hws (ξ : E) : tsupport (fun x => w x ξ) ⊆ S :=
    (closure_mono (Function.support_const_smul_subset _ _)).trans (hs ξ)
  have hP (ξ : E) : ContDiff ℝ ∞ (fun x => p x ξ) := hp.comp (contDiff_id.prodMk (contDiff_const (c := ξ)))
  have hwSmooth (ξ : E) : ContDiff ℝ ∞ (fun x => w x ξ) := (hP ξ).const_smul _
  have hwOrder (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => w y ξ) x‖ ≤ C := by
    obtain ⟨C, hC, hB⟩ := hd n
    refine ⟨C, hC, fun x ξ => ?_⟩
    have h : ContDiffAt ℝ n (fun x => p x ξ) x :=
      (hP ξ).contDiffAt.of_le (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)
    change ‖iteratedFDeriv ℝ n ((1 + ‖ξ‖) • (fun y => p y ξ)) x‖ ≤ C
    rw [iteratedFDeriv_const_smul_apply h, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖)]
    exact hB x ξ
  obtain ⟨C, hC, hI, hD⟩ := baseFourierCoefficient_dominated
    (compactBaseOrderOne_frequencyWeight ⟨S, hS, hws⟩ hwSmooth hwOrder)
  refine ⟨_, hI, fun k => by positivity, fun k ξ => ?_⟩
  have hscale : baseFourierCoefficient w k ξ = (1 + ‖ξ‖) • baseFourierCoefficient p k ξ := by
    simp only [baseFourierCoefficient, Real.fourierIntegral_eq', w, ← integral_smul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => smul_comm _ _ _
  have hDk := hD k ξ
  rw [hscale, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖)] at hDk
  exact hDk

private theorem norm_bilateral_mode (a b m : BoundedSymbol E) :
    ‖(symbolCLM a).comp ((fourierMultiplier m).comp (symbolCLM b))‖ ≤
      a.bound * (m.bound * b.bound) := by
  have hA : ‖symbolCLM a‖ ≤ a.bound :=
    ContinuousLinearMap.opNorm_le_bound _ a.bound_nonneg (symbolL2_norm_le a)
  have hB : ‖symbolCLM b‖ ≤ b.bound :=
    ContinuousLinearMap.opNorm_le_bound _ b.bound_nonneg (symbolL2_norm_le b)
  have hM : ‖fourierMultiplier m‖ ≤ m.bound :=
    ContinuousLinearMap.opNorm_le_bound _ m.bound_nonneg (fourierMultiplier_norm_le m)
  have hRight : ‖(fourierMultiplier m).comp (symbolCLM b)‖ ≤ m.bound * b.bound :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hM hB (norm_nonneg _) m.bound_nonneg)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hA hRight (norm_nonneg _) a.bound_nonneg)

/-- The actual order-minus-one left quantization on the specified compact right
window is represented by a compact operator, with its exact Schwartz pairings. -/
theorem compact_orderMinusOne_leftAction_model
    (p : E → E → ℂ) (S L : Set E) (hS : IsCompact S) (hL : IsCompact L)
    (hs : ∀ ξ, tsupport (fun x => p x ξ) ⊆ S) (hp : ContDiff ℝ ∞ (uncurry p))
    (hd : OrderMinusOneBounds p) :
    ∃ R : ComplexL2 E →L[ℂ] ComplexL2 E, IsCompactOperator R ∧
      ∀ f v : SchwartzMap E ℂ, tsupport (v : E → ℂ) ⊆ L →
        inner ℂ (f.toLp 2 volume) (R (v.toLp 2 volume)) =
          ∫ x, conj (f x) * firstOrderAction p v x := by
  obtain ⟨_, _, _, _, α, hαSmooth, hαC, _, _, hα⟩ :=
    Burnett.Geometry.FlatRigidity.exists_smooth_cutoff_on_compact_chart hS isOpen_univ (subset_univ S)
  obtain ⟨_, _, _, _, β, hβSmooth, hβC, _, _, hβ⟩ :=
    Burnett.Geometry.FlatRigidity.exists_smooth_cutoff_on_compact_chart hL isOpen_univ (subset_univ L)
  obtain ⟨g, hg, hg₀, hDecay⟩ := coefficient_decay p S hS hs hp hd
  have hB (k ξ : E) : ‖baseFourierCoefficient p k ξ‖ ≤ g k :=
    (le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg ξ))).trans (hDecay k ξ)
  let m := baseFourierCoefficientSymbol p hp.continuous.measurable g hB
  let a : D := ⟨α, hαSmooth, hαC⟩
  let b : D := ⟨β, hβSmooth, hβC⟩
  let ψ := smoothCutoffSymbol a
  let H := symbolCLM (smoothCutoffSymbol b)
  let Q (k : E) := (symbolCLM (oscillatoryCutoff ψ k)).comp ((fourierMultiplier (m k)).comp H)
  have hFM : Continuous (fun k => fourierMultiplier (m k)) := by
    refine continuous_operatorFamily_of_uniform m fourierMultiplier norm_fourierMultiplier_sub_le ?_
    intro k ε hε
    obtain ⟨C, hC, hU⟩ := hd 0
    have hUniform (x ξ : E) : ‖p x ξ‖ ≤ C :=
      (le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg ξ))).trans
        (by simpa only [norm_iteratedFDeriv_zero] using hU x ξ)
    exact baseFourierCoefficient_eventually_uniform p S hS hs hp.continuous C hC hUniform k ε hε
  have hQM : Continuous Q :=
    (continuous_symbolCLM_oscillatoryCutoff ψ (hαC.comp_left Complex.ofReal_zero)).clm_comp
      (hFM.clm_comp continuous_const)
  have hQI : Integrable Q := by
    refine ((hg.mul_const (smoothCutoffSymbol b).bound).const_mul ψ.bound).mono'
      hQM.aestronglyMeasurable (Eventually.of_forall fun k => ?_)
    change ‖Q k‖ ≤ ψ.bound * (g k * (smoothCutoffSymbol b).bound)
    exact norm_bilateral_mode (oscillatoryCutoff ψ k) (smoothCutoffSymbol b) (m k)
  have hPhase (k : E) : symbolCLM (oscillatoryCutoff ψ k) =
      (symbolCLM (baseFourierPhaseSymbol k)).comp (symbolCLM ψ) := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.comp_apply, ← symbolCLM_product]
    apply symbolL2_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [oscillatoryCutoff, productSymbol_apply, baseFourierPhaseSymbol, baseFourierPhase,
        Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  have hCompact (k : E) : IsCompactOperator (Q k) := by
    have hCont : Continuous (m k : E → ℂ) :=
      continuous_baseFourierCoefficient_frequency p S hS hs hp.continuous k
    have hInfinity (ε : ℝ) (hε : 0 < ε) : ∃ L : ℝ, ∀ ξ : E, L < ‖ξ‖ → ‖m k ξ‖ ≤ ε := by
      refine ⟨g k / ε, fun ξ hξ => ?_⟩
      have hCross := (div_lt_iff₀ hε).mp hξ
      have hPos : 0 < 1 + ‖ξ‖ := by positivity
      exact ((le_div_iff₀ hPos).2 (by simpa only [mul_comm] using hDecay k ξ)).trans
        ((div_le_iff₀ hPos).2 (by nlinarith only [hCross, hε]))
    have h := compact_spatial_cutoffs_decaying_multiplier a b (m k) hCont hInfinity
    unfold Q
    rw [hPhase, ContinuousLinearMap.comp_assoc]
    exact h.clm_comp (symbolCLM (baseFourierPhaseSymbol k))
  refine ⟨∫ k, Q k, isCompactOperator_integral Q hQM volume hQI hCompact, ?_⟩
  intro f v hv
  have hV : H (v.toLp 2 volume) = v.toLp 2 volume := by
    apply Lp.ext
    filter_upwards [symbolL2_ae (smoothCutoffSymbol b) (v.toLp 2 volume), v.coeFn_toLp 2 volume]
      with x h₁ h₂
    change symbolL2 (smoothCutoffSymbol b) (v.toLp 2 volume) x = v.toLp 2 volume x
    rw [h₁, h₂]
    by_cases hx : x ∈ L
    · change (β x : ℂ) * v x = v x
      rw [hβ x hx, Complex.ofReal_one, one_mul]
    · have hz : v x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hv h))
      rw [hz, mul_zero]
  have hMode (k : E) : inner ℂ (f.toLp 2 volume) (Q k (v.toLp 2 volume)) =
      inner ℂ ((coeffMul a f).toLp 2 volume)
        (separableOperator (baseFourierPhaseSymbol k) (m k) (v.toLp 2 volume)) := by
    simp only [Q, ContinuousLinearMap.comp_apply, hV, coeffMul_toLp, inner_symbolCLM_left]
    congr 1
    simp only [separableOperator, ContinuousLinearMap.comp_apply, ← symbolCLM_product]
    apply symbolL2_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [oscillatoryCutoff, productSymbol_apply, baseFourierPhaseSymbol, baseFourierPhase,
        Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, ψ, conjugateSymbol_apply,
        smoothCutoffSymbol, physicalCoefficient, Complex.conj_ofReal]
      ring
  let Λ := (innerSL ℂ (f.toLp 2 volume)).comp
    (ContinuousLinearMap.apply ℂ (ComplexL2 E) (v.toLp 2 volume))
  have hSwap := (Λ.integral_comp_comm hQI).symm
  have hSmooth (ξ : E) : ContDiff ℝ ∞ (fun x => p x ξ) := hp.comp (contDiff_id.prodMk (contDiff_const (c := ξ)))
  have hOrder (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ, ‖iteratedFDeriv ℝ n (fun y => p y ξ) x‖ ≤ C := by
    obtain ⟨C, hC, hB⟩ := hd n
    exact ⟨C, hC, fun x ξ => (le_mul_of_one_le_left (norm_nonneg _)
      (le_add_of_nonneg_right (norm_nonneg ξ))).trans (hB x ξ)⟩
  have hInv := baseFourierCoefficient_inverse (compactBaseOrderOne_frequencyWeight
    ⟨S, hS, hs⟩ hSmooth hOrder)
  have hPair := firstOrderAction_pairing_eq_integral_separable_baseFourier p m
    (measurable_baseFourierCoefficient hp.continuous.measurable) g hg (fun _ => le_rfl) hInv v (coeffMul a f)
  calc
    _ = ∫ k, inner ℂ (f.toLp 2 volume) (Q k (v.toLp 2 volume)) := hSwap
    _ = ∫ x, conj (coeffMul a f x) * firstOrderAction p v x :=
      (integral_congr_ae (Eventually.of_forall hMode)).trans hPair.2.symm
    _ = _ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ S
      · change conj ((α x : ℂ) * f x) * _ = _
        rw [hα x hx, Complex.ofReal_one, one_mul]
      · have hZero (ξ : E) : p x ξ = 0 := image_eq_zero_of_notMem_tsupport (f := fun z => p z ξ)
          (fun h => hx (hs ξ h))
        have hAction : firstOrderAction p v x = 0 := by
          simp only [firstOrderAction, Real.fourierIntegralInv_eq', hZero, zero_mul, smul_zero, integral_zero]
        simp only [hAction, mul_zero]

end Burnett.Microlocal.Overlap
