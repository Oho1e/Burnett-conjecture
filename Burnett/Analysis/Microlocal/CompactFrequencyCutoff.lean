import Burnett.Analysis.Fourier.Projection
import Burnett.Analysis.Sobolev.TestJet
import Mathlib.Analysis.Normed.Operator.Compact

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section

namespace Burnett.Microlocal.CompactFrequencyCutoff

open Set Filter MeasureTheory Function Burnett.Fourier
open Burnett.X02.SobolevTestJet (Space D test_smooth test_compactSupport)
open scoped ContDiff Topology FourierTransform ComplexConjugate

private abbrev E := Space
abbrev Operator := ComplexL2 Space →L[ℂ] ComplexL2 Space

private def wave (k y : E) : ℂ := Real.fourierChar (inner ℝ k y)

private theorem wave_continuous : Continuous (uncurry wave) :=
  continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_fst.inner continuous_snd))

private theorem smoothCutoffSymbol_bound (a : D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Space, ‖((a : Space → ℝ) x : ℂ)‖ ≤ B := by
  obtain ⟨B, hB, h⟩ := ((test_compactSupport a).image (test_smooth a).continuous).isBounded.exists_pos_norm_le
  refine ⟨B, hB.le, fun x => ?_⟩
  rw [Complex.norm_real]
  by_cases hx : x ∈ tsupport (a : Space → ℝ)
  · exact h _ ⟨x, hx, rfl⟩
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact hB.le

def smoothCutoffSymbol (a : D) : BoundedSymbol Space where
  toFun x := ((a : Space → ℝ) x : ℂ)
  measurable := (Complex.continuous_ofReal.comp (test_smooth a).continuous).aestronglyMeasurable
  bound := (smoothCutoffSymbol_bound a).choose
  bound_nonneg := (smoothCutoffSymbol_bound a).choose_spec.1
  norm_le := (smoothCutoffSymbol_bound a).choose_spec.2

private def oscillatoryCutoff (ψ : BoundedSymbol E) (k : E) : BoundedSymbol E where
  toFun x := Real.fourierChar (inner ℝ k x) • ψ x
  measurable := (Real.continuous_fourierChar.comp
    (continuous_const.inner continuous_id)).aestronglyMeasurable.smul ψ.measurable
  bound := ψ.bound
  bound_nonneg := ψ.bound_nonneg
  norm_le x := by simpa only [Circle.norm_smul] using ψ.norm_le x

private def boundedDifference (a b : BoundedSymbol E) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ ξ, ‖a ξ - b ξ‖ ≤ C) : BoundedSymbol E where
  toFun := fun ξ => a ξ - b ξ
  measurable := a.measurable.sub b.measurable
  bound := C
  bound_nonneg := hC
  norm_le := h

private theorem symbolCLM_boundedDifference (a b : BoundedSymbol E) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ ξ, ‖a ξ - b ξ‖ ≤ C) :
    symbolCLM (boundedDifference a b C hC h) = symbolCLM a - symbolCLM b := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [symbolL2_ae (boundedDifference a b C hC h) u, symbolL2_ae a u, symbolL2_ae b u,
    Lp.coeFn_sub (symbolL2 a u) (symbolL2 b u)] with x hd ha hb hsub
  change symbolL2 (boundedDifference a b C hC h) u x = (symbolL2 a u - symbolL2 b u) x
  rw [hd, hsub, Pi.sub_apply, ha, hb]
  exact sub_mul (a x) (b x) (u x)

private theorem norm_symbolCLM_sub_le (a b : BoundedSymbol E) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ ξ, ‖a ξ - b ξ‖ ≤ C) : ‖symbolCLM a - symbolCLM b‖ ≤ C := by
  rw [← symbolCLM_boundedDifference a b C hC h]
  exact ContinuousLinearMap.opNorm_le_bound _ hC (symbolL2_norm_le (boundedDifference a b C hC h))

private theorem norm_fourierMultiplier_sub_le (a b : BoundedSymbol E) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ ξ, ‖a ξ - b ξ‖ ≤ C) : ‖fourierMultiplier a - fourierMultiplier b‖ ≤ C := by
  let d := boundedDifference a b C hC h
  have he : fourierMultiplier d = fourierMultiplier a - fourierMultiplier b := by
    apply ContinuousLinearMap.ext
    intro u
    have hs := congrArg (fun A : ComplexL2 E →L[ℂ] ComplexL2 E => A (fourierL2Equiv u))
      (symbolCLM_boundedDifference a b C hC h)
    change symbolL2 d (fourierL2Equiv u) =
      symbolL2 a (fourierL2Equiv u) - symbolL2 b (fourierL2Equiv u) at hs
    rw [ContinuousLinearMap.sub_apply, fourierMultiplier_apply, fourierMultiplier_apply,
      fourierMultiplier_apply, hs, map_sub]
  rw [← he]
  exact ContinuousLinearMap.opNorm_le_bound _ hC (fourierMultiplier_norm_le d)

private theorem continuous_operatorFamily_of_uniform (p : E → BoundedSymbol E)
    (T : BoundedSymbol E → (ComplexL2 E →L[ℂ] ComplexL2 E))
    (hT : ∀ a b C, 0 ≤ C → (∀ ξ, ‖a ξ - b ξ‖ ≤ C) → ‖T a - T b‖ ≤ C)
    (hp : ∀ (k : E) (ε : ℝ), 0 < ε → ∀ᶠ l in 𝓝 k, ∀ ξ, ‖p l ξ - p k ξ‖ ≤ ε) :
    Continuous (fun k => T (p k)) := by
  apply continuous_iff_continuousAt.mpr
  intro k
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hp k (ε/2) (half_pos hε)] with l hl
  rw [dist_eq_norm]
  exact (hT (p l) (p k) (ε/2) (half_pos hε).le hl).trans_lt (half_lt_self hε)

private theorem continuous_symbolCLM_oscillatoryCutoff (ψ : BoundedSymbol E)
    (hψ : HasCompactSupport (ψ : E → ℂ)) :
    Continuous (fun k => symbolCLM (oscillatoryCutoff ψ k)) := by
  apply continuous_operatorFamily_of_uniform (fun k => oscillatoryCutoff ψ k) symbolCLM
    norm_symbolCLM_sub_le
  intro k ε hε
  let K := tsupport (ψ : E → ℂ)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hψ
  let F (q : E) (x : K) : ℂ := Real.fourierChar (inner ℝ q (x : E))
  have hF : Continuous (uncurry F) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_fst.inner (continuous_subtype_val.comp continuous_snd)))
  let d := ε / (ψ.bound + 1)
  have hd : 0 < d := div_pos hε (by linarith [ψ.bound_nonneg])
  have hUni := (Metric.tendstoUniformly_iff.mp (hF.tendstoUniformly F k)) d hd
  filter_upwards [hUni] with l hl x
  by_cases hx : ψ x = 0
  · simp [oscillatoryCutoff, hx, hε.le]
  · have hxK : x ∈ K := subset_tsupport (ψ : E → ℂ) hx
    have hPhase : ‖F l ⟨x,hxK⟩ - F k ⟨x,hxK⟩‖ < d := by
      simpa only [dist_eq_norm, norm_sub_rev (F k ⟨x,hxK⟩) (F l ⟨x,hxK⟩)] using hl ⟨x,hxK⟩
    have hEq : oscillatoryCutoff ψ l x - oscillatoryCutoff ψ k x =
        (F l ⟨x,hxK⟩ - F k ⟨x,hxK⟩) * ψ x := by
      simp only [oscillatoryCutoff, Circle.smul_def, smul_eq_mul, F, sub_mul]
    rw [hEq, norm_mul]
    calc
      _ ≤ d * ψ.bound := mul_le_mul hPhase.le (ψ.norm_le x) (norm_nonneg _) hd.le
      _ ≤ d * (ψ.bound + 1) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hd.le
      _ = ε := div_mul_cancel₀ _ (by linarith [ψ.bound_nonneg])

def frequencyTruncation (p : BoundedSymbol E) (R : ℝ) : BoundedSymbol E where
  toFun := (Metric.closedBall (0:E) R).indicator p
  measurable := p.measurable.indicator Metric.isClosed_closedBall.measurableSet
  bound := p.bound
  bound_nonneg := p.bound_nonneg
  norm_le ξ := by
    by_cases h : ξ ∈ Metric.closedBall (0:E) R
    · simpa only [indicator_of_mem h] using p.norm_le ξ
    · simpa only [indicator_of_notMem h,norm_zero] using p.bound_nonneg

private theorem inner_smoothCutoffSymbol_left_eq_right (β : D) (u v : ComplexL2 E) :
    inner ℂ (symbolCLM (smoothCutoffSymbol β) u) v =
      inner ℂ u (symbolCLM (smoothCutoffSymbol β) v) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [symbolL2_ae (smoothCutoffSymbol β) u,symbolL2_ae (smoothCutoffSymbol β) v] with x hx hy
  change inner ℂ (symbolL2 (smoothCutoffSymbol β) u x) (v x) =
    inner ℂ (u x) (symbolL2 (smoothCutoffSymbol β) v x)
  rw [RCLike.inner_apply',RCLike.inner_apply',hx,hy,map_mul]
  change conj ((β : E → ℝ) x : ℂ) * conj (u x) * v x =
    conj (u x) * (((β : E → ℝ) x : ℂ) * v x)
  rw [Complex.conj_ofReal]
  ring

/-- The operator-norm integral of a continuous integrable family of compact
operators belongs to the closed space of compact operators. -/
theorem isCompactOperator_integral (A : E → Operator) (hAc : Continuous A)
    (μ : Measure E) (hA : Integrable A μ) (hK : ∀ k, IsCompactOperator (A k)) :
    IsCompactOperator (∫ k, A k ∂μ : Operator) := by
  let K := compactOperator (RingHom.id ℂ) (ComplexL2 E) (ComplexL2 E)
  have hclosed : IsClosed (K : Set Operator) := isClosed_setOf_isCompactOperator
  letI : CompleteSpace K := hclosed.completeSpace_coe
  let a (k : E) : K := ⟨A k,hK k⟩
  have hac : Continuous a := hAc.subtype_mk _
  letI : SecondCountableTopologyEither E K := secondCountableTopologyEither_of_left _ _
  have ha : Integrable a μ := hA.norm.mono' hac.aestronglyMeasurable (Eventually.of_forall fun _ => le_rfl)
  have he : K.subtypeL (∫ k, a k ∂μ) = ∫ k, A k ∂μ :=
    (K.subtypeL.integral_comp_comm ha).symm
  change (∫ k, A k ∂μ) ∈ K
  rw [← he]
  exact (∫ k, a k ∂μ).property

private def waveWindow (b : BoundedSymbol E) (hbc : HasCompactSupport (b : E → ℂ)) : ComplexL2 E :=
  indicatorConstLp 2 hbc.measurableSet (hbc.measure_ne_top (μ := volume)) (1 : ℂ)

private def windowWave (b : BoundedSymbol E) (hbc : HasCompactSupport (b : E → ℂ)) (ξ : E) :
    ComplexL2 E := symbolCLM (oscillatoryCutoff b ξ) (waveWindow b hbc)

private theorem windowWave_continuous (b : BoundedSymbol E) (hbc : HasCompactSupport (b : E → ℂ)) :
    Continuous (windowWave b hbc) :=
  (continuous_symbolCLM_oscillatoryCutoff b hbc).clm_apply continuous_const

private theorem windowWave_ae (b : BoundedSymbol E) (hbc : HasCompactSupport (b : E → ℂ)) (ξ : E) :
    (windowWave b hbc ξ : E → ℂ) =ᵐ[volume] fun x => wave ξ x * b x := by
  let w := waveWindow b hbc
  filter_upwards [symbolL2_ae (oscillatoryCutoff b ξ) w,
    indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure E)) (hs := hbc.measurableSet)
      (hμs := hbc.measure_ne_top (μ := volume)) (c := (1 : ℂ))] with x h hInd
  rw [show windowWave b hbc ξ x = _ from h]
  rw [show w x = _ from hInd]
  by_cases hx : x ∈ tsupport (b : E → ℂ)
  · simp only [indicator_of_mem hx, mul_one, oscillatoryCutoff, Circle.smul_def, smul_eq_mul, wave]
  · have he : b x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [indicator_of_notMem hx,mul_zero,he,mul_zero]

private theorem real_coefficient_compact (a : D) :
    HasCompactSupport (smoothCutoffSymbol a : E → ℂ) :=
  (test_compactSupport a).comp_left Complex.ofReal_zero

private def cutoffSchwartz (a : D) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  let hc : HasCompactSupport (fun x => smoothCutoffSymbol a x * f x) := (real_coefficient_compact a).mul_right
  hc.toSchwartzMap ((Complex.ofRealCLM.contDiff.comp (test_smooth a)).mul f.smooth')

private theorem cutoffSchwartz_toLp (a : D) (f : SchwartzMap E ℂ) :
    (cutoffSchwartz a f).toLp 2 volume = symbolCLM (smoothCutoffSymbol a) (f.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(cutoffSchwartz a f).coeFn_toLp 2 volume, f.coeFn_toLp 2 volume,
    symbolL2_ae (smoothCutoffSymbol a) (f.toLp 2 volume)] with x h₁ h₂ h₃
  change (cutoffSchwartz a f).toLp 2 volume x = symbolL2 (smoothCutoffSymbol a) (f.toLp 2 volume) x
  rw [h₁,h₃,h₂]
  rfl

private theorem inner_windowWave (a : D) (f : SchwartzMap E ℂ) (ξ : E) :
    inner ℂ (windowWave (smoothCutoffSymbol a) (real_coefficient_compact a) ξ) (f.toLp 2 volume) =
      (𝓕 (cutoffSchwartz a f : E → ℂ)) ξ := by
  rw [L2.inner_def,Real.fourierIntegral_eq]
  apply integral_congr_ae
  filter_upwards [windowWave_ae (smoothCutoffSymbol a) (real_coefficient_compact a) ξ,
    f.coeFn_toLp 2 volume] with x hx hf
  rw [RCLike.inner_apply',hx,hf]
  change conj (wave ξ x * ((a : E → ℝ) x : ℂ)) * f x =
    Real.fourierChar (-inner ℝ x ξ) • (((a : E → ℝ) x : ℂ) * f x)
  rw [real_inner_comm ξ x,map_mul,Complex.conj_ofReal,AddChar.map_neg_eq_inv,Circle.smul_def,
    Circle.coe_inv_eq_conj]
  simp only [smul_eq_mul,wave,mul_assoc]

private theorem isCompactOperator_rankOne (v w : ComplexL2 E) :
    IsCompactOperator ((innerSL ℂ w).smulRight v) := by
  have hc : IsCompactOperator (id : ℂ → ℂ) :=
    ⟨Metric.closedBall 0 1,isCompact_closedBall _ _,Metric.closedBall_mem_nhds _ zero_lt_one⟩
  exact (hc.comp_clm (innerSL ℂ w)).clm_comp ((ContinuousLinearMap.id ℂ ℂ).smulRight v)

/-- The doubly localized low-frequency multiplier is compact. Its integral
over the frequency ball consists of the actual rank-one phase operators. -/
theorem compact_spatial_cutoffs_truncated_multiplier (a b : D) (p : BoundedSymbol E)
    (hp : Continuous (p : E → ℂ)) (R : ℝ) :
    IsCompactOperator ((symbolCLM (smoothCutoffSymbol a)).comp
      ((fourierMultiplier (frequencyTruncation p R)).comp (symbolCLM (smoothCutoffSymbol b)))) := by
  let va := windowWave (smoothCutoffSymbol a) (real_coefficient_compact a)
  let vb := windowWave (smoothCutoffSymbol b) (real_coefficient_compact b)
  let A (ξ : E) : Operator := p ξ • (innerSL ℂ (vb ξ)).smulRight (va ξ)
  have hac : Continuous va := windowWave_continuous _ _
  have hbc : Continuous vb := windowWave_continuous _ _
  have hinner : Continuous (fun ξ => innerSL ℂ (vb ξ)) := (innerSL ℂ).continuous.comp hbc
  have hRank : Continuous (fun ξ => (innerSL ℂ (vb ξ)).smulRight (va ξ)) :=
    ((ContinuousLinearMap.smulRightL ℂ (ComplexL2 E) (ComplexL2 E)).continuous.comp hinner).clm_apply hac
  have hAc : Continuous A := hp.smul hRank
  let Q := Metric.closedBall (0 : E) R
  let μ := (volume : Measure E).restrict Q
  letI : SecondCountableTopologyEither E Operator := secondCountableTopologyEither_of_left _ _
  have hAi : Integrable A μ := hAc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hC (ξ : E) : IsCompactOperator (A ξ) := (isCompactOperator_rankOne (va ξ) (vb ξ)).smul (p ξ)
  let T := ∫ ξ, A ξ ∂μ
  have hT : IsCompactOperator T := isCompactOperator_integral A hAc μ hAi hC
  let S := (symbolCLM (smoothCutoffSymbol a)).comp
      ((fourierMultiplier (frequencyTruncation p R)).comp (symbolCLM (smoothCutoffSymbol b)))
  have hEq : S = T := by
    apply ContinuousLinearMap.ext
    intro g
    apply ext_inner_left ℂ
    intro f
    apply (schwartz_toLp_denseRange (V := E)).induction_on₂
      (p := fun u v => inner ℂ u (S v) = inner ℂ u (T v)) _ _ f g
    · exact isClosed_eq (continuous_fst.inner (S.continuous.comp continuous_snd))
        (continuous_fst.inner (T.continuous.comp continuous_snd))
    · intro f g
      let u := f.toLp 2 volume
      let v := g.toLp 2 volume
      have hL : inner ℂ u (S v) = inner ℂ (symbolCLM (smoothCutoffSymbol a) u)
          (fourierMultiplier (frequencyTruncation p R) (symbolCLM (smoothCutoffSymbol b) v)) := by
        exact (inner_smoothCutoffSymbol_left_eq_right a _ _).symm
      have hPair :
          inner ℂ u (S v) = ∫ ξ in Q,
            conj ((𝓕 (cutoffSchwartz a f : E → ℂ)) ξ) * (p ξ * (𝓕 (cutoffSchwartz b g : E → ℂ)) ξ) := by
        rw [hL, ← cutoffSchwartz_toLp a f, ← cutoffSchwartz_toLp b g,
          ← fourierL2Equiv.inner_map_map, fourier_fourierMultiplier, L2.inner_def]
        have hQ : MeasurableSet Q := Metric.isClosed_closedBall.measurableSet
        rw [← integral_indicator hQ]
        let F := fourierL2Equiv ((cutoffSchwartz b g).toLp 2 volume)
        apply integral_congr_ae
        filter_upwards [fourierL2Equiv_schwartz_ae (cutoffSchwartz a f),
          fourierL2Equiv_schwartz_ae (cutoffSchwartz b g),symbolL2_ae (frequencyTruncation p R) F]
          with ξ h₁ h₂ h₃
        rw [RCLike.inner_apply',h₁,h₃,show F ξ = _ from h₂]
        change conj ((𝓕 (cutoffSchwartz a f : E → ℂ)) ξ) * ((Q.indicator p) ξ * _) =
          (Q.indicator _) ξ
        by_cases hξ : ξ ∈ Q
        · simp only [indicator_of_mem hξ]
        · simp only [indicator_of_notMem hξ,zero_mul,mul_zero]
      change inner ℂ u (S v) = inner ℂ u (T v)
      rw [hPair, show inner ℂ u (T v) = ∫ ξ, inner ℂ u (A ξ v) ∂μ from by
        exact (((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ (ComplexL2 E) v)).integral_comp_comm hAi).symm]
      apply integral_congr_ae
      filter_upwards with ξ
      have hA' := inner_windowWave a f ξ
      have hB' := inner_windowWave b g ξ
      change inner ℂ (va ξ) u = _ at hA'
      change inner ℂ (vb ξ) v = _ at hB'
      simp only [A,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply,
        inner_smul_right,hB',← hA']
      rw [inner_conj_symm]
      ring
  have hS : IsCompactOperator S := hEq.symm ▸ hT
  exact hS

/-- A multiplier whose symbol decays at infinity is compact between any
two compact spatial cutoffs. -/
theorem compact_spatial_cutoffs_decaying_multiplier (a b : D) (p : BoundedSymbol E)
    (hp : Continuous (p : E → ℂ))
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ ξ : E, R < ‖ξ‖ → ‖p ξ‖ ≤ ε) :
    IsCompactOperator ((symbolCLM (smoothCutoffSymbol a)).comp
      ((fourierMultiplier p).comp (symbolCLM (smoothCutoffSymbol b)))) := by
  let L := symbolCLM (smoothCutoffSymbol a)
  let M := symbolCLM (smoothCutoffSymbol b)
  let S (R : ℝ) := L.comp ((fourierMultiplier (frequencyTruncation p R)).comp M)
  have hc : ∀ᶠ R in atTop, IsCompactOperator (S R) :=
    Eventually.of_forall (compact_spatial_cutoffs_truncated_multiplier a b p hp)
  refine isCompactOperator_of_tendsto ?_ hc
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (2 * (‖L‖+1) * (‖M‖+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨R,hR⟩ := hdec δ hδ
  filter_upwards [eventually_ge_atTop R] with r hr
  have hpt (ξ : E) : ‖frequencyTruncation p r ξ-p ξ‖ ≤ δ := by
    by_cases hξ : ξ ∈ Metric.closedBall (0 : E) r
    · simp [frequencyTruncation, indicator_of_mem hξ, hδ.le]
    · have hn : r < ‖ξ‖ := lt_of_not_ge (by simpa only [Metric.mem_closedBall,dist_zero_right] using hξ)
      simpa only [frequencyTruncation,indicator_of_notMem hξ,zero_sub,norm_neg] using hR ξ (hr.trans_lt hn)
  have H := norm_fourierMultiplier_sub_le (frequencyTruncation p r) p δ hδ.le hpt
  have he : S r - L.comp ((fourierMultiplier p).comp M) =
      L.comp ((fourierMultiplier (frequencyTruncation p r)-fourierMultiplier p).comp M) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [S,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,map_sub]
  change dist (S r) (L.comp ((fourierMultiplier p).comp M)) < ε
  rw [dist_eq_norm,he]
  calc
    _ ≤ ‖L‖ * (δ * ‖M‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right H (norm_nonneg _)))
        (norm_nonneg _))
    _ ≤ (‖L‖+1) * (δ * (‖M‖+1)) := by gcongr <;> linarith [norm_nonneg L, norm_nonneg M]
    _ = ε/2 := by
      dsimp [δ]
      field_simp
    _ < ε := half_lt_self hε

end Burnett.Microlocal.CompactFrequencyCutoff
