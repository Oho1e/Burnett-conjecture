import Burnett.Analysis.PrincipalEnergy.Localization.OrderOneCutoffOverlap
import Burnett.Analysis.PrincipalEnergy.Commutator.HighOffSupportAction
import Burnett.Analysis.PrincipalEnergy.Localization.CoefficientTailKernel

set_option autoImplicit false
set_option maxHeartbeats 6800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Set Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate InnerProductSpace

private def absComplex (f : SchwartzMap Space ℂ) (x : Space) : ℂ := ‖f x‖

private theorem absComplex_memLp (f : SchwartzMap Space ℂ) : MemLp (absComplex f) 2 volume := by
  have hC : Continuous (absComplex f) := Complex.continuous_ofReal.comp f.continuous.norm
  apply (f.memLp 2 volume).mono hC.aestronglyMeasurable
  exact .of_forall fun x => by rw [absComplex, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]

private theorem absComplex_L2_norm (f : SchwartzMap Space ℂ) :
    ‖(absComplex_memLp f).toLp (absComplex f)‖ = ‖f.toLp 2 volume‖ := by
  change ‖(absComplex_memLp f).toLp (absComplex f)‖ = ‖(f.memLp 2 volume).toLp (f : Space → ℂ)‖
  rw [Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  apply eLpNorm_congr_norm_ae
  exact .of_forall fun x => by rw [absComplex, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]

private theorem weighted_tail_abs_bound (f g : SchwartzMap Space ℂ) :
    ∃ G : Space → ℂ, ∃ hG : MemLp G 2 volume,
      (∀ x, G x = (∫ y, inverseFifthTail 1 (x-y) * ‖f y‖ : ℝ)) ∧
      Integrable (fun x => ‖g x‖*‖G x‖) ∧
      (∫ x, ‖g x‖*‖G x‖) ≤
        (∫ z : Space, inverseFifthTail 1 z) * ‖f.toLp 2 volume‖ * ‖g.toLp 2 volume‖ := by
  let D := inverseFifthTail 1
  let K (x y : Space) : ℂ := D (x-y)
  have hD : Measurable D :=
    Measurable.ite (measurableSet_le measurable_const measurable_norm) (by fun_prop) measurable_const
  have hK : Measurable (uncurry K) := Complex.continuous_ofReal.measurable.comp
    (hD.comp (measurable_fst.sub measurable_snd))
  have hAbs : Continuous (absComplex f) := Complex.continuous_ofReal.comp f.continuous.norm
  have hAbs₁ : Integrable (absComplex f) := Complex.ofRealCLM.integrable_comp f.integrable.norm
  let G (x : Space) := ∫ y, K x y * absComplex f y
  obtain ⟨hG, hGbound⟩ := convolution_envelope_action_norm_le K hK D hD (inverseFifthTail_nonneg 1)
    (inverseFifthTail_integrable zero_lt_one) (fun x y => by
      change ‖(D (x-y) : ℂ)‖ ≤ D (x-y)
      rw [Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ D (x-y) from inverseFifthTail_nonneg 1 _)])
    (absComplex f) hAbs.measurable hAbs₁ (absComplex_memLp f)
  have hRe (x : Space) : G x = (∫ y, D (x-y) * ‖f y‖ : ℝ) := by
    simp only [G, K, absComplex, ← Complex.ofReal_mul, integral_complex_ofReal]
  have hN (x : Space) : ‖G x‖ = ∫ y, D (x-y)*‖f y‖ := by
    rw [hRe, Complex.norm_real, Real.norm_of_nonneg]
    exact integral_nonneg fun y => mul_nonneg (inverseFifthTail_nonneg 1 _) (norm_nonneg _)
  have hI : Integrable (fun x => ‖g x‖*‖G x‖) :=
    (g.memLp 2 volume).norm.integrable_mul hG.norm
  refine ⟨G, hG, hRe, hI, ?_⟩
  let A := (absComplex_memLp g).toLp (absComplex g)
  let B := hG.toLp G
  have hInner : ⟪A,B⟫_ℂ = (∫ x, ‖g x‖*‖G x‖ : ℝ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (absComplex_memLp g), MemLp.coeFn_toLp hG] with x hg hx
    change inner ℂ (A x) (B x) = ((‖g x‖*‖G x‖ : ℝ) : ℂ)
    rw [hg, hx, RCLike.inner_apply']
    have hRealG : G x = (‖G x‖ : ℂ) := (hRe x).trans (congrArg Complex.ofReal (hN x).symm)
    change conj (absComplex g x) * G x = ((‖g x‖*‖G x‖ : ℝ) : ℂ)
    calc
      _ = conj (absComplex g x) * (‖G x‖ : ℂ) := congrArg (fun z => conj (absComplex g x) * z) hRealG
      _ = _ := by rw [absComplex, Complex.conj_ofReal, Complex.ofReal_mul]
  calc
    _ = ‖⟪A,B⟫_ℂ‖ := by
      rw [hInner, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => by positivity)]
    _ ≤ ‖A‖*‖B‖ := norm_inner_le_norm _ _
    _ ≤ ‖A‖*((∫ z : Space, D z)*‖f.toLp 2 volume‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [absComplex_L2_norm] using hGbound
    _ = _ := by
      rw [show ‖A‖ = ‖g.toLp 2 volume‖ from absComplex_L2_norm g]
      ring

/-- The left cut covers the test. The right part missing its plateau is
separated from that test and its entire sum uses one inverse-fifth tail. -/
theorem exists_firstOrderAction_latticeFar_pair_bound {a : Space → Space → ℂ} (ha : FrequencyOrderOne a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Fintype ι]
      (α χ : ι → SchwartzMap Space ℂ) (f g : SchwartzMap Space ℂ),
      (∀ i x, ‖χ i x - 1‖ ≤ 1) →
      (∀ x, ∑ i, ‖α i x‖ ≤ 1) →
      (∀ i x y, α i x ≠ 0 → χ i y ≠ 1 → 1 ≤ ‖x-y‖) →
      ‖∑ i, ∫ x, conj (scalarSchwartzProduct (α i) g x) *
          firstOrderAction a (f-scalarSchwartzProduct (χ i) f : SchwartzMap Space ℂ) x‖ ≤
        C * ‖f.toLp 2 volume‖ * ‖g.toLp 2 volume‖ := by
  obtain ⟨A, _, hA, _, hLo, _⟩ := exists_firstOrderLowKernel_relative_bounds ha
  obtain ⟨p, B, hB, hp, hHi⟩ := exists_normalizedInverseProfiles ha
  let N := A+34*B
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  let D := inverseFifthTail 1
  refine ⟨N*(∫ z : Space, D z), mul_nonneg hN (integral_nonneg (inverseFifthTail_nonneg 1)), ?_⟩
  intro ι _ α χ f g hChi hSub hGap
  obtain ⟨G, hG, hGRe, hI, hGbound⟩ := weighted_tail_abs_bound f g
  have hGval (x : Space) : ‖G x‖ = ∫ y, D (x-y)*‖f y‖ := by
    rw [hGRe, Complex.norm_real, Real.norm_of_nonneg]
    exact integral_nonneg fun y => mul_nonneg (inverseFifthTail_nonneg 1 _) (norm_nonneg _)
  have tailMeas : Measurable D :=
    Measurable.ite (measurableSet_le measurable_const measurable_norm) (by fun_prop) measurable_const
  have hID (x : Space) : Integrable (fun y => D (x-y)*‖f y‖) := by
    apply (f.integrable.norm).mono'
      ((tailMeas.comp (measurable_const.sub measurable_id)).mul f.continuous.norm.measurable).aestronglyMeasurable
    filter_upwards with y
    have hn : 0 ≤ D (x-y)*‖f y‖ := mul_nonneg (inverseFifthTail_nonneg 1 _) (norm_nonneg _)
    change ‖D (x-y)*‖f y‖‖ ≤ ‖f y‖
    rw [Real.norm_of_nonneg hn]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    change inverseFifthTail 1 (x-y) ≤ 1
    unfold inverseFifthTail
    split_ifs with h
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ h)
    · exact zero_le_one
  let F (i : ι) := f-scalarSchwartzProduct (χ i) f
  let T (i : ι) (x : Space) := conj (scalarSchwartzProduct (α i) g x) * firstOrderAction a (F i) x
  have hFvalue (i : ι) (y : Space) : ‖F i y‖ ≤ ‖f y‖ := by
    have hEq : F i y = (1-χ i y)*f y := by
      simp only [F, SchwartzMap.sub_apply, scalarSchwartzProduct_apply]
      ring
    rw [hEq, norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    simpa only [norm_sub_rev (1:ℂ) (χ i y)] using hChi i y
  have hFnz (i : ι) (y : Space) (hy : F i y ≠ 0) : χ i y ≠ 1 := by
    intro h
    exact hy (by simp only [F, SchwartzMap.sub_apply, scalarSchwartzProduct_apply, h, one_mul, sub_self])
  have hAction (i : ι) (x : Space) (hx : α i x ≠ 0) : ‖firstOrderAction a (F i) x‖ ≤ N * ‖G x‖ := by
    have hOff : x ∉ tsupport (F i : Space → ℂ) := by
      have hClosed : IsClosed {y : Space | 1 ≤ ‖x-y‖} :=
        isClosed_le continuous_const (continuous_const.sub continuous_id).norm
      have hSupp : tsupport (F i : Space → ℂ) ⊆ {y : Space | 1 ≤ ‖x-y‖} :=
        closure_minimal (fun y hy => hGap i x y hx (hFnz i y hy)) hClosed
      intro hh
      have hf := hSupp hh
      simp only [mem_setOf_eq, sub_self, norm_zero] at hf
      exact (not_le_of_gt zero_lt_one) hf
    have hDom (K : Space → ℂ) (C : ℝ) (hC : 0 ≤ C)
        (hK : ∀ y, y ≠ x → ‖K y‖ ≤ C*(‖x-y‖^5)⁻¹) :
        ‖∫ y, K y * F i y‖ ≤ C * ‖G x‖ := by
      rw [hGval, ← integral_const_mul]
      apply norm_integral_le_of_norm_le ((hID x).const_mul _)
      filter_upwards with y
      by_cases hy : F i y = 0
      · rw [hy, mul_zero, norm_zero]
        exact mul_nonneg hC (mul_nonneg (inverseFifthTail_nonneg 1 _) (norm_nonneg _))
      have hGap' := hGap i x y hx (hFnz i y hy)
      have hyx : y ≠ x := fun h => (not_le_of_gt zero_lt_one) (by simpa only [h, sub_self, norm_zero] using hGap')
      unfold D inverseFifthTail
      rw [if_pos hGap', norm_mul, ← mul_assoc]
      exact mul_le_mul (hK y hyx) (hFvalue i y) (norm_nonneg _) (by positivity)
    rw [firstOrderAction_eq_low_add_high ha, firstOrderLowAction_eq_kernel ha _ (F i).integrable,
      (firstOrderHighAction_offSupport ha (F i) x hOff).2]
    refine (norm_add_le _ _).trans ((add_le_add (hDom _ A hA fun y hy => hLo x (x-y) (sub_ne_zero.mpr hy.symm))
      (hDom _ (34*B) (by positivity) fun y hy => ?_)).trans_eq (by dsimp only [N]; ring))
    exact ((firstOrderKernel_size a p hp B hB hHi x (x-y) (sub_ne_zero.mpr hy.symm)).2 0).2
  have hNorm (i : ι) (x : Space) : ‖T i x‖ ≤ ‖α i x‖*(N*(‖g x‖*‖G x‖)) := by
    by_cases hx : α i x = 0
    · simp only [T, scalarSchwartzProduct_apply, hx, zero_mul, map_zero, norm_zero, le_refl]
    have hh := hAction i x hx
    simp only [T, scalarSchwartzProduct_apply, norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)
  have hMajor (i : ι) : Integrable (fun x => ‖α i x‖*(N*(‖g x‖*‖G x‖))) := by
    refine (hI.const_mul N).mono'
      ((α i).continuous.norm.aestronglyMeasurable.mul (hI.const_mul N).aestronglyMeasurable) (.of_forall fun x => ?_)
    have hα : ‖α i x‖ ≤ 1 :=
      (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => norm_nonneg (α j x))
        (Finset.mem_univ i)).trans (hSub x)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (by positivity) hα
  change ‖∑ i, ∫ x, T i x‖ ≤ _
  calc
    _ ≤ ∑ i, ‖∫ x, T i x‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∫ x, ‖α i x‖*(N*(‖g x‖*‖G x‖)) := Finset.sum_le_sum fun i _ =>
      norm_integral_le_of_norm_le (hMajor i) (.of_forall (hNorm i))
    _ = ∫ x, ∑ i, ‖α i x‖*(N*(‖g x‖*‖G x‖)) := (integral_finset_sum _ (fun i _ => hMajor i)).symm
    _ ≤ ∫ x, N*(‖g x‖*‖G x‖) := by
      apply integral_mono (integrable_finset_sum _ (fun i _ => hMajor i)) (hI.const_mul N)
      intro x
      change (∑ i, ‖α i x‖*(N*(‖g x‖*‖G x‖))) ≤ N*(‖g x‖*‖G x‖)
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left (by positivity) (hSub x)
    _ ≤ _ := by
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left hGbound hN).trans_eq (by dsimp only [D]; ring)

end Burnett.Analysis.CarlesonEmbedding
