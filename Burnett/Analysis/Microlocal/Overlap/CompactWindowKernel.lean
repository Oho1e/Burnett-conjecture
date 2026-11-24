import Burnett.Analysis.Microlocal.Overlap.DyadicSchur
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Compact

/-! A continuous kernel on a compact rectangle gives a compact L² operator
with the same operator norm bound as the convolution envelope estimate. -/

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel (E)
open scoped ComplexConjugate InnerProduct Topology ENNReal

/-- Realizes a kernel on a compact window as one compact operator on the entire
ambient L² space. The Schur constant is kept independently of the pointwise
bound used for compactness. -/
theorem exists_compact_windowKernel_schur
    (K : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hK : Measurable (uncurry K)) (hCont : ContinuousOn (uncurry K) (S ×ˢ S))
    (hSupp : ∀ x y, x ∉ S ∨ y ∉ S → K x y = 0)
    (C q s : ℝ) (hC : 0 ≤ C) (hq : 0 < q) (hs : 0 < s)
    (hBound : ∀ x y, ‖K x y‖ ≤ C * s ^ 3 / (1 + s * q * ‖x - y‖) ^ 5) :
    ∃ R : ComplexL2 E →L[ℂ] ComplexL2 E, IsCompactOperator R ∧
      ‖R‖ ≤ (C / q ^ 4 * ∫ z, fifthProfile z) / s ∧
      ∀ u : ComplexL2 E, R u =ᵐ[volume] fun x => ∫ y, K x y * u y := by
  let I : ComplexL2 E := indicatorConstLp 2 hS.isClosed.measurableSet hS.measure_lt_top.ne 1
  let hSm := hS.isClosed.measurableSet
  have hI : I =ᵐ[volume] S.indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn
  let m := (C / q ^ 4 * ∫ z, fifthProfile z) / s
  have hm : 0 ≤ m := div_nonneg (mul_nonneg (div_nonneg hC (pow_nonneg hq.le _))
    (integral_nonneg fifthProfile_nonneg)) hs.le
  let U (u : ComplexL2 E) := S.indicator ((Lp.aestronglyMeasurable u).mk u)
  have hUm (u : ComplexL2 E) : Measurable (U u) :=
    (Lp.aestronglyMeasurable u).stronglyMeasurable_mk.measurable.indicator hSm
  have hUeq (u : ComplexL2 E) : U u =ᵐ[volume] S.indicator (u : E → ℂ) := by
    filter_upwards [(Lp.aestronglyMeasurable u).ae_eq_mk] with x hx
    by_cases h : x ∈ S
    · simp only [U, indicator_of_mem h, hx]
    · simp only [U, indicator_of_notMem h]
  have hU₂ (u : ComplexL2 E) : MemLp (U u) 2 volume :=
    (memLp_congr_ae (hUeq u)).2 ((Lp.memLp u).indicator hSm)
  have hU₁ (u : ComplexL2 E) : Integrable (U u) := by
    apply (integrable_indicator_iff hSm).2
    haveI : IsFiniteMeasure ((volume : Measure E).restrict S) :=
      ⟨by simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using hS.measure_lt_top⟩
    exact ((memLp_congr_ae (ae_restrict_of_ae (s := S) (Lp.aestronglyMeasurable u).ae_eq_mk)).1
      ((Lp.memLp u).restrict S)).integrable (by norm_num)
  have hUn (u : ComplexL2 E) : ‖(hU₂ u).toLp (U u)‖ ≤ ‖u‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hU₂ u).coeFn_toLp, hUeq u] with x hx hx'
    rw [hx, hx']
    by_cases h : x ∈ S
    · rw [indicator_of_mem h]
    · simp only [indicator_of_notMem h, norm_zero, norm_nonneg]
  let g (x : E) (y : E) := conj (K x y)
  have hGlobal (x y : E) : ‖g x y‖ ≤ C * s ^ 3 := by
    rw [Complex.norm_conj]
    apply (hBound x y).trans
    have hd : 1 ≤ 1 + s * q * ‖x - y‖ := le_add_of_nonneg_right (by positivity)
    rw [div_le_iff₀ (pow_pos (zero_lt_one.trans_le hd) _)]
    exact le_mul_of_one_le_right (mul_nonneg hC (pow_nonneg hs.le _)) (one_le_pow₀ hd)
  have hG (x : E) : MemLp (g x) 2 volume := by
    have hD : MemLp (S.indicator (fun _ : E => C * s ^ 3)) 2 volume :=
      memLp_indicator_const 2 hSm _ (Or.inr hS.measure_lt_top.ne)
    refine hD.mono (Complex.continuous_conj.measurable.comp
      (hK.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ S
    · simpa only [indicator_of_mem hy, Real.norm_of_nonneg (mul_nonneg hC (pow_nonneg hs.le _))]
        using hGlobal x y
    · simp only [g, hSupp x y (Or.inr hy), map_zero, indicator_of_notMem hy, norm_zero, le_refl]
  let row (x : E) := (hG x).toLp (g x)
  have hRow0 (x : E) (hx : x ∉ S) : row x = 0 := by
    apply Lp.ext
    filter_upwards [(hG x).coeFn_toLp, Lp.coeFn_zero ℂ 2 (volume : Measure E)] with y hy hz
    simp only [row, hy, hz, g, hSupp x y (Or.inl hx), map_zero, Pi.zero_apply]
  have hPair (x : E) (u : ComplexL2 E) :
      (∫ y, K x y * U u y) = inner ℂ (row x) u := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hG x).coeFn_toLp, hUeq u] with y hy hu
    change K x y * U u y = inner ℂ ((hG x).toLp (g x) y) (u y)
    rw [hy, hu, RCLike.inner_apply', show conj (g x y) = K x y from Complex.conj_conj _]
    by_cases h : y ∈ S
    · rw [indicator_of_mem h]
    · simp only [hSupp x y (Or.inr h), indicator_of_notMem h, zero_mul]
  choose hAction hNorm using fun u =>
    overlapKernel_action_norm_le K hK C q s hC hq hs hBound (U u) (hUm u) (hU₁ u) (hU₂ u)
  let action (u : ComplexL2 E) := (hAction u).toLp (fun x => ∫ y, K x y * U u y)
  have hActionAE (u : ComplexL2 E) : action u =ᵐ[volume] fun x => inner ℂ (row x) u := by
    filter_upwards [(hAction u).coeFn_toLp] with x hx
    exact hx.trans (hPair x u)
  let R₀ : ComplexL2 E →ₗ[ℂ] ComplexL2 E :=
    { toFun := action
      map_add' := fun u v => by
        apply Lp.ext
        filter_upwards [hActionAE (u + v), hActionAE u, hActionAE v, Lp.coeFn_add (action u) (action v)]
          with x hsum hu hv he
        rw [hsum, he, Pi.add_apply, hu, hv, inner_add_right]
      map_smul' := fun c u => by
        apply Lp.ext
        filter_upwards [hActionAE (c • u), hActionAE u, Lp.coeFn_smul c (action u)]
          with x hs' hu he
        rw [RingHom.id_apply, hs', he, Pi.smul_apply, hu, inner_smul_right, smul_eq_mul] }
  let R := R₀.mkContinuous m (fun u => (hNorm u).trans (mul_le_mul_of_nonneg_left (hUn u) hm))
  have hR (u : ComplexL2 E) : R u =ᵐ[volume] fun x => inner ℂ (row x) u := hActionAE u
  have hRowDist (x y : E) (ε : ℝ)
      (h : ∀ z ∈ S, ‖K x z - K y z‖ ≤ ε) : dist (row x) (row y) ≤ ε * ‖I‖ := by
    rw [dist_eq_norm]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (row x) (row y), (hG x).coeFn_toLp, (hG y).coeFn_toLp, hI]
      with z hz hx hy hi
    rw [hz, Pi.sub_apply]
    change ‖(hG x).toLp (g x) z - (hG y).toLp (g y) z‖ ≤ ε * ‖I z‖
    rw [hx, hy, hi, show g x z - g y z = conj (K x z - K y z) from
      (map_sub (starRingEnd ℂ) _ _).symm,
      Complex.norm_conj]
    by_cases hzs : z ∈ S
    · simpa only [indicator_of_mem hzs, norm_one, mul_one] using h z hzs
    · simp only [indicator_of_notMem hzs, norm_zero, mul_zero, hSupp x z (Or.inr hzs),
        hSupp y z (Or.inr hzs), sub_zero, le_refl]
  have hRow : ContinuousOn row S := by
    refine Metric.continuousOn_iff.2 fun x hx ε hε => ?_
    have hδ₀ : 0 < ε / (‖I‖ + 1) := div_pos hε (by positivity)
    obtain ⟨δ, hδ, hUC⟩ := Metric.uniformContinuousOn_iff.mp
      (hS.prod hS |>.uniformContinuousOn_of_continuous hCont) _ hδ₀
    refine ⟨δ, hδ, fun y hy hyx => ?_⟩
    have hB := hRowDist y x (ε / (‖I‖ + 1)) (fun z hz => by
      simpa only [dist_eq_norm] using
        (hUC (y,z) ⟨hy,hz⟩ (x,z) ⟨hx,hz⟩ (by simpa only [dist_prod_same_right] using hyx)).le)
    refine hB.trans_lt ?_
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith only [hε]
  have hCompact : IsCompactOperator R := by
    change R ∈ {f : ComplexL2 E →L[ℂ] ComplexL2 E | IsCompactOperator f}
    rw [← isClosed_setOf_isCompactOperator.closure_eq]
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    let δ := ε / (‖I‖ + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    obtain ⟨B, _, hB, hCover⟩ := (hS.image_of_continuousOn hRow).finite_cover_balls hδ
    let V := Submodule.span ℂ B
    letI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ hB
    letI : ProperSpace V := FiniteDimensional.proper ℂ V
    let P := V.orthogonalProjection
    let Q := R.comp (V.subtypeL.comp P)
    have hP : IsCompactOperator P := by
      apply (isCompactOperator_iff_image_closedBall_subset_compact P.toLinearMap zero_lt_one).2
      refine ⟨Metric.closedBall 0 1, isCompact_closedBall _ _, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      simp only [Metric.mem_closedBall, dist_zero_right] at *
      exact (V.norm_orthogonalProjection_apply_le u).trans hu
    refine ⟨Q, (hP.clm_comp V.subtypeL).clm_comp R, ?_⟩
    rw [dist_eq_norm]
    have hSmall (u : ComplexL2 E) : ‖(R - Q) u‖ ≤ (δ * ‖I‖) * ‖u‖ := by
      have ht : ‖(R - Q) u‖ ≤ (δ * ‖u‖) * ‖I‖ := by
        apply Lp.norm_le_mul_norm_of_ae_le_mul
        change ∀ᵐ x ∂volume, ‖(R u - Q u) x‖ ≤ (δ * ‖u‖) * ‖I x‖
        filter_upwards [Lp.coeFn_sub (R u) (Q u), hR u, hR (V.starProjection u), hI]
          with x hx hu hv hi
        rw [hx, Pi.sub_apply, hu, show Q u = R (V.starProjection u) from rfl, hv, hi]
        by_cases hxs : x ∈ S
        · have hxrow : row x ∈ row '' S := mem_image_of_mem _ hxs
          have hMem := hCover hxrow
          rcases mem_iUnion.mp hMem with ⟨z, hz⟩
          rcases mem_iUnion.mp hz with ⟨hzB, hzδ⟩
          have hProj : ‖row x - V.starProjection (row x)‖ ≤ δ := by
            rw [Submodule.starProjection_minimal]
            let zV : V := ⟨z, Submodule.subset_span hzB⟩
            have hzlt : dist (row x) z < δ := hzδ
            exact (ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ zV).trans
              (by simpa only [zV, dist_eq_norm] using hzlt.le)
          rw [← V.inner_starProjection_left_eq_right, ← inner_sub_left, indicator_of_mem hxs,
            norm_one, mul_one]
          exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hProj (norm_nonneg _))
        · simp only [hRow0 x hxs, inner_zero_left, sub_zero, norm_zero, indicator_of_notMem hxs,
            mul_zero, le_refl]
      simpa only [mul_right_comm δ ‖u‖ ‖I‖] using ht
    have hn : ‖R - Q‖ ≤ δ * ‖I‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hδ.le (norm_nonneg _)) hSmall
    refine hn.trans_lt ?_
    dsimp only [δ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith only [hε]
  refine ⟨R, hCompact, R₀.mkContinuous_norm_le hm _, fun u => ?_⟩
  filter_upwards [hR u] with x hx
  rw [hx, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hG x).coeFn_toLp] with y hy
  change inner ℂ ((hG x).toLp (g x) y) (u y) = _
  rw [hy, RCLike.inner_apply', show conj (g x y) = K x y from Complex.conj_conj _]

end Burnett.Microlocal.Overlap
