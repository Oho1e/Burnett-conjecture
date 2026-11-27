import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactKernelOrderZero

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The derivative in the parameter while the integration variable is fixed. -/
def compactFrequencyParameterDerivative (F : P → E → ℂ) (q : P) (ξ : E) : P →L[ℝ] ℂ :=
  (fderiv ℝ (Function.uncurry F) (q,ξ)).comp (ContinuousLinearMap.inl ℝ P E)

/-- Differentiation in each parameter of the actual compact frequency integral. The
support is fixed only in frequency. The parameter can run over all of its space. -/
theorem compact_frequency_parameter_integral_contDiff (F : P → E → ℂ) (R : ℝ)
    (smooth : ContDiff ℝ 1 (Function.uncurry F))
    (supported : ∀ q ξ, ξ ∉ closedBall (0 : E) R → F q ξ = 0) :
    ContDiff ℝ 1 (fun q => ∫ ξ : E, F q ξ) ∧ ∀ q,
      Integrable (compactFrequencyParameterDerivative F q) volume ∧
      HasFDerivAt (fun q => ∫ ξ : E, F q ξ)
        (∫ ξ : E, compactFrequencyParameterDerivative F q ξ) q := by
  let G := compactFrequencyParameterDerivative F
  have hd (q : P) (ξ : E) : HasFDerivAt (fun t => F t ξ) (G q ξ) q := by
    have dq := (smooth.differentiable le_rfl (q,ξ)).hasFDerivAt
    have pair : HasFDerivAt (fun t : P => (t,ξ)) (ContinuousLinearMap.inl ℝ P E) q :=
      hasFDerivAt_prodMk_left q ξ
    exact dq.comp q pair
  have FC (q : P) : Continuous (F q) :=
    smooth.continuous.comp (continuous_const.prodMk continuous_id)
  have GC : Continuous (Function.uncurry G) :=
    (smooth.continuous_fderiv le_rfl).clm_comp_const _
  have Gzero (q : P) (ξ : E) (hξ : ξ ∉ closedBall (0 : E) R) : G q ξ = 0 := by
    have zeroSection : (fun t => F t ξ) = (fun _ : P => (0 : ℂ)) :=
      funext fun t => supported t ξ hξ
    have h := hd q ξ
    rw [zeroSection] at h
    exact h.unique (hasFDerivAt_const 0 q)
  have GI (q : P) : Integrable (G q) volume := by
    apply (GC.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) R)
      (by
        intro ξ n
        by_contra hξ
        exact n (Gzero q ξ hξ))
  have FI (q : P) : Integrable (F q) volume := by
    apply (FC q).integrable_of_hasCompactSupport
    exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) R)
      (by
        intro ξ n
        by_contra hξ
        exact n (supported q ξ hξ))
  have atParameter (q : P) : HasFDerivAt (fun t => ∫ ξ : E, F t ξ)
        (∫ ξ : E, G q ξ) q ∧ ContinuousAt (fun t => ∫ ξ : E, G t ξ) q := by
    let S := closedBall (0 : E) R
    have gNorm : Continuous (fun p : P × E => ‖G p.1 p.2‖) := GC.norm
    obtain ⟨A, hA⟩ := ((isCompact_closedBall q 1).prod
      (isCompact_closedBall (0 : E) R)).bddAbove_image gNorm.continuousOn
    let bound : E → ℝ := S.indicator (fun _ => A)
    have bI : Integrable bound volume := by
      have hS : MeasurableSet S := isClosed_closedBall.measurableSet
      rw [integrable_indicator_iff hS]
      exact continuousOn_const.integrableOn_compact (isCompact_closedBall (0 : E) R)
    have b (ξ : E) (t : P) (ht : t ∈ ball q 1) : ‖G t ξ‖ ≤ bound ξ := by
      by_cases hξ : ξ ∈ S
      · rw [show bound ξ = A from indicator_of_mem hξ _]
        exact hA ⟨(t,ξ),⟨ball_subset_closedBall ht,hξ⟩,rfl⟩
      · rw [show bound ξ = 0 from indicator_of_notMem hξ _, Gzero t ξ hξ, norm_zero]
    constructor
    · apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F := F) (F' := G)
        (bound := bound) (ε := 1) (by norm_num)
      · exact Eventually.of_forall fun t => (FC t).aestronglyMeasurable
      · exact FI q
      · exact (GI q).aestronglyMeasurable
      · exact Eventually.of_forall b
      · exact bI
      · exact Eventually.of_forall fun ξ t _ => hd t ξ
    · apply continuousAt_of_dominated (F := G) (bound := bound)
      · exact Eventually.of_forall fun t => (GI t).aestronglyMeasurable
      · filter_upwards [ball_mem_nhds q (by norm_num : (0 : ℝ) < 1)] with t ht
        exact Eventually.of_forall fun ξ => b ξ t ht
      · exact bI
      · exact Eventually.of_forall fun ξ =>
          (GC.comp (continuous_id.prodMk continuous_const)).continuousAt
  have intDerivative : fderiv ℝ (fun q => ∫ ξ : E, F q ξ) =
      (fun q => ∫ ξ : E, G q ξ) := funext fun q => (atParameter q).1.fderiv
  refine ⟨contDiff_one_iff_fderiv.mpr ⟨fun q => (atParameter q).1.differentiableAt, ?_⟩,
    fun q => ⟨GI q,(atParameter q).1⟩⟩
  rw [intDerivative]
  exact continuous_iff_continuousAt.mpr fun q => (atParameter q).2

end Burnett.A03
