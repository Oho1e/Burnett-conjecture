import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderActionLimit

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Filter MeasureTheory Set Burnett.Microlocal.AngularDyadicKernel
open scoped FourierTransform Topology BigOperators

/-- Off the actual support of a Schwartz input, the full limiting high-frequency
action is the absolutely convergent Bochner integral of the kernel itself. -/
theorem firstOrderHighAction_offSupport {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (f : SchwartzMap E ℂ) (x : E) (hx : x ∉ tsupport (f : E → ℂ)) :
    Integrable (fun y => firstOrderKernel a x (x-y) * f y) ∧
      firstOrderHighAction a f x = ∫ y, firstOrderKernel a x (x-y) * f y := by
  obtain ⟨p,C,hC,hP,hBound⟩ := exists_normalizedInverseProfiles ha
  obtain ⟨δ,hδ,hBall⟩ := Metric.mem_nhds_iff.mp (isClosed_closure.isOpen_compl.mem_nhds hx)
  let K (n : ℕ) (y : E) := (∑ j ∈ Finset.range n, firstOrderAnnularKernel a x j (x-y)) * f y
  let k (y : E) := firstOrderKernel a x (x-y) * f y
  let Ψ (y : E) := 34 * C * (δ^5)⁻¹ * ‖f y‖
  have hDist (y : E) (hy : f y ≠ 0) : δ ≤ ‖x-y‖ := by
    have hOut : y ∉ Metric.ball x δ := fun h => hBall h (subset_closure hy)
    simpa only [Metric.mem_ball,dist_comm y x,dist_eq_norm,not_lt] using hOut
  have hControl (y : E) (hy : f y ≠ 0) :
      x-y ≠ 0 ∧ (‖x-y‖^5)⁻¹ ≤ (δ^5)⁻¹ := by
    have hD := hDist y hy
    have hPos := hδ.trans_le hD
    exact ⟨norm_pos_iff.mp hPos,(inv_le_inv₀ (pow_pos hPos _) (pow_pos hδ _)).mpr
      (pow_le_pow_left₀ hδ.le hD _)⟩
  have hM (n : ℕ) : AEStronglyMeasurable (K n) (volume : Measure E) := by
    have hCont : Continuous (fun y : E => ∑ j ∈ Finset.range n,
        firstOrderAnnularKernel a x j (x-y)) := by
      apply continuous_finset_sum
      intro j _
      simp only [firstOrderAnnularKernel_eq_scaled,← hP x j]
      exact continuous_const.smul ((p x j).continuous.comp
        (continuous_const.smul (continuous_const.sub continuous_id)))
    exact (hCont.mul f.continuous).aestronglyMeasurable
  have hDom (n : ℕ) (y : E) : ‖K n y‖ ≤ Ψ y := by
    by_cases hy : f y = 0
    · simp only [K, Ψ, hy, mul_zero, norm_zero, le_refl]
    obtain ⟨hn,hi⟩ := hControl y hy
    rw [show K n y = (∑ j ∈ Finset.range n, firstOrderAnnularKernel a x j (x-y)) * f y from rfl, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact ((firstOrderKernel_size a p hP C hC hBound x (x-y) hn).2 n).1.trans
      (mul_le_mul_of_nonneg_left hi (by positivity))
  have hLim (y : E) : Tendsto (fun n => K n y) atTop (𝓝 (k y)) := by
    by_cases hy : f y = 0
    · simp only [K,k,hy,mul_zero,tendsto_const_nhds]
    have hn := (hControl y hy).1
    exact ((firstOrderKernel_size a p hP C hC hBound x (x-y) hn).1.of_norm.hasSum.tendsto_sum_nat).mul
      tendsto_const_nhds
  have hInt : Integrable Ψ := f.integrable.norm.const_mul _
  have hLim₁ : Integrable k := by
    refine hInt.mono' (aestronglyMeasurable_of_tendsto_ae atTop hM (Eventually.of_forall hLim)) ?_
    exact Eventually.of_forall fun y =>
      le_of_tendsto ((hLim y).norm) (Eventually.of_forall fun n => hDom n y)
  have hSpatial : Tendsto (fun n => ∫ y, K n y) atTop (𝓝 (∫ y, k y)) :=
    tendsto_integral_of_dominated_convergence Ψ hM hInt
      (fun n => Eventually.of_forall (hDom n)) (Eventually.of_forall hLim)
  have hFrequency := firstOrderFiniteAction_tendsto a ha f x
  refine ⟨hLim₁,tendsto_nhds_unique hFrequency ?_⟩
  exact hSpatial.congr' (Eventually.of_forall fun n =>
    (firstOrderFiniteAction_eq_kernel a x (ha.smooth x).continuous n f f.integrable).symm)

end Burnett.Analysis.FirstOrderDyadic
