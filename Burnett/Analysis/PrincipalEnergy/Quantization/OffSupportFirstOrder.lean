import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderActionLimit
import Burnett.Analysis.PrincipalEnergy.Quantization.LipschitzSymbolKernel

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Filter Function MeasureTheory Set Burnett.Microlocal.AngularDyadicKernel
open scoped BigOperators FourierTransform Topology

private theorem finite_kernel_continuous (a : E → E → ℂ) (x : E) (N : ℕ)
    (p : ℕ → SchwartzMap E ℂ)
    (hp : ∀ j, (p j : E → ℂ) = 𝓕⁻ (normalizedFirstOrderAnnulus a x j)) :
    Continuous (fun y : E => ∑ j ∈ Finset.range N, firstOrderAnnularKernel a x j (x-y)) := by
  apply continuous_finset_sum
  intro j _
  simp only [firstOrderAnnularKernel_eq_scaled, ← hp]
  exact continuous_const.smul ((p j).continuous.comp
    (continuous_const.smul (continuous_const.sub continuous_id)))

/-- Away from the support, the mixed multiplier difference has an ordinary
Bochner integral for the limiting high-frequency symbol. The spatial proof
uses positive separation, so it does not resolve the diagonal singularity. -/
theorem firstOrderHighCoefficientCommutator_offSupport (a : E → E → ℂ) (ha : FrequencyOrderOne a)
    (r f rf : SchwartzMap E ℂ) (hrf : ∀ y, rf y = r y * f y)
    (L : NNReal) (hLip : LipschitzWith L r) (hfC : HasCompactSupport (f : E → ℂ))
    (x : E) (hx : x ∉ tsupport (f : E → ℂ)) :
    r x * firstOrderHighAction a f x - firstOrderHighAction a rf x =
      ∫ y, coefficientKernel r (firstOrderKernel a) x y * f y := by
  obtain ⟨p, C, hC, hp, hBound⟩ := exists_normalizedInverseProfiles ha
  have hOpen : (tsupport (f : E → ℂ))ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hx
  obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.mp hOpen
  let K (N : ℕ) (u z : E) := ∑ j ∈ Finset.range N, firstOrderAnnularKernel a u j z
  have hBnd (N : ℕ) (y : E) :
      ‖coefficientKernel r (K N) x y * f y‖ ≤ ((L : ℝ) * (34*C) * (δ ^ 4)⁻¹) * ‖f y‖ := by
    by_cases hy : f y = 0
    · simp only [hy, mul_zero, norm_zero, le_refl]
    · have hy' : y ∈ tsupport (f : E → ℂ) := subset_closure hy
      have hyB : y ∉ Metric.ball x δ := fun h => hBall h hy'
      have hSep : δ ≤ ‖x-y‖ := by
        simpa only [Metric.mem_ball, dist_comm y x, dist_eq_norm, not_lt] using hyB
      have hxy : x ≠ y := by
        intro he
        simp [he] at hSep
        linarith
      have hInv : (‖x-y‖ ^ 4)⁻¹ ≤ (δ ^ 4)⁻¹ := by
        exact (inv_le_inv₀ (pow_pos (hδ.trans_le hSep) _) (pow_pos hδ _)).mpr
          (pow_le_pow_left₀ hδ.le hSep _)
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (firstOrderCoefficientKernel_size a p hp C hC hBound r L hLip N x y hxy).1.trans
        (mul_le_mul_of_nonneg_left hInv (by positivity))
  have hSpace : Tendsto (fun N => ∫ y, coefficientKernel r (K N) x y * f y) atTop
      (𝓝 (∫ y, coefficientKernel r (firstOrderKernel a) x y * f y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ((L : ℝ) * (34*C) * (δ ^ 4)⁻¹) * ‖f y‖)
      ?_ (f.integrable.norm.const_mul _) (fun N => Eventually.of_forall (hBnd N)) ?_
    · intro N
      have hK := finite_kernel_continuous a x N (p x) (hp x)
      exact (((continuous_const.sub r.continuous).mul hK).mul f.continuous).aestronglyMeasurable
    · filter_upwards with y
      by_cases hy : f y = 0
      · simp only [hy, mul_zero, tendsto_const_nhds]
      · have hxy : x ≠ y := by
          intro h
          subst y
          exact hx (subset_closure hy)
        have hs := (firstOrderKernel_size a p hp C hC hBound x (x-y) (sub_ne_zero.mpr hxy)).1
        have hConv : Tendsto (fun N => K N x (x-y)) atTop (𝓝 (firstOrderKernel a x (x-y))) :=
          hs.of_norm.hasSum.tendsto_sum_nat
        exact (tendsto_const_nhds.mul hConv).mul tendsto_const_nhds
  have hfFreq := firstOrderFiniteAction_tendsto a ha f x
  have hrfFreq := firstOrderFiniteAction_tendsto a ha rf x
  have hFreq : Tendsto (fun N => r x * firstOrderFiniteAction a N f x - firstOrderFiniteAction a N rf x)
      atTop (𝓝 (r x * firstOrderHighAction a f x - firstOrderHighAction a rf x)) :=
    (tendsto_const_nhds.mul hfFreq).sub hrfFreq
  apply tendsto_nhds_unique hFreq
  refine hSpace.congr' (Eventually.of_forall fun N => ?_)
  change (∫ y, coefficientKernel r (K N) x y * f y) =
    r x * firstOrderFiniteAction a N f x - firstOrderFiniteAction a N rf x
  rw [show (rf : E → ℂ) = fun y => r y * f y from funext hrf]
  exact (firstOrderFiniteCoefficientCommutator_eq_kernel a x (ha.smooth x).continuous N r f
    r.continuous f.continuous hfC).symm

end Burnett.Analysis.FirstOrderDyadic
