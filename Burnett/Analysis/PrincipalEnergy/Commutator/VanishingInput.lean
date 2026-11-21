import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderActionLimit
import Burnett.Analysis.PrincipalEnergy.Quantization.LipschitzSymbolKernel
import Burnett.Analysis.PrincipalEnergy.Fourier.SphereIntegration

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Filter MeasureTheory Burnett.Microlocal.AngularDyadicKernel Burnett.Microlocal.NearDiagonal
open scoped BigOperators FourierTransform Topology

private theorem finiteKernel_continuous (a : E → E → ℂ) (x : E) (N : ℕ)
    (p : ℕ → SchwartzMap E ℂ)
    (hp : ∀ j, (p j : E → ℂ) = 𝓕⁻ (normalizedFirstOrderAnnulus a x j)) :
    Continuous (fun y : E => ∑ j ∈ Finset.range N, firstOrderAnnularKernel a x j (x-y)) := by
  apply continuous_finset_sum
  intro j _
  simp only [firstOrderAnnularKernel_eq_scaled, ← hp]
  exact continuous_const.smul ((p j).continuous.comp
    (continuous_const.smul (continuous_const.sub continuous_id)))

private theorem centered_value_norm_le (g : E → ℂ) {G : NNReal} (hg : LipschitzWith G g)
    (x y : E) (hx : g x = 0) : ‖g y‖ ≤ (G : ℝ) * ‖x-y‖ := by
  simpa only [dist_eq_norm, hx, sub_zero, norm_sub_rev y x] using hg.dist_le_mul y x

/-- Vanishing at the evaluation point supplies one integrable power in four
dimensions. The original regularized operator, and not a chosen diagonal
extension of the kernel, equals this absolutely integrable action. -/
theorem firstOrderHighCoefficientCommutator_vanishingInput (a : E → E → ℂ) (ha : FrequencyOrderOne a)
    (r g rg : SchwartzMap E ℂ) (hrg : ∀ y, rg y = r y * g y)
    (L G : NNReal) (hr : LipschitzWith L r) (hg : LipschitzWith G g)
    (hgC : HasCompactSupport (g : E → ℂ)) (x : E) (hx : g x = 0) :
    Integrable (fun y => coefficientKernel r (firstOrderKernel a) x y * g y) (volume : Measure E) ∧
      r x * firstOrderHighAction a g x - firstOrderHighAction a rg x =
        ∫ y, coefficientKernel r (firstOrderKernel a) x y * g y := by
  obtain ⟨p, C, hC, hp, hProfile⟩ := exists_normalizedInverseProfiles ha
  let K (N : ℕ) (u z : E) := ∑ j ∈ Finset.range N, firstOrderAnnularKernel a u j z
  let J (N : ℕ) (y : E) := coefficientKernel r (K N) x y * g y
  let Jlim (y : E) := coefficientKernel r (firstOrderKernel a) x y * g y
  let A : ℝ := (L : ℝ) * (34*C)
  have hA : 0 ≤ A := by unfold A; positivity
  let b (y : E) := A * (G : ℝ) * inverseCubeEnvelope 1 (x-y) + A * ‖g y‖
  have hb : Integrable b (volume : Measure E) :=
    ((integrable_inverseCubeEnvelope_sub_left 1 x).const_mul _).add (g.integrable.norm.const_mul _)
  have hB (N : ℕ) (y : E) : ‖J N y‖ ≤ b y := by
    have hb₁ : 0 ≤ A * (G : ℝ) * inverseCubeEnvelope 1 (x-y) :=
      mul_nonneg (mul_nonneg hA G.coe_nonneg) (inverseCubeEnvelope_nonneg _ _)
    have hb₂ : 0 ≤ A * ‖g y‖ := mul_nonneg hA (norm_nonneg _)
    by_cases hxy : x = y
    · subst y
      have hbPos : 0 ≤ b x := add_nonneg hb₁ hb₂
      simpa only [J, hx, mul_zero, norm_zero] using hbPos
    have hPos := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hc : ‖coefficientKernel r (K N) x y‖ ≤ A * (‖x-y‖ ^ 4)⁻¹ :=
      (firstOrderCoefficientKernel_size a p hp C hC hProfile r L hr N x y hxy).1
    change ‖coefficientKernel r (K N) x y * g y‖ ≤ _
    rw [norm_mul]
    by_cases hNear : ‖x-y‖ < 1
    · have hEnv : inverseCubeEnvelope 1 (x-y) = (‖x-y‖ ^ 3)⁻¹ :=
        inverseCubeEnvelope_apply_inside 1 (x-y) hPos hNear
      calc
        _ ≤ (A * (‖x-y‖ ^ 4)⁻¹) * ((G : ℝ) * ‖x-y‖) :=
          mul_le_mul hc (centered_value_norm_le g hg x y hx) (norm_nonneg _) (by positivity)
        _ = A * (G : ℝ) * inverseCubeEnvelope 1 (x-y) := by
          rw [hEnv]
          field_simp [hPos.ne']
        _ ≤ b y := le_add_of_nonneg_right hb₂
    · have hd : (‖x-y‖ ^ 4)⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        exact one_le_pow₀ (le_of_not_gt hNear)
      exact (mul_le_mul_of_nonneg_right (hc.trans (mul_le_of_le_one_right hA hd)) (norm_nonneg _)).trans
        (le_add_of_nonneg_left hb₁)
  have hJm (N : ℕ) : Measurable (J N) := by
    have hK := finiteKernel_continuous a x N (p x) (hp x)
    exact (((continuous_const.sub r.continuous).mul hK).mul g.continuous).measurable
  have hConv (y : E) : Tendsto (fun N => J N y) atTop (𝓝 (Jlim y)) := by
    by_cases hxy : x = y
    · subst y
      simp only [J, Jlim, hx, mul_zero, tendsto_const_nhds]
    · have hs := (firstOrderKernel_size a p hp C hC hProfile x (x-y) (sub_ne_zero.mpr hxy)).1
      have hK : Tendsto (fun N => K N x (x-y)) atTop (𝓝 (firstOrderKernel a x (x-y))) :=
        hs.of_norm.hasSum.tendsto_sum_nat
      exact (tendsto_const_nhds.mul hK).mul tendsto_const_nhds
  refine ⟨hb.mono' (measurable_of_tendsto_metrizable hJm (tendsto_pi_nhds.mpr hConv)).aestronglyMeasurable ?_, ?_⟩
  · filter_upwards with y
    exact le_of_tendsto (hConv y).norm (Eventually.of_forall (fun N => hB N y))
  have hSpatial : Tendsto (fun N => ∫ y, J N y) atTop (𝓝 (∫ y, Jlim y)) :=
    tendsto_integral_of_dominated_convergence b (fun N => (hJm N).aestronglyMeasurable) hb
      (fun N => Eventually.of_forall (hB N)) (Eventually.of_forall hConv)
  have hgF := firstOrderFiniteAction_tendsto a ha g x
  have hrgF := firstOrderFiniteAction_tendsto a ha rg x
  have hFreq : Tendsto (fun N => r x * firstOrderFiniteAction a N g x - firstOrderFiniteAction a N rg x)
      atTop (𝓝 (r x * firstOrderHighAction a g x - firstOrderHighAction a rg x)) :=
    (tendsto_const_nhds.mul hgF).sub hrgF
  apply tendsto_nhds_unique hFreq
  refine hSpatial.congr' (Eventually.of_forall fun N => ?_)
  change (∫ y, J N y) = r x * firstOrderFiniteAction a N g x - firstOrderFiniteAction a N rg x
  rw [show (rg : E → ℂ) = fun y => r y * g y from funext hrg]
  exact (firstOrderFiniteCoefficientCommutator_eq_kernel a x (ha.smooth x).continuous N r g
    r.continuous g.continuous hgC).symm

end Burnett.Analysis.FirstOrderDyadic
