import Burnett.Analysis.PrincipalEnergy.Commutator.ActualFullCommutatorKernel
import Burnett.Analysis.PrincipalEnergy.Quantization.ConvolutionEnvelope
import Burnett.Analysis.PrincipalEnergy.Commutator.InverseFifthTail

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Burnett.Analysis.FirstOrderDyadic
open scoped NNReal Topology

/-- Away from the diagonal the actual full kernel retains the inverse fifth power
if the coefficient difference is estimated by its supremum. -/
theorem exists_fullCoefficientKernel_size_of_bounded {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Space → ℂ) (U : ℝ), 0 ≤ U →
      (∀ x, ‖r x‖ ≤ U) → ∀ x y, x ≠ y →
        ‖fullCoefficientKernel a r x y‖ ≤ C * U * (‖x-y‖^5)⁻¹ := by
  obtain ⟨A, _, hA, _, hLow, _⟩ := exists_firstOrderLowKernel_relative_bounds ha.frequency
  obtain ⟨p, B, hB, hp, hBound⟩ := exists_normalizedInverseProfiles ha.frequency
  refine ⟨2 * (A + 34 * B), by positivity, ?_⟩
  intro r U hU hR x y hxy
  have hz : x-y ≠ 0 := sub_ne_zero.mpr hxy
  have hDiff : ‖r x-r y‖ ≤ 2 * U := by
    calc
      ‖r x-r y‖ ≤ ‖r x‖ + ‖r y‖ := norm_sub_le _ _
      _ ≤ 2 * U := by linarith [hR x, hR y]
  have hHigh : ‖firstOrderKernel a x (x-y)‖ ≤ 34 * B * (‖x-y‖^5)⁻¹ :=
    ((firstOrderKernel_size a p hp B hB hBound x (x-y) hz).2 0).2
  unfold fullCoefficientKernel lowCoefficientKernel coefficientKernel
  calc
    ‖(r x-r y) * firstOrderLowKernel a x (x-y) +
        (r x-r y) * firstOrderKernel a x (x-y)‖ ≤
        ‖(r x-r y) * firstOrderLowKernel a x (x-y)‖ +
          ‖(r x-r y) * firstOrderKernel a x (x-y)‖ := norm_add_le _ _
    _ = ‖r x-r y‖ * ‖firstOrderLowKernel a x (x-y)‖ +
          ‖r x-r y‖ * ‖firstOrderKernel a x (x-y)‖ := by rw [norm_mul, norm_mul]
    _ ≤ (2 * U) * (A * (‖x-y‖^5)⁻¹) +
          (2 * U) * (34 * B * (‖x-y‖^5)⁻¹) :=
      add_le_add
        (mul_le_mul hDiff (hLow x (x-y) hz) (norm_nonneg _) (by positivity))
        (mul_le_mul hDiff hHigh (norm_nonneg _) (by positivity))
    _ = 2 * (A + 34 * B) * U * (‖x-y‖^5)⁻¹ := by ring

/-- A real weight applied to the actual low and high coefficient kernels. -/
def weightedCoefficientKernel (a : Space → Space → ℂ) (r : Space → ℂ)
    (w : Space × Space → ℝ) (x y : Space) : ℂ :=
  w (x,y) • fullCoefficientKernel a r x y

theorem weightedCoefficientKernel_continuous {a : Space → Space → ℂ}
    {r : Space → ℂ} {C : ℝ}
    (hK : CalderonZygmundKernelBounds (fullCoefficientKernel a r) C)
    {w : Space × Space → ℝ} (hw : Continuous w) {d : ℝ} (hd : 0 < d)
    (hZero : ∀ p : Space × Space, ‖p.1 - p.2‖ < d → w p = 0) :
    Continuous (Function.uncurry (weightedCoefficientKernel a r w)) := by
  let H := Function.uncurry (weightedCoefficientKernel a r w)
  have hz (p : Space × Space) (hp : ‖p.1-p.2‖ < d) : H p = 0 := by
    change w p • fullCoefficientKernel a r p.1 p.2 = 0
    rw [hZero p hp, zero_smul]
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p.1 ≠ p.2
  · exact hw.continuousAt.smul (hK.continuousAt_offDiagonal p.1 p.2 hp)
  · have hSmall : ‖p.1-p.2‖ < d := by
      rwa [not_ne_iff.mp hp, sub_self, norm_zero]
    have hOpen : IsOpen {q : Space × Space | ‖q.1-q.2‖ < d} :=
      isOpen_lt (continuous_fst.sub continuous_snd).norm continuous_const
    have hx : ∀ᶠ q : Space × Space in 𝓝 p, ‖q.1-q.2‖ < d := hOpen.mem_nhds hSmall
    change Tendsto H (𝓝 p) (𝓝 (H p))
    rw [hz p hSmall]
    exact tendsto_const_nhds.congr' (hx.mono fun q hq => (hz q hq).symm)

/-- The weighted, separated part of the actual coefficient kernel acts in
L2 uniformly in the choice of weight. In dimension four its bound contains
the inverse separation distance. -/
theorem exists_weightedCoefficientTail_L2_action_bound {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (r : Space → ℂ) (L : NNReal) (U : ℝ), LipschitzWith L r → 0 ≤ U →
      (∀ x, ‖r x‖ ≤ U) → ∀ (d : ℝ), 0 < d →
      ∀ (w : Space × Space → ℝ), Continuous w → (∀ p, 0 ≤ w p) →
      (∀ p, w p ≤ 1) → (∀ p, ‖p.1-p.2‖ < d → w p = 0) →
      ∀ (f : SchwartzMap Space ℂ),
        ∃ hA : MemLp (fun x => ∫ y, weightedCoefficientKernel a r w x y * f y) 2 volume,
          ‖hA.toLp (fun x => ∫ y, weightedCoefficientKernel a r w x y * f y)‖ ≤
            C * U * d⁻¹ * ‖(f.memLp 2 volume).toLp (f : Space → ℂ)‖ := by
  obtain ⟨A, hA, hSize⟩ := exists_fullCoefficientKernel_size_of_bounded ha
  obtain ⟨B, _, hCZ⟩ := exists_fullCoefficientKernel_bounds ha
  let M : ℝ := ∫ z, inverseFifthTail 1 z
  have hM : 0 ≤ M := integral_nonneg (inverseFifthTail_nonneg 1)
  refine ⟨A * M, by positivity, ?_⟩
  intro r L U hLip hU hR d hd w hw hw₀ hw₁ hwGap f
  let D : Space → ℝ := fun z => (A * U) * inverseFifthTail d z
  have hTailMeas : Measurable (inverseFifthTail d) :=
    Measurable.ite (measurableSet_le measurable_const measurable_norm) (by fun_prop) measurable_const
  have hD : Measurable D := measurable_const.mul hTailMeas
  have hD₀ (z : Space) : 0 ≤ D z := mul_nonneg (mul_nonneg hA hU) (inverseFifthTail_nonneg d z)
  have hDInt : Integrable D := (inverseFifthTail_integrable hd).const_mul _
  have hK := weightedCoefficientKernel_continuous (hCZ r L hLip) hw hd hwGap
  have hDom (x y : Space) : ‖weightedCoefficientKernel a r w x y‖ ≤ D (x-y) := by
    change ‖w (x,y) • fullCoefficientKernel a r x y‖ ≤ (A * U) * inverseFifthTail d (x-y)
    by_cases hFar : d ≤ ‖x-y‖
    · have hxy : x ≠ y := by
        intro h
        rw [h, sub_self, norm_zero] at hFar
        exact (not_le_of_gt hd) hFar
      rw [inverseFifthTail, if_pos hFar, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw₀ _)]
      calc
        w (x,y) * ‖fullCoefficientKernel a r x y‖ ≤
            1 * ‖fullCoefficientKernel a r x y‖ :=
          mul_le_mul_of_nonneg_right (hw₁ _) (norm_nonneg _)
        _ ≤ (A * U) * (‖x-y‖^5)⁻¹ := by
          rw [one_mul]
          exact hSize r U hU hR x y hxy
    · rw [hwGap (x,y) (lt_of_not_ge hFar), zero_smul, norm_zero, inverseFifthTail,
        if_neg hFar, mul_zero]
  obtain ⟨hAction, hActionBound⟩ :=
    convolution_envelope_action_norm_le _ hK.measurable D hD hD₀ hDInt hDom
      f f.continuous.measurable f.integrable (f.memLp 2 volume)
  refine ⟨hAction, hActionBound.trans_eq ?_⟩
  change ((∫ z, (A * U) * inverseFifthTail d z) * _) = _
  rw [integral_const_mul, inverseFifthTail_integral_scale hd]
  change (A * U * (d⁻¹ * M)) * _ = _
  ring

end Burnett.Analysis.CarlesonEmbedding
