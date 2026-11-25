import Burnett.Analysis.TransportPatches.ProjectedRemainderScale
import Burnett.Analysis.GaugeProjection.WholeSpaceProjectedVacuumSource

/-! The first gradient cost in the actual projected divergence estimate.
The derivative of the cutoff multiplies the original undifferentiated
metric error, with exactly the same compact patch volume. -/
set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 4300000

noncomputable section

namespace Burnett.C03

open Set MeasureTheory Burnett.P01 Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.A07 (coordinateDerivative)
open scoped ENNReal ContDiff BigOperators

open private norm_scalarPartial_le_first from Burnett.Analysis.TransportPatches.ProjectedRemainderScale
open private coordinateDerivative_real localizedMetricEntry_smooth from
  Burnett.Analysis.GaugeProjection.WholeSpaceProjectedVacuumSource

/-- Actual gradient mass of the localized Schwartz input to the projected
divergence. This controls all four derivative slots on the whole space. -/
theorem localizedMetricGradientMass_le_patch_measure
    (g g₀ : CoordinateSpace → Tensor2) (hg : SmoothCoordinateComponents g)
    (hg₀ : SmoothCoordinateComponents g₀) (χ : CoordinateSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hSupp : tsupport χ ⊆ K)
    (ℓ B₀ B₁ D e : ℝ) (hℓ : 0 < ℓ) (h₀ : 0 ≤ B₀) (h₁ : 0 ≤ B₁)
    (hD : 0 ≤ D) (he : 0 ≤ e)
    (hχ₀ : ∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ 0 χ x‖ ≤ B₀)
    (hχ₁ : ∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ 1 χ x‖ ≤ B₁ * ℓ⁻¹)
    (hField : ∀ x ∈ tsupport χ, ‖g x - g₀ x‖ ≤ e ∧
      ‖coordinateJet g x - coordinateJet g₀ x‖ ≤ D) :
    projectedSourceGradientMass (localizedMetricSchwartz g g₀ χ hχ hc hg hg₀) ≤
      4 * (ENNReal.ofReal (B₀ * D + (B₁ * ℓ⁻¹) * e) *
        volume K ^ ((1 : ℝ) / 2)).toReal := by
  let M := B₀ * D + (B₁ * ℓ⁻¹) * e
  let F := K.indicator (fun _ => M)
  have hScale : 0 ≤ B₁ * ℓ⁻¹ := mul_nonneg h₁ (inv_nonneg.mpr hℓ.le)
  have hM : 0 ≤ M := add_nonneg (mul_nonneg h₀ hD) (mul_nonneg hScale he)
  have hF : MemLp F 2 volume :=
    memLp_indicator_const 2 hK.isClosed.measurableSet _ (Or.inr hK.measure_lt_top.ne)
  have hPartial (a i j : Index) (x : CoordinateSpace) :
      ‖scalarPartial (localizedMetricEntry g g₀ χ i j) a x‖ ≤ F x := by
    by_cases hx : x ∈ tsupport χ
    · have hC₀ : ‖χ x‖ ≤ B₀ := by simpa only [norm_iteratedFDeriv_zero] using hχ₀ x hx
      have hC₁ := (norm_scalarPartial_le_first χ x a).trans (hχ₁ x hx)
      have hVal : ‖g x i j - g₀ x i j‖ ≤ e :=
        ((norm_le_pi_norm ((g x - g₀ x) i) j).trans
          (norm_le_pi_norm (g x - g₀ x) i)).trans (hField x hx).1
      let dj := coordinateJet g x - coordinateJet g₀ x
      have hd : ‖dj a i j‖ ≤ D := ((norm_le_pi_norm (dj a i) j).trans
        ((norm_le_pi_norm (dj a) i).trans (norm_le_pi_norm dj a))).trans (hField x hx).2
      have hDiff : scalarPartial (fun y => g y i j - g₀ y i j) a x = dj a i j := by
        simp only [scalarPartial, coordinateJet, dj, Pi.sub_apply,
          fderiv_fun_sub ((hg i j).differentiable (by simp) x) ((hg₀ i j).differentiable (by simp) x),
          ContinuousLinearMap.sub_apply]
      change ‖scalarPartial (fun y => χ y * (g y i j - g₀ y i j)) a x‖ ≤ _
      rw [scalarPartial_product _ _ _ _ (hχ.differentiable (by simp) x)
        (((hg i j).sub (hg₀ i j)).differentiable (by simp) x), hDiff]
      change _ ≤ K.indicator (fun _ => M) x
      rw [indicator_of_mem (hSupp hx)]
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul]
      simpa only [M, add_comm] using add_le_add
        (mul_le_mul hC₁ hVal (norm_nonneg _) hScale) (mul_le_mul hC₀ hd (norm_nonneg _) h₀)
    · have hs : x ∉ tsupport (localizedMetricEntry g g₀ χ i j) :=
        fun h => hx (tsupport_mul_subset_left h)
      simp only [scalarPartial, fderiv_of_notMem_tsupport ℝ hs, ContinuousLinearMap.zero_apply, norm_zero]
      by_cases hxK : x ∈ K
      · simpa only [F, indicator_of_mem hxK] using hM
      · simp only [F, indicator_of_notMem hxK, le_rfl]
  have hMass : projectedSourceGradientMass (localizedMetricSchwartz g g₀ χ hχ hc hg hg₀) ≤
      4 * (eLpNorm F 2 volume).toReal := by
    unfold projectedSourceGradientMass
    calc
      _ ≤ ∑ _ : Fin 4, (eLpNorm F 2 volume).toReal := by
        apply Finset.sum_le_sum
        intro a _
        apply (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2
        intro i
        apply (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2
        intro j
        change ‖(coordinateDerivative a _).toLp 2 volume‖ ≤ _
        rw [SchwartzMap.toLp, Lp.norm_toLp]
        apply ENNReal.toReal_mono hF.2.ne
        apply eLpNorm_mono_real
        intro x
        rw [coordinateDerivative_real _ (localizedMetricEntry g g₀ χ i j) (fun _ => rfl) x
          ((localizedMetricEntry_smooth g g₀ hg hg₀ χ hχ i j).differentiable (by simp) x),
          Complex.norm_real]
        exact hPartial a i j x
      _ = _ := by simp [nsmul_eq_mul]
  refine hMass.trans_eq ?_
  dsimp only [F]
  rw [eLpNorm_indicator_const hK.isClosed.measurableSet (by norm_num) (by simp),
    ← ofReal_norm, Real.norm_of_nonneg hM]
  norm_num [M]

end Burnett.C03
