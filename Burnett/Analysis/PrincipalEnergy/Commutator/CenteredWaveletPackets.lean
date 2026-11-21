import Burnett.Analysis.PrincipalEnergy.Paraproduct.ParaproductKernelDifference
import Burnett.Analysis.PrincipalEnergy.Commutator.LocalOscillationRamp

set_option autoImplicit false
set_option maxHeartbeats 2800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Set MeasureTheory Burnett.Analysis.FirstOrderDyadic
open scoped NNReal

theorem waveletWindow_hasCompactSupport (ψ : SchwartzMap Space ℂ)
    (hψ : ∀ z, 1<‖z‖ → ψ z=0) : HasCompactSupport (ψ : Space → ℂ) := by
  apply (isCompact_closedBall (0:Space) 1).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  by_contra h
  have hNorm : 1<‖z‖ := not_le.mp (by simpa only [Metric.mem_closedBall,dist_zero_right] using h)
  exact hz (hψ z hNorm)

/-- The actual mass-normalized translated Schwartz wavelet. -/
def centeredWavelet (ψ : SchwartzMap Space ℂ) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (s : ℝ) (hs : 0<s) (c : Space) : SchwartzMap Space ℂ :=
  (s^4)⁻¹ • translatedOscillationCutoff ψ (waveletWindow_hasCompactSupport ψ hψ) c (half_pos hs)

@[simp] theorem centeredWavelet_apply (ψ : SchwartzMap Space ℂ) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (s : ℝ) (hs : 0<s) (c x : Space) :
    centeredWavelet ψ hψ s hs c x=compactWaveletKernel ψ s (x-c) := by
  rw [centeredWavelet,SchwartzMap.smul_apply,translatedOscillationCutoff_apply,
    show 2*(s/2)=s by ring,compactWaveletKernel]

theorem centeredWavelet_support (ψ : SchwartzMap Space ℂ) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (s : ℝ) (hs : 0<s) (c : Space) :
    tsupport (centeredWavelet ψ hψ s hs c : Space → ℂ) ⊆ Metric.closedBall c s := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra h
  have hGap : s<‖x-c‖ := not_le.mp (by simpa only [Metric.mem_closedBall,dist_eq_norm] using h)
  exact hx ((centeredWavelet_apply ψ hψ s hs c x).trans
    (compactWaveletKernel_zero_outside_scale ψ hψ s hs (x-c) hGap))

theorem centeredWavelet_hasCompactSupport (ψ : SchwartzMap Space ℂ) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (s : ℝ) (hs : 0<s) (c : Space) :
    HasCompactSupport (centeredWavelet ψ hψ s hs c : Space → ℂ) :=
  (isCompact_closedBall c s).of_isClosed_subset isClosed_closure (centeredWavelet_support ψ hψ s hs c)

theorem centeredWavelet_integral (ψ : SchwartzMap Space ℂ) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (s : ℝ) (hs : 0<s) (c : Space) : (∫ z, centeredWavelet ψ hψ s hs c z)=∫ z, ψ z := by
  have ht : MeasurePreserving (fun z : Space => z-c) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure Space) (-c)
  have hK : Integrable (compactWaveletKernel ψ s) (volume : Measure Space) :=
    (ψ.integrable.comp_smul (inv_ne_zero hs.ne')).smul _
  simp only [centeredWavelet_apply]
  rw [← integral_map (f := compactWaveletKernel ψ s) ht.measurable.aemeasurable
    (by rw [ht.map_eq]; exact hK.aestronglyMeasurable),ht.map_eq]
  exact compactWaveletKernel_integral_eq ψ s hs

theorem centeredWavelet_integral_norm (ψ : SchwartzMap Space ℂ) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (s : ℝ) (hs : 0<s) (c : Space) : (∫ z, ‖centeredWavelet ψ hψ s hs c z‖)=∫ z, ‖ψ z‖ := by
  have ht : MeasurePreserving (fun z : Space => z-c) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure Space) (-c)
  have hK : Integrable (compactWaveletKernel ψ s) (volume : Measure Space) :=
    (ψ.integrable.comp_smul (inv_ne_zero hs.ne')).smul _
  simp only [centeredWavelet_apply]
  rw [← integral_map (f := fun z => ‖compactWaveletKernel ψ s z‖) ht.measurable.aemeasurable
    (by rw [ht.map_eq]; exact hK.norm.aestronglyMeasurable),ht.map_eq]
  simp only [compactWaveletKernel,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _))]
  rw [integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg volume (fun z => ‖ψ z‖) hs.le,
    finrank_euclideanSpace_fin,smul_eq_mul,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 4 hs.ne'),one_mul]

theorem centeredWavelet_norm_le (ψ : SchwartzMap Space ℂ) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (s : ℝ) (hs : 0<s) (c x : Space) :
    ‖centeredWavelet ψ hψ s hs c x‖≤(s^4)⁻¹*SchwartzMap.seminorm ℝ 0 0 ψ := by
  rw [centeredWavelet_apply]
  exact compactWaveletKernel_norm_le_scale ψ s hs (x-c)

theorem centeredWavelet_lipschitz (ψ : SchwartzMap Space ℂ) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (s : ℝ) (hs : 0<s) (c : Space) :
    LipschitzWith (.mk ((s^5)⁻¹*SchwartzMap.seminorm ℝ 0 1 ψ)
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _)) (apply_nonneg _ _)))
      (centeredWavelet ψ hψ s hs c : Space → ℂ) := by
  refine lipschitzWith_iff_norm_sub_le.mpr fun x y => ?_
  simp only [centeredWavelet_apply,NNReal.coe_mk]
  have h := compactWaveletKernel_spatial_sub_bound ψ s hs (x-c) (y-c)
  rwa [show (x-c)-(y-c)=x-y by abel] at h

theorem centeredWavelet_fderiv_bound (ψ : SchwartzMap Space ℂ) (hψ : ∀ z, 1<‖z‖ → ψ z=0)
    (s : ℝ) (hs : 0<s) (c x : Space) :
    ‖fderiv ℝ (centeredWavelet ψ hψ s hs c : Space → ℂ) x‖≤(s^5)⁻¹*SchwartzMap.seminorm ℝ 0 1 ψ :=
  norm_fderiv_le_of_lipschitz ℝ (centeredWavelet_lipschitz ψ hψ s hs c)

end Burnett.Analysis.CarlesonEmbedding
