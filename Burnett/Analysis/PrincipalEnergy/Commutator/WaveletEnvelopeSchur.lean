import Burnett.Analysis.PrincipalEnergy.Commutator.FarWaveletSchur
import Burnett.Analysis.PrincipalEnergy.Quantization.ConvolutionEnvelope

set_option autoImplicit false
set_option maxHeartbeats 3400000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Function Burnett.Analysis.FirstOrderDyadic Burnett.Fourier

def waveletNearCutoff (t : ℝ) : Space → ℝ :=
  (Metric.closedBall (0:Space) (4*t)).indicator fun _ => 1

private theorem waveletNearCutoff_measurable (t : ℝ) : Measurable (waveletNearCutoff t) :=
  measurable_const.indicator Metric.isClosed_closedBall.measurableSet

private theorem waveletNearCutoff_integrable (t : ℝ) : Integrable (waveletNearCutoff t) := by
  exact (integrableOn_const
    (isCompact_closedBall (0:Space) (4*t)).measure_lt_top.ne).integrable_indicator
    Metric.isClosed_closedBall.measurableSet

private theorem waveletNearCutoff_nonneg (t : ℝ) (z : Space) : 0≤waveletNearCutoff t z := by
  by_cases hz : z ∈ Metric.closedBall (0:Space) (4*t)
  · simp [waveletNearCutoff,Set.indicator_of_mem hz]
  · simp [waveletNearCutoff,Set.indicator_of_notMem hz]

private theorem waveletNearCutoff_integral_scale {t : ℝ} (ht : 0<t) :
    (t^4)⁻¹*(∫ z, waveletNearCutoff t z) = ∫ z, waveletNearCutoff 1 z := by
  have hScale (z : Space) : waveletNearCutoff t (t • z)=waveletNearCutoff 1 z := by
    have hRegion : t • z ∈ Metric.closedBall (0:Space) (4*t) ↔
        z ∈ Metric.closedBall (0:Space) (4*1) := by
      simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg ht.le,mul_one]
      rw [mul_comm (4:ℝ) t,mul_le_mul_iff_right₀ ht]
    by_cases hz : z ∈ Metric.closedBall (0:Space) (4*1)
    · simp only [waveletNearCutoff,Set.indicator_of_mem hz,Set.indicator_of_mem (hRegion.mpr hz)]
    · simp only [waveletNearCutoff,Set.indicator_of_notMem hz,Set.indicator_of_notMem (mt hRegion.mp hz)]
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure Space) (waveletNearCutoff t) t
    (hR := ht.le)
  rw [show Module.finrank ℝ Space=4 from finrank_euclideanSpace_fin] at h
  simpa only [hScale,smul_eq_mul] using h.symm

/-- Integrable convolution envelope for the two orders of spatial separation. -/
def twoScaleWaveletEnvelope (A B s t : ℝ) (z : Space) : ℝ :=
  (A*Real.sqrt (s/t)*(t^4)⁻¹)*waveletNearCutoff t z+
    (B*s)*inverseFifthTail (4*t) z

/-- The fine/coarse Schur gain follows from the physical ball and inverse
fifth tail, with the same scale ratio in both directions of integration. -/
theorem twoScaleWaveletEnvelope_schur
    (K : Space → Space → ℂ) (hK : Measurable (uncurry K))
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B) (s t : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≤t)
    (hNear : ∀ x y : Space, ‖x-y‖≤4*t → ‖K x y‖≤A*Real.sqrt (s/t)*(t^4)⁻¹)
    (hFar : ∀ x y : Space, 4*t≤‖x-y‖ → ‖K x y‖≤B*s*(‖x-y‖^5)⁻¹)
    (f : SchwartzMap Space ℂ) :
    let U (x : Space) := ∫ y, K x y*f y
    ∃ hU : MemLp U 2 volume,
      ‖hU.toLp U‖≤(A*(∫ z, waveletNearCutoff 1 z)+
        B*(∫ z, inverseFifthTail 1 z)/4)*Real.sqrt (s/t)*‖f.toLp 2 volume‖ := by
  intro U
  let V := twoScaleWaveletEnvelope A B s t
  let q := Real.sqrt (s/t)
  let J := ∫ z : Space, waveletNearCutoff 1 z
  let Q := ∫ z : Space, inverseFifthTail 1 z
  have hJ : 0≤J := integral_nonneg (waveletNearCutoff_nonneg _)
  have hQ : 0≤Q := integral_nonneg (inverseFifthTail_nonneg _)
  have hVM : Measurable V := by
    have htM : Measurable (inverseFifthTail (4*t)) := by
      unfold inverseFifthTail
      exact Measurable.ite (measurableSet_le measurable_const measurable_norm)
        (by fun_prop) measurable_const
    exact (measurable_const.mul (waveletNearCutoff_measurable t)).add (measurable_const.mul htM)
  have hVi : Integrable V :=
    ((waveletNearCutoff_integrable t).const_mul _).add
      ((inverseFifthTail_integrable (by positivity : 0<4*t)).const_mul _)
  have hV₀ (z : Space) : 0≤V z :=
    add_nonneg (mul_nonneg (by positivity) (waveletNearCutoff_nonneg _ _))
      (mul_nonneg (by positivity) (inverseFifthTail_nonneg _ _))
  have hDom (x y : Space) : ‖K x y‖≤V (x-y) := by
    by_cases h : ‖x-y‖≤4*t
    · have hz : x-y ∈ Metric.closedBall (0:Space) (4*t) := by simpa only [Metric.mem_closedBall,dist_zero_right]
      refine (hNear x y h).trans ?_
      simp only [V,twoScaleWaveletEnvelope,waveletNearCutoff,Set.indicator_of_mem hz,mul_one]
      exact le_add_of_nonneg_right (mul_nonneg (by positivity) (inverseFifthTail_nonneg _ _))
    · have hd := (lt_of_not_ge h).le
      refine (hFar x y hd).trans ?_
      simp only [V,twoScaleWaveletEnvelope,inverseFifthTail,if_pos hd]
      exact le_add_of_nonneg_left (mul_nonneg (by positivity) (waveletNearCutoff_nonneg _ _))
  obtain ⟨hU,hUL⟩ := convolution_envelope_action_norm_le K hK V hVM hV₀ hVi hDom f
    f.continuous.measurable f.integrable (f.memLp 2 volume)
  refine ⟨hU,hUL.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hq : 0≤q := Real.sqrt_nonneg _
  have hqSq : q^2=s/t := Real.sq_sqrt (div_nonneg hs.le ht.le)
  have hqOne : q≤1 := (sq_le_sq₀ hq zero_le_one).mp
    (by rw [hqSq,one_pow]; exact (div_le_one ht).mpr hst)
  have hRatio : s/t≤q := by
    rw [← hqSq]
    nlinarith only [mul_nonneg hq (sub_nonneg.mpr hqOne)]
  have hInt : (∫ z, V z)=A*q*J+(B*Q/4)*(s/t) := by
    dsimp only [V,twoScaleWaveletEnvelope]
    rw [integral_add ((waveletNearCutoff_integrable t).const_mul _)
      ((inverseFifthTail_integrable (by positivity : 0<4*t)).const_mul _),integral_const_mul,
      integral_const_mul,inverseFifthTail_integral_scale (by positivity : 0<4*t),
      mul_assoc (A*q),waveletNearCutoff_integral_scale ht]
    dsimp only [J,Q]
    field_simp [ht.ne']
  calc
    _ = A*q*J+(B*Q/4)*(s/t) := hInt
    _ ≤ A*q*J+(B*Q/4)*q :=
      add_le_add_left (mul_le_mul_of_nonneg_left hRatio (by positivity)) _
    _ = _ := by dsimp only [q,J,Q]; ring

end Burnett.Analysis.CarlesonEmbedding
