import Burnett.Analysis.GaugeProjection.ProjectedFiniteLp
import Burnett.Analysis.GaugeProjection.LocalizedMetricSchwartzInputs

set_option autoImplicit false
set_option maxHeartbeats 2800000

noncomputable section

namespace Burnett.P01

open MeasureTheory Set Filter
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.A07 (coordinateDerivative)
open scoped ContDiff ENNReal NNReal Topology

private theorem projectionMatrixLpNorm_le_of_support
    (w : ProjectionSchwartzMatrix) (K : Set CoordinateSpace) (hK : MeasurableSet K)
    (p : ℝ) (hp : 0 < p) (M : ℝ) (hM : 0 ≤ M)
    (hZero : ∀ x i j, x ∉ K → w i j x = 0)
    (hBound : ∀ x i j, ‖w i j x‖ ≤ M) :
    projectionMatrixLpNorm p w ≤ ENNReal.ofReal M * volume K ^ (1 / p) := by
  have hp₀ : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  calc
    _ ≤ eLpNorm (K.indicator fun _ => M) (ENNReal.ofReal p) volume := by
      refine eLpNorm_mono_real (fun x => ?_)
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
        exact (pi_norm_le_iff_of_nonneg hM).2 fun i =>
          (pi_norm_le_iff_of_nonneg hM).2 fun j => hBound x i j
      · rw [indicator_of_notMem hx]
        have hfield : (fun i j => w i j x) = (0 : Fin 4 → Fin 4 → ℂ) := by
          funext i j
          exact hZero x i j hx
        rw [hfield, norm_zero]
    _ = _ := by
      rw [eLpNorm_indicator_const hK hp₀ ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp.le, Real.enorm_of_nonneg hM]

private theorem coordinateDerivative_norm_le
    (f : SchwartzMap CoordinateSpace ℂ) (L : ℝ≥0) (hL : LipschitzWith L (f : CoordinateSpace → ℂ))
    (b : Index) (x : CoordinateSpace) :
    ‖coordinateDerivative b f x‖ ≤ (L : ℝ) := by
  have h := (fderiv ℝ f x).le_opNorm (EuclideanSpace.single b (1 : ℝ))
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at h
  simpa only [coordinateDerivative, SchwartzMap.pderivCLM_apply] using
    h.trans (norm_fderiv_le_of_lipschitz ℝ hL)

private theorem coordinateDerivative_zero_outside
    (f : SchwartzMap CoordinateSpace ℂ) (K : Set CoordinateSpace)
    (hK : tsupport (f : CoordinateSpace → ℂ) ⊆ K)
    (b : Index) (x : CoordinateSpace) (hx : x ∉ K) :
    coordinateDerivative b f x = 0 := by
  have hr : fderiv ℝ (f : CoordinateSpace → ℂ) x = 0 := by
    by_contra h
    exact hx (hK (support_fderiv_subset ℝ h))
  simp only [coordinateDerivative, SchwartzMap.pderivCLM_apply, hr, ContinuousLinearMap.zero_apply]

def projectionGradientLpNorm (p : ℝ) (w : ProjectionSchwartzMatrix) : ℝ≥0∞ :=
  eLpNorm (fun x : CoordinateSpace => fun b i j => projectionMatrixDerivative b w i j x)
    (ENNReal.ofReal p) volume

private theorem projectionGradientLpNorm_le_sum (p : ℝ) (hp : 1 ≤ ENNReal.ofReal p)
    (w : ProjectionSchwartzMatrix) :
    projectionGradientLpNorm p w ≤ ∑ b, projectionMatrixLpNorm p (projectionMatrixDerivative b w) := by
  let F (b : Fin 4) (x : CoordinateSpace) := fun i j => projectionMatrixDerivative b w i j x
  have h_cont (b : Fin 4) : Continuous (F b) := by
    exact continuous_pi fun i => continuous_pi fun j => (projectionMatrixDerivative b w i j).continuous
  have hEq : (fun x => ∑ b, ‖F b x‖) = ∑ b, (fun x => ‖F b x‖) := by
    funext x
    simp only [Finset.sum_apply]
  calc
    _ ≤ eLpNorm (fun x => ∑ b, ‖F b x‖) (ENNReal.ofReal p) volume := by
      apply eLpNorm_mono_real
      intro x
      exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b =>
        Finset.single_le_sum (f := fun b => ‖F b x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b)
    _ ≤ _ := by
      rw [hEq]
      simpa only [eLpNorm_norm, projectionMatrixLpNorm, F] using
        eLpNorm_sum_le (f := fun b x => ‖F b x‖) (s := Finset.univ)
          (fun b _ => (h_cont b).norm.aestronglyMeasurable) hp

private theorem tendsto_projectionMatrixLpNorm_zero_of_uniform
    (w : ℕ → ProjectionSchwartzMatrix) (K : Set CoordinateSpace) (hK : IsCompact K)
    (p : ℝ) (hp : 0 < p)
    (hZero : ∀ n x i j, x ∉ K → w n i j x = 0)
    (hSmall : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ x i j, ‖w n i j x‖ < ε) :
    Tendsto (fun n => projectionMatrixLpNorm p (w n)) atTop (𝓝 0) := by
  let V : ℝ≥0∞ := volume K ^ (1 / p)
  have hV : V < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by positivity) hK.measure_lt_top.ne
  have hReal : Tendsto (fun m : ℕ => (1/2 : ℝ)^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hENN : Tendsto (fun m : ℕ => ENNReal.ofReal ((1/2 : ℝ)^m)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hReal
  have hMix : Tendsto (fun m : ℕ => ENNReal.ofReal ((1/2 : ℝ)^m) * V) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hENN (Or.inr hV.ne)
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨m, hm⟩ := eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 hMix ε hε)
  let δ := (1/2 : ℝ)^m
  have hδ : 0 < δ := by positivity
  filter_upwards [hSmall δ hδ] with n hn
  exact (projectionMatrixLpNorm_le_of_support (w n) K hK.isClosed.measurableSet
    p hp δ hδ.le (hZero n) (fun x i j => (hn x i j).le)).trans (hm m le_rfl)

/-- For the same cutoff fluctuation and actual P01 projection, the whole-space
Lp norm tends to zero and each projected coordinate derivative is bounded. -/
theorem localizedMetricProjection_finiteLp_norms
    (g : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (hg : ∀ n, SmoothCoordinateComponents (g n)) (hg₀ : SmoothCoordinateComponents g₀)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hConv : TendstoUniformlyOn g g₀ atTop (tsupport χ))
    (B : ℝ≥0) (hDeriv : ∀ n i j x, x ∈ tsupport χ →
      ‖fderiv ℝ (fun y => g n y i j - g₀ y i j) x‖ ≤ (B : ℝ))
    (p : ℝ) (hp : 1 < p) :
    let z := fun n => localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀
    Tendsto (fun n => projectionMatrixLpNorm p (projectionFullSchwartz (z n))) atTop (𝓝 0) ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, projectionGradientLpNorm p (projectionFullSchwartz (z n)) ≤ C := by
  let z := fun n => localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀
  let K := tsupport χ
  let V : ℝ≥0∞ := volume K ^ (1 / p)
  have hp₀ : 0 < p := zero_lt_one.trans hp
  have hV : V < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by positivity) hc.measure_lt_top.ne
  obtain ⟨L, hL, hSmall⟩ := localizedMetricSchwartz_uniform_inputs g g₀ hg hg₀
    χ hχ hc hConv B hDeriv
  have hz (n : ℕ) (i j : Index) : tsupport (z n i j : CoordinateSpace → ℂ) ⊆ K :=
    localizedMetricSchwartz_tsupport_subset (g n) g₀ χ hχ hc (hg n) hg₀ i j
  have hzZero (n : ℕ) (x : CoordinateSpace) (i j : Index) (hx : x ∉ K) :
      z n i j x = 0 := by
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hz n i j h))
  have hInput := tendsto_projectionMatrixLpNorm_zero_of_uniform z K hc p hp₀ hzZero hSmall
  obtain ⟨M, hM, hProj⟩ := exists_projectionFullSchwartz_finiteLp_bounds p hp
  have hInputScaled : Tendsto (fun n => M * projectionMatrixLpNorm p (z n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hInput (Or.inr hM.ne)
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hInputScaled
    (fun _ => zero_le _) (fun n => (hProj (z n)).1), ?_⟩
  have hD (n : ℕ) (b : Index) :
      projectionMatrixLpNorm p (projectionMatrixDerivative b (z n)) ≤ (L : ℝ≥0∞) * V := by
    have hBd (x : CoordinateSpace) (i j : Index) :
        ‖projectionMatrixDerivative b (z n) i j x‖ ≤ (L : ℝ) :=
      coordinateDerivative_norm_le (z n i j) L (hL n i j) b x
    have hZ (x : CoordinateSpace) (i j : Index) (hx : x ∉ K) :
        projectionMatrixDerivative b (z n) i j x = 0 :=
      coordinateDerivative_zero_outside (z n i j) K (hz n i j) b x hx
    simpa only [ENNReal.ofReal_coe_nnreal] using
      projectionMatrixLpNorm_le_of_support (projectionMatrixDerivative b (z n))
        K isClosed_closure.measurableSet p hp₀ (L : ℝ) L.coe_nonneg hZ hBd
  let C := M * ((L : ℝ≥0∞) * V)
  have hC : C < ⊤ := ENNReal.mul_lt_top hM (ENNReal.mul_lt_top ENNReal.coe_lt_top hV)
  have hp₁ : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  refine ⟨4 * C, ENNReal.mul_lt_top (by simp) hC, fun n => ?_⟩
  calc
    _ ≤ ∑ b, projectionMatrixLpNorm p (projectionMatrixDerivative b (projectionFullSchwartz (z n))) :=
      projectionGradientLpNorm_le_sum p hp₁ (projectionFullSchwartz (z n))
    _ ≤ ∑ _ : Index, C := Finset.sum_le_sum fun b _ =>
      ((hProj (z n)).2 b).trans (mul_le_mul_left' (hD n b) M)
    _ = _ := by simp [nsmul_eq_mul]

end Burnett.P01
