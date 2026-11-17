import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Burnett.Analysis.Cubic.Explicit
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Actual compact cutoffs and large spatial dilations for X03

A real smooth bump is constructed inside an arbitrary open time neighborhood
of zero intersected with cos(2t)>0. Its integral and its cos(2t)-weighted
integral are strictly positive, with compact support and actual integrability.
Two explicit spatial bumps on Euclidean R3 give a nonnegative positive-integral
cutoff and a larger plateau. A single constant bounds the sum of the true
first directional derivatives, by continuity and compactness; outside the
smaller support the derivative is actually zero. Dilation gives true Frechet
1/R scaling and the exact R3 Haar integral law, together with separate
integrability of the scaled smooth compact cutoffs for R nonzero.
These are constructed proof inputs, not supplied cutoff conclusion fields.
-/

noncomputable section
namespace Burnett.RotatingNullMoments.ScaledCutoffs
open Set Metric MeasureTheory
open scoped ContDiff Topology BigOperators

/-- A genuine compact smooth cutoff in any prescribed neighborhood of t=0. -/
theorem exists_time_cutoff (I : Set ℝ) (hI : IsOpen I) (h0 : (0 : ℝ) ∈ I) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ I ∩ {t | 0 < Real.cos (2*t)} ∧
      (∀ t, 0 ≤ χ t) ∧ (∫ t, χ t) > 0 ∧ (∫ t, χ t * Real.cos (2*t)) > 0 := by
  let U : Set ℝ := I ∩ {t | 0 < Real.cos (2*t)}
  have hU : IsOpen U := hI.inter (isOpen_lt continuous_const (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  have h0U : (0 : ℝ) ∈ U := ⟨h0, by norm_num⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  let b : ContDiffBump (0 : ℝ) := ⟨ε/4, ε/2, by positivity, by linarith⟩
  have hbU : tsupport (b : ℝ → ℝ) ⊆ U := by
    rw [b.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp [b]; linarith)).trans hεU
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hw : Continuous (fun t : ℝ => b t * Real.cos (2*t)) :=
    b.continuous.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hc : HasCompactSupport (fun t : ℝ => b t * Real.cos (2*t)) := b.hasCompactSupport.mul_right
  have hn : ∀ t : ℝ, 0 ≤ b t * Real.cos (2*t) := by
    intro t
    by_cases ht : t ∈ tsupport (b : ℝ → ℝ)
    · exact mul_nonneg b.nonneg (hbU ht).2.le
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  have hi : 0 < ∫ t : ℝ, b t * Real.cos (2*t) :=
    hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) hc hn (by simp [hb0])
  exact ⟨b, b.contDiff, b.hasCompactSupport, hbU, b.nonneg', b.integral_pos, hi⟩

abbrev Space := EuclideanSpace ℝ (Fin 3)

def spatialBump : ContDiffBump (0 : Space) := ⟨1, 2, by norm_num, by norm_num⟩
def majorantBump : ContDiffBump (0 : Space) := ⟨2, 3, by norm_num, by norm_num⟩

def directional (j : Fin 3) (f : Space → ℝ) (x : Space) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single j 1)

def derivativeSum (f : Space → ℝ) (x : Space) : ℝ := ∑ j, |directional j f x|

theorem continuous_derivativeSum (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) :
    Continuous (derivativeSum f) := by
  apply continuous_finset_sum
  intro j _
  exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).abs

/-- The larger actual bump is one wherever any derivative of the smaller one can live. -/
theorem majorant_one_on_support (x : Space) (hx : x ∈ tsupport (spatialBump : Space → ℝ)) :
    majorantBump x = 1 := by
  apply majorantBump.one_of_mem_closedBall
  simpa only [spatialBump.tsupport_eq] using hx

theorem derivativeSum_zero_outside (x : Space) (hx : x ∉ tsupport (spatialBump : Space → ℝ)) :
    derivativeSum spatialBump x = 0 := by
  unfold derivativeSum directional
  rw [fderiv_of_notMem_tsupport ℝ hx]
  simp

theorem exists_spatial_derivative_majorant : ∃ C : ℝ, 0 < C ∧
    ∀ x : Space, derivativeSum spatialBump x ≤ C * majorantBump x := by
  have hK : IsCompact (tsupport (spatialBump : Space → ℝ)) := spatialBump.hasCompactSupport
  have hb := hK.bddAbove_image (continuous_derivativeSum spatialBump spatialBump.contDiff).continuousOn
  obtain ⟨B, hB⟩ := hb
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  by_cases hx : x ∈ tsupport (spatialBump : Space → ℝ)
  · rw [majorant_one_on_support x hx, mul_one]
    exact (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  · rw [derivativeSum_zero_outside x hx]
    exact mul_nonneg (le_trans zero_le_one (le_max_right _ _)) majorantBump.nonneg

/-- Both spatial cutoffs and their derivative constant are constructed, not supplied fields. -/
theorem exists_spatial_cutoffs : ∃ (η θ : Space → ℝ) (C : ℝ),
    ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x) ∧ (∫ x, η x) > 0 ∧
    ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ (∀ x, 0 ≤ θ x) ∧ (∫ x, θ x) > 0 ∧
    0 < C ∧ ∀ x, derivativeSum η x ≤ C * θ x := by
  obtain ⟨C, hC, hbound⟩ := exists_spatial_derivative_majorant
  exact ⟨spatialBump, majorantBump, C, spatialBump.contDiff, spatialBump.hasCompactSupport,
    spatialBump.nonneg', spatialBump.integral_pos, majorantBump.contDiff, majorantBump.hasCompactSupport,
    majorantBump.nonneg', majorantBump.integral_pos, hC, hbound⟩

/-- The spatial cutoff at radius R, using the actual scalar dilation. -/
def scale (R : ℝ) (f : Space → ℝ) (x : Space) : ℝ := f (R⁻¹ • x)

theorem smooth_scale (R : ℝ) (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scale R f) := hf.comp (contDiff_const.smul contDiff_id)

theorem compactSupport_scale (R : ℝ) (hR : R ≠ 0) (f : Space → ℝ) (hf : HasCompactSupport f) :
    HasCompactSupport (scale R f) := hf.comp_smul (inv_ne_zero hR)

theorem integral_scale (R : ℝ) (hR : 0 ≤ R) (f : Space → ℝ) :
    (∫ x, scale R f x) = R^3 * ∫ x, f x := by
  simpa [scale, Space, smul_eq_mul] using
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure Space) f hR

/-- Real integrability of the scaled cutoffs, separate from the total-function integral formula. -/
theorem integrable_scale (R : ℝ) (hR : R ≠ 0) (f : Space → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Integrable (scale R f) :=
  (smooth_scale R f hf).continuous.integrable_of_hasCompactSupport (compactSupport_scale R hR f hc)

theorem directional_scale (R : ℝ) (f : Space → ℝ) (hf : Differentiable ℝ f)
    (j : Fin 3) (x : Space) :
    directional j (scale R f) x = R⁻¹ * directional j f (R⁻¹ • x) := by
  have hL : HasFDerivAt (fun x : Space => R⁻¹ • x)
      (R⁻¹ • ContinuousLinearMap.id ℝ Space) x :=
    (R⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt
  unfold directional scale
  have hd : HasFDerivAt (fun y : Space => f (R⁻¹ • y))
      ((fderiv ℝ f (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ Space)) x :=
    (hf _).hasFDerivAt.comp x hL
  rw [hd.fderiv]
  simp

theorem derivativeSum_scale (R : ℝ) (hR : 0 < R) (f : Space → ℝ) (hf : Differentiable ℝ f)
    (x : Space) : derivativeSum (scale R f) x = R⁻¹ * derivativeSum f (R⁻¹ • x) := by
  unfold derivativeSum
  simp_rw [directional_scale R f hf, abs_mul, abs_of_pos (inv_pos.mpr hR)]
  exact (Finset.mul_sum _ _ _).symm

theorem scaled_spatial_derivative_majorant : ∃ C : ℝ, 0 < C ∧
    ∀ (R : ℝ), 0 < R → ∀ x : Space,
      derivativeSum (scale R spatialBump) x ≤ (C/R) * scale R majorantBump x := by
  obtain ⟨C, hC, hbound⟩ := exists_spatial_derivative_majorant
  refine ⟨C, hC, ?_⟩
  intro R hR x
  rw [derivativeSum_scale R hR spatialBump ((spatialBump.contDiff (n := ⊤)).differentiable (by simp))]
  calc
    _ ≤ R⁻¹ * (C * majorantBump (R⁻¹ • x)) :=
      mul_le_mul_of_nonneg_left (hbound _) (inv_nonneg.mpr hR.le)
    _ = (C/R) * scale R majorantBump x := by unfold scale; ring

end Burnett.RotatingNullMoments.ScaledCutoffs
