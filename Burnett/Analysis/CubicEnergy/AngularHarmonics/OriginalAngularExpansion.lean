import Burnett.Analysis.CubicEnergy.AngularHarmonics.SmoothAngularCoefficient
import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicActualMultiplier
import Burnett.Analysis.CubicEnergy.AngularHarmonics.HarmonicOperatorSum
import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicPointEvaluation
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.LowCartesianSymbol

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A07

open Burnett.A06 Burnett.A02.FrequencySplit MeasureTheory Metric Set
open scoped ContDiff ENNReal

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

def sphereEvaluationConstant : ℝ := Real.sqrt ((roundSphere3Measure.real univ)⁻¹)

theorem norm_roundSphereHarmonic_le (i : SphereHarmonicIndex) :
    ‖sphereHarmonicFamily i‖ ≤ sphereEvaluationConstant * ((i.1 : ℝ) + 1) := by
  apply (ContinuousMap.norm_le _ (by unfold sphereEvaluationConstant; positivity)).2
  intro x
  have h := norm_sphereHarmonicValue_le i.1 (sphereHarmonicPolynomialBasis i.1 i.2) x
  change ‖sphereHarmonicFamily i x‖ ≤
    Real.sqrt ((((i.1 + 1)^2 : ℕ) : ℝ) / roundSphere3Measure.real univ) * ‖sphereHarmonicFamilyLp i‖ at h
  rw [sphereHarmonicFamilyLp_orthonormal.norm_eq_one, mul_one] at h
  refine h.trans_eq ?_
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, sphereEvaluationConstant]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  exact mul_comm _ _

private theorem realHarmonicExpansion_at (f : C(RoundSphere3, ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hcoef : ∀ i : SphereHarmonicIndex,
      ‖∫ x, f x * sphereHarmonicFamily i x ∂roundSphere3Measure‖ ≤ M / ((i.1 : ℝ) + 1)^12)
    (x : RoundSphere3) :
    HasSum (fun i : SphereHarmonicIndex =>
      (∫ y, f y * sphereHarmonicFamily i y ∂roundSphere3Measure) * sphereHarmonicFamily i x) (f x) := by
  let term (i : SphereHarmonicIndex) :=
    (∫ y, f y * sphereHarmonicFamily i y ∂roundSphere3Measure) • sphereHarmonicFamily i
  let A := M * sphereEvaluationConstant
  have hA : 0 ≤ A := mul_nonneg hM (Real.sqrt_nonneg _)
  have hTerm (i : SphereHarmonicIndex) : ‖term i‖ ≤ A / ((i.1 : ℝ) + 1)^5 := by
    have h1 : 1 ≤ (i.1 : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hp : (0 : ℝ) < ((i.1 : ℝ) + 1)^5 := by positivity
    apply (le_div_iff₀ hp).2
    dsimp [term]
    rw [norm_smul]
    calc
      _ ≤ M / ((i.1 : ℝ) + 1)^12 * (sphereEvaluationConstant * ((i.1 : ℝ) + 1)) *
          ((i.1 : ℝ) + 1)^5 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hcoef i) (norm_roundSphereHarmonic_le i) (norm_nonneg _)
            (div_nonneg hM (by positivity))) hp.le
      _ = A * (((i.1 : ℝ) + 1)^6 / ((i.1 : ℝ) + 1)^12) := by dsimp [A]; ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one (by positivity)).mpr (pow_le_pow_right₀ h1 (by norm_num))) hA
      _ = A := mul_one _
  have hUniform : HasSum term f := by
    apply ContinuousMap.hasSum_of_hasSum_Lp (𝕜 := ℝ) (p := 2) (μ := roundSphere3Measure)
      (harmonic_series_estimate term hA hTerm).summable
    simpa only [Function.comp_apply, term, map_smul, sphereHarmonicFamilyLp]
      using roundSphereHarmonicSeries_hasSum f
  have hAt := (ContinuousMap.evalCLM ℝ x).hasSum hUniform
  simpa only [Function.comp_apply, term, ContinuousMap.evalCLM_apply,
    ContinuousMap.smul_apply, smul_eq_mul] using hAt

/-- The same complex coefficient integrals recover the original angular
slice at every point of the actual round sphere. -/
theorem jointSphereHarmonicCoefficientComplex_hasSum_at {F : Joint × RotationSpace → ℂ}
    {p : Joint} (hF : Continuous (fun x : RoundSphere3 => F (p,x)))
    {M : ℝ} (hM : 0 ≤ M)
    (hcoef : ∀ i : SphereHarmonicIndex, ‖jointSphereHarmonicCoefficientComplex F i p‖ ≤
      M / ((i.1 : ℝ) + 1)^12) (x : RoundSphere3) :
    HasSum (fun i : SphereHarmonicIndex =>
      jointSphereHarmonicCoefficientComplex F i p * (sphereHarmonicFamily i x : ℂ)) (F (p,x)) := by
  let fr : C(RoundSphere3, ℝ) := ⟨fun y => (F (p,y)).re, Complex.continuous_re.comp hF⟩
  let fi : C(RoundSphere3, ℝ) := ⟨fun y => (F (p,y)).im, Complex.continuous_im.comp hF⟩
  let c := fun i => jointSphereHarmonicCoefficientComplex F i p
  have hg (i : SphereHarmonicIndex) : Integrable (fun y : RoundSphere3 =>
      F (p,y) * (sphereHarmonicFamily i y : ℂ)) roundSphere3Measure :=
    (hF.mul (Complex.continuous_ofReal.comp (sphereHarmonicFamily i).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr (i : SphereHarmonicIndex) : (c i).re = ∫ y, fr y * sphereHarmonicFamily i y ∂roundSphere3Measure := by
    simpa [c, fr, jointSphereHarmonicCoefficientComplex, Function.comp_apply, Complex.mul_re]
      using (Complex.reCLM.integral_comp_comm (hg i)).symm
  have hi (i : SphereHarmonicIndex) : (c i).im = ∫ y, fi y * sphereHarmonicFamily i y ∂roundSphere3Measure := by
    simpa [c, fi, jointSphereHarmonicCoefficientComplex, Function.comp_apply, Complex.mul_im]
      using (Complex.imCLM.integral_comp_comm (hg i)).symm
  have reSum := realHarmonicExpansion_at fr hM
    (fun i => by rw [← hr i, Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hcoef i)) x
  have imSum := realHarmonicExpansion_at fi hM
    (fun i => by rw [← hi i, Real.norm_eq_abs]; exact (Complex.abs_im_le_norm _).trans (hcoef i)) x
  have h := (Complex.ofRealCLM.hasSum reSum).add
    ((Complex.I • Complex.ofRealCLM : ℝ →L[ℝ] ℂ).hasSum imSum)
  convert h using 1
  · funext i
    simp only [ContinuousLinearMap.smul_apply,
      Complex.ofRealCLM_apply, Complex.ofReal_mul, smul_eq_mul, ← hr i, ← hi i]
    have hc : (↑(c i).re : ℂ) + Complex.I * (c i).im = c i := by
      rw [mul_comm Complex.I, Complex.re_add_im]
    change c i * (sphereHarmonicFamily i x : ℂ) = _
    conv_lhs => rw [← hc]
    ring
  · change F (p,↑x) = (↑(F (p,↑x)).re : ℂ) + Complex.I * (F (p,↑x)).im
    rw [mul_comm Complex.I, Complex.re_add_im]

/-- The actual regularized low/high symbol before angular expansion. -/
def originalRegularizedAngularSymbol (η χ : ℝ → ℝ) (F : Joint × RotationSpace → ℂ) (x : Joint) : ℂ :=
  regularizedLowCartesianSymbol η χ (fun z => F (z, roundSphereRadialNormalize x.1)) x

/-- At each nonzero low frequency the original symbol equals its angular sum,
with the same cutoffs and independent variables on each mode. -/
theorem originalRegularizedAngularSymbol_hasSum
    (η χ : ℝ → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hcut : ∀ s ≥ ρ^2, χ s = 0)
    {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}
    (hF : ContinuousOn F W)
    (hW : (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : RotationSpace) 1 ⊆ W)
    {M : ℝ} (hM : 0 ≤ M)
    (hcoef : ∀ i : SphereHarmonicIndex, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1,
      ‖jointSphereHarmonicCoefficientComplex F i z‖ ≤ M / ((i.1 : ℝ) + 1)^12)
    (x : Joint) (hx : x.1 ≠ 0) :
    HasSum (fun i : SphereHarmonicIndex => (sphereHarmonicMultiplierSymbol i.1 i.2 x.1 : ℂ) *
      regularizedLowCartesianSymbol η χ (jointSphereHarmonicCoefficientComplex F i) x)
      (originalRegularizedAngularSymbol η χ F x) := by
  let z := normalizedHighPair x
  let a := η ‖x.2‖ * ‖x.2‖ * χ (‖z.1‖^2)
  have hscale (c : Joint → ℂ) : regularizedLowCartesianSymbol η χ c x = a • c z := by
    simp only [regularizedLowCartesianSymbol, lowCartesianSymbol, smul_smul, a, z, mul_assoc]
  by_cases ha : a = 0
  · simpa only [originalRegularizedAngularSymbol, hscale, ha, zero_smul, mul_zero]
      using (hasSum_zero : HasSum (fun _ : SphereHarmonicIndex => (0 : ℂ)) 0)
  have hq : x.2 ≠ 0 := by
    intro h
    apply ha
    simp [a, h]
  have hχ : χ (‖z.1‖^2) ≠ 0 := by
    intro h
    apply ha
    simp [a, h]
  have haz : ‖z.1‖ ≤ ρ := by
    by_contra! h
    exact hχ (hcut _ (pow_le_pow_left₀ hρ h.le 2))
  have hz : z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 :=
    ⟨mem_closedBall_zero_iff.mpr haz, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hq)⟩
  have hcont : Continuous (fun d : RoundSphere3 => F (z,d)) :=
    hF.comp_continuous (continuous_const.prodMk continuous_subtype_val) (fun d => hW ⟨hz,d.property⟩)
  let direction : RoundSphere3 := ⟨roundSphereRadialNormalize x.1,
    mem_sphere_zero_iff_norm.mpr (roundSphereRadialNormalize_norm hx)⟩
  have hY (i : SphereHarmonicIndex) :
      (sphereHarmonicMultiplierSymbol i.1 i.2 x.1 : ℂ) = (sphereHarmonicFamily i direction : ℂ) :=
    congrArg Complex.ofReal (sphereHarmonicMultiplierSymbol_eq i.1 i.2 hx)
  have hSum := ((a • ContinuousLinearMap.id ℝ ℂ) : ℂ →L[ℝ] ℂ).hasSum
    (jointSphereHarmonicCoefficientComplex_hasSum_at hcont hM (fun i => hcoef i z hz) direction)
  convert hSum using 1
  · funext i
    rw [hY, hscale]
    change (sphereHarmonicFamily i direction : ℂ) * (a • jointSphereHarmonicCoefficientComplex F i z) =
      a • (jointSphereHarmonicCoefficientComplex F i z * (sphereHarmonicFamily i direction : ℂ))
    simp only [Complex.real_smul]
    ring
  · exact hscale _

end Burnett.A07
