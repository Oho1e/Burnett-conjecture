import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualThinTransversality
import Burnett.Analysis.FrozenScreen.Constraints
import Burnett.Analysis.FrozenScreen.Phase
import Burnett.Analysis.GaugeProjection.GaugeProjectionFourier

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 14200000

noncomputable section

namespace Burnett.C02

open Matrix Burnett.RicciSymbol Burnett.V06 Burnett.A02.FrequencySplit
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix projectionFullSchwartz
  projectionFullSchwartz_radianFourier regularizedComplexGaugeProjection gaugeProjectionInfrared_zero)
open Burnett.Microlocal.PhysicalDensity (OrderedPair tensorOfVector)
open Burnett.Analysis.ProjectiveNullCaps (thinConeProfile thinConeProfile_nonzero_cone)
open scoped Matrix

open private complexDirectionProjection_transpose from Burnett.Analysis.GaugeProjection.GaugeProjectionFourier

private theorem wardThin_realProjection_symm (m H : ScreenMatrix) (q : Covector)
    (hm : mᵀ = m) (hH : Hᵀ = H) (wi wo : ℝ) :
    (globalAngularScreenSymbol wi wo m H q)ᵀ = globalAngularScreenSymbol wi wo m H q := by
  rw [globalAngularScreenSymbol, transpose_smul]
  change _ • (frozenScreenProjection m (screenDirectionProjection m (screenUnitCovector q)) H)ᵀ = _
  rw [frozenScreenProjection_symmetric m H (screenUnitCovector q) hm hH]
  rfl

private theorem wardProjectedSpectrum_symm (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a) (ξ : E) :
    IsSymmetricComplexTensor (fun a b => radianFourier (projectionFullSchwartz z a b) ξ) := by
  let input : ComplexComponents := Matrix.of (fun a b => radianFourier (z a b) ξ)
  have hIn : inputᵀ = input := by
    ext a b
    change radianFourier (z b a) ξ = radianFourier (z a b) ξ
    rw [hz b a]
  have hP : (regularizedComplexGaugeProjection ξ input)ᵀ = regularizedComplexGaugeProjection ξ input := by
    simp only [regularizedComplexGaugeProjection, transpose_smul, transpose_mul,
      complexDirectionProjection_transpose, hIn, mul_assoc]
  intro a b
  change radianFourier (projectionFullSchwartz z a b) ξ = radianFourier (projectionFullSchwartz z b a) ξ
  rw [projectionFullSchwartz_radianFourier, projectionFullSchwartz_radianFourier]
  exact (congrFun (congrFun hP a) b).symm

/-- The thin multiplier is the original scalar cutoff times the original
wide screen acting on the actual infrared-regularized Fourier amplitude. -/
theorem wardActualThinSpectrum_eq_cutoff_wide (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) (ξ : E) :
    wardActualThinSpectrum m wi wo hm hη i o z ξ =
      (thinConeProfile m η i o ξ : ℂ) • complexWideScreen wi wo m
        (fun a b => radianFourier (projectionFullSchwartz z a b) ξ) (fun a => ξ a) := by
  let f (j : OrderedPair) := radianFourier (projectionFullSchwartz z j.1 j.2) ξ
  have hWide := tensorOfVector_actualWideScreenOrdered wi wo m (fun a => ξ a) f
  change _ = _ • complexWideScreen wi wo m (tensorOfVector f) _
  rw [← hWide]
  funext a b
  rw [wardActualThinSpectrum_eq_sum m wi wo hm hη i o z ξ (a,b)]
  change (∑ j : OrderedPair,
    ((thinConeProfile m η i o ξ *
      (actualWideScreenOrdered wi wo m (fun a => ξ a) (a,b) j).re : ℝ) : ℂ) * f j) =
    (thinConeProfile m η i o ξ : ℂ) * ((actualWideScreenOrdered wi wo m (fun a => ξ a)) *ᵥ f) (a,b)
  simp only [actualWideScreenOrdered, Complex.ofReal_re, Complex.ofReal_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- The actual thin Fourier amplitude retains the symmetry of the original
localized perturbation. -/
theorem wardActualThinSpectrum_symmetric (m : Tensor2) (hSym : (Matrix.of m)ᵀ = Matrix.of m)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a) (ξ : E) :
    IsSymmetricComplexTensor (wardActualThinSpectrum m wi wo hm hη i o z ξ) := by
  rw [wardActualThinSpectrum_eq_cutoff_wide]
  let input : ComplexTensor2 := fun a b => radianFourier (projectionFullSchwartz z a b) ξ
  have hIn := wardProjectedSpectrum_symm z hz ξ
  have hRe : (Matrix.of (tensorRe input))ᵀ = Matrix.of (tensorRe input) := by
    ext a b
    exact congrArg Complex.re (hIn b a)
  have hIm : (Matrix.of (tensorIm input))ᵀ = Matrix.of (tensorIm input) := by
    ext a b
    exact congrArg Complex.im (hIn b a)
  intro a b
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Complex.ext
  · exact (congrFun (congrFun (wardThin_realProjection_symm m (tensorRe input) (fun d => ξ d) hSym hRe wi wo) a) b).symm
  · exact (congrFun (congrFun (wardThin_realProjection_symm m (tensorIm input) (fun d => ξ d) hSym hIm wi wo) a) b).symm

private theorem wardRealMetricTrace_eq_trace_mul (m H : ScreenMatrix) (hSym : mᵀ = m) :
    metricTrace m H = Matrix.trace (m * H) := by
  simp only [metricTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [show m b a = m a b from congrFun (congrFun hSym a) b]

private theorem wardGlobalScreen_trace_zero (m H : ScreenMatrix) (hSym : mᵀ = m)
    (wi wo : ℝ) (q : Covector) (hq : q ≠ 0)
    (hw : screenSecondDirection m (screenUnitCovector q) ≠ 0)
    (hA : IsUnit (screenMetricExtension m (screenDirectionProjection m (screenUnitCovector q))).det) :
    metricTrace m (globalAngularScreenSymbol wi wo m H q) = 0 := by
  let e := screenUnitCovector q
  have he : e ⬝ᵥ e = 1 := screenUnitCovector_unit q hq
  have hRange := frozenScreenProjection_range m (screenDirectionProjection m e) H
    (screenDirectionProjection_idempotent m e he hw) (screenDirectionProjection_trace m e he hw) hA
  rw [wardRealMetricTrace_eq_trace_mul m _ hSym, globalAngularScreenSymbol, mul_smul_comm, Matrix.trace_smul]
  change angularScreenCutoff wi wo (symbolNorm m e) *
    Matrix.trace (m * frozenScreenProjection m (screenDirectionProjection m e) H) = 0
  rw [hRange.2.2, mul_zero]

private theorem wardActualThinSpectrum_origin (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) :
    wardActualThinSpectrum m wi wo hm hη i o z 0 = 0 := by
  funext a b
  rw [wardActualThinSpectrum_eq_sum m wi wo hm hη i o z 0 (a,b)]
  apply Finset.sum_eq_zero
  intro j _
  rw [projectionFullSchwartz_radianFourier]
  simp only [regularizedComplexGaugeProjection, norm_zero, gaugeProjectionInfrared_zero (by norm_num : (0 : ℝ) ≤ 1),
    Complex.ofReal_zero, zero_smul, Matrix.zero_apply, mul_zero]

/-- Trace-free physicality of the exact thin field for an angular radius
chosen inside the genuine Lorentz screen invertibility window. -/
theorem wardActualThinSpectrum_trace_free (m : Tensor2) (hSym : (Matrix.of m)ᵀ = Matrix.of m)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm m e| < ε →
      screenSecondDirection m e ≠ 0 ∧ IsUnit (screenMetricExtension m (screenDirectionProjection m e)).det)
    (z : ProjectionSchwartzMatrix) (ξ : E) :
    complexMetricTrace m (wardActualThinSpectrum m wi wo hm hη i o z ξ) = 0 := by
  by_cases hξ : ξ = 0
  · subst ξ
    rw [wardActualThinSpectrum_origin]
    simp [complexMetricTrace]
  rw [wardActualThinSpectrum_eq_cutoff_wide, complexMetricTrace_smul]
  by_cases hχ : thinConeProfile m η i o ξ = 0
  · simp only [hχ, Complex.ofReal_zero, zero_mul]
  suffices h : complexMetricTrace m (complexWideScreen wi wo m
      (fun a b => radianFourier (projectionFullSchwartz z a b) ξ) (fun a => ξ a)) = 0 by rw [h, mul_zero]
  let q : Covector := fun a => ξ a
  have hq : q ≠ 0 := fun hz => hξ (by ext a; exact congrFun hz a)
  have hPhase : |symbolNorm m (screenUnitCovector q)| < ε := by
    have hCone := thinConeProfile_nonzero_cone hη hi hio hξ hχ
    have hDen := pow_pos (norm_pos_iff.mpr hξ) 2
    have hNormalized : |normalizedFrozenPhase m ξ| < o * η := by
      rw [normalizedFrozenPhase, abs_div, abs_of_pos hDen]
      exact (div_lt_iff₀ hDen).mpr hCone
    rw [normalizedFrozenPhase_eq_unitPhase] at hNormalized
    exact hNormalized.trans_le hSmall
  obtain ⟨hSecond, hA⟩ := hWindow (screenUnitCovector q) (screenUnitCovector_unit q hq) hPhase
  apply Complex.ext
  · rw [complexMetricTrace_re, Complex.zero_re]
    exact wardGlobalScreen_trace_zero m _ hSym wi wo q hq hSecond hA
  · rw [complexMetricTrace_im, Complex.zero_im]
    exact wardGlobalScreen_trace_zero m _ hSym wi wo q hq hSecond hA

/-- The physical slots of the actual frozen Einstein density are the true
signed quadratic phase times the same twice-raised thin Fourier tensor. -/
theorem wardActualThinSpectrum_einsteinPhase (m : Tensor2) (hSym : (Matrix.of m)ᵀ = Matrix.of m)
    (w wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm m e| < ε →
      screenSecondDirection m e ≠ 0 ∧ IsUnit (screenMetricExtension m (screenDirectionProjection m e)).det)
    (z : ProjectionSchwartzMatrix) (ξ : E) (a b : Index) :
    let H := wardActualThinSpectrum m wi wo hm hη i o z ξ
    let q : Covector := fun j => ξ j
    einsteinDensitySymbol m w q H a b =
      (w : ℂ) * (symbolNorm m q : ℂ) / 2 * raiseBoth m H a b := by
  intro H q
  have ht := wardActualThinSpectrum_trace_free m hSym wi wo hm hη i o ε hi hio hSmall hWindow z ξ
  have hq (j : Index) : complexContracted m q H j = 0 := by
    have h := (wardActualThinSpectrum_metricTransverse m wi wo hm hη i o z ξ).2 j
    simpa only [complexContracted, raiseCovector, Matrix.mulVec, dotProduct, H, q, mul_comm] using h
  exact (einsteinDensitySymbol_screen_phase m w q H ht hq a b).1

end Burnett.C02
