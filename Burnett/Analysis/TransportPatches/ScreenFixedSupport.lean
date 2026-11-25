import Burnett.Analysis.TransportPatches.ProjectedNullScreenSupport
import Burnett.Analysis.FrozenScreen.Invertibility
import Burnett.Analysis.FrozenScreen.Constraints
import Burnett.Analysis.FrozenScreen.Symbol
import Burnett.Analysis.Microlocal.AuxiliaryCovectorScale

/-! The actual V06 screen fixes the projected complex Ricci kernel on the null cone. -/

set_option autoImplicit false
set_option maxHeartbeats 5400000

noncomputable section

namespace Burnett.C02

open Matrix Burnett.RicciSymbol Burnett.V06 TensorFrame
open Burnett.P01 (principalGaugeProjection)
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.FixedChartGeometricDensity (symbolNorm_rescale)
open scoped BigOperators Matrix

/-- The complexification of the true V06 screen symbol. -/
def complexFrozenScreen (B : ScreenMatrix) (H : ComplexTensor2) (q : Covector) : ComplexTensor2 :=
  fun i j => ⟨frozenScreenSymbol B (tensorRe H) q i j, frozenScreenSymbol B (tensorIm H) q i j⟩

private theorem real_mulVec_zero (H : ComplexTensor2) (v : Covector)
    (h : Matrix.of H *ᵥ (fun i => (v i : ℂ)) = 0) :
    (tensorRe H : ScreenMatrix) *ᵥ v = 0 := by
  funext i
  have hi := congrArg Complex.re (congrFun h i)
  simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Pi.zero_apply, Complex.zero_re, tensorRe] using hi

private theorem imag_mulVec_zero (H : ComplexTensor2) (v : Covector)
    (h : Matrix.of H *ᵥ (fun i => (v i : ℂ)) = 0) :
    (tensorIm H : ScreenMatrix) *ᵥ v = 0 := by
  funext i
  have hi := congrArg Complex.im (congrFun h i)
  simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_add, Pi.zero_apply, Complex.zero_im, tensorIm] using hi

private theorem matrixTrace_eq_metricTrace (B R : ScreenMatrix) (hR : Rᵀ = R) :
    Matrix.trace (B * R) = metricTrace B R := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, metricTrace]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show R j i = R i j from congrFun (congrFun hR i) j]

theorem complexFrozenScreen_fixes_projected_nullRicciKernel
    (B : ScreenMatrix) (frame : LorentzFrame B) (hB : IsUnit B.det)
    (ξ : E) (K : ComplexTensor2) (hS : IsSymmetricComplexTensor K)
    (hξ : (fun i : Index => ξ i) ≠ 0) (hNull : symbolNorm B (fun i => ξ i) = 0)
    (hR : ∀ a b, complexRicciSymbol B (fun i => ξ i) K a b = 0) :
    let q : Covector := fun i => ξ i
    let H : ComplexTensor2 := principalGaugeProjection ξ K
    complexFrozenScreen B H q = H := by
  intro q H
  have hBS : IsSymmetricTensor B := LorentzPhysical.metric_symmetric B frame
  obtain ⟨hH, hE, hT, hTrace⟩ := screen_of_projected_nullRicciKernel B ξ K hBS hS hξ hNull hR
  change Matrix.of H *ᵥ (fun i => (q i : ℂ)) = 0 at hE
  change Matrix.of H *ᵥ (fun i => (((B *ᵥ q) i : ℝ) : ℂ)) = 0 at hT
  let e := screenUnitCovector q
  let c := (Real.sqrt (q ⬝ᵥ q))⁻¹
  have heq : e = c • q := rfl
  have he : e ⬝ᵥ e = 1 := screenUnitCovector_unit q hξ
  have he₀ : e ≠ 0 := by
    intro hz
    rw [hz, zero_dotProduct] at he
    norm_num at he
  have hNullE : symbolNorm B e = 0 := by
    rw [heq]
    change symbolNorm B (fun i => c * q i) = 0
    rw [symbolNorm_rescale, hNull, mul_zero]
  have hw := screenSecondDirection_ne_zero_on_null B e hB he₀ hNullE
  have hA := screenMetricExtension_isUnit_on_null B frame hB e he hNullE
  have hScaled (R : ScreenMatrix) (hE₀ : R *ᵥ q = 0) (hT₀ : R *ᵥ (B *ᵥ q) = 0) :
      R *ᵥ e = 0 ∧ R *ᵥ (B *ᵥ e) = 0 := by
    simp only [heq, mulVec_smul, hE₀, hT₀, smul_zero, and_self]
  let HR : ScreenMatrix := tensorRe H
  let HI : ScreenMatrix := tensorIm H
  have hHr : HRᵀ = HR := by
    ext i j
    exact congrArg Complex.re (hH j i)
  have hHi : HIᵀ = HI := by
    ext i j
    exact congrArg Complex.im (hH j i)
  change complexMetricTrace B H = 0 at hTrace
  have hReTrace : Matrix.trace (B * HR) = 0 := by
    rw [matrixTrace_eq_metricTrace B HR hHr]
    change metricTrace B (tensorRe H) = 0
    rw [← complexMetricTrace_re, hTrace, Complex.zero_re]
  have hImTrace : Matrix.trace (B * HI) = 0 := by
    rw [matrixTrace_eq_metricTrace B HI hHi]
    change metricTrace B (tensorIm H) = 0
    rw [← complexMetricTrace_im, hTrace, Complex.zero_im]
  have hRe := hScaled HR (real_mulVec_zero H q hE) (real_mulVec_zero H (B *ᵥ q) hT)
  have hIm := hScaled HI (imag_mulVec_zero H q hE) (imag_mulVec_zero H (B *ᵥ q) hT)
  have hReFix : frozenScreenSymbol B HR q = HR :=
    (frozenScreenProjection_fixed_iff B HR hHr e he hw hA).2 ⟨hRe.1, hRe.2, hReTrace⟩
  have hImFix : frozenScreenSymbol B HI q = HI :=
    (frozenScreenProjection_fixed_iff B HI hHi e he hw hA).2 ⟨hIm.1, hIm.2, hImTrace⟩
  funext i j
  apply Complex.ext
  · exact congrFun (congrFun hReFix i) j
  · exact congrFun (congrFun hImFix i) j

end Burnett.C02
