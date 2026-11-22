import Burnett.Analysis.GaugeProjection.GaugeProjectionFourier
import Burnett.Algebra.HermitianScreen
import Mathlib.Data.Complex.BigOperators

set_option autoImplicit false
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.P01

open Matrix
open Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open scoped BigOperators Matrix

/-- The original projection on the homogeneous angular symbol. The fixed
infrared regularization of the actual multiplier is one at high frequency. -/
def principalGaugeProjection (ξ : E) (H : ComplexTensor2) : ComplexComponents :=
  let P := (directionProjection (fun i => ξ i)).map Complex.ofReal
  P * Matrix.of H * P

theorem regularizedComplexGaugeProjection_eq_principal (ξ : E) (H : ComplexTensor2)
    (hξ : 2 ≤ ‖ξ‖) :
    regularizedComplexGaugeProjection ξ (Matrix.of H) = principalGaugeProjection ξ H := by
  change (gaugeProjectionInfrared ‖ξ‖ : ℂ) • principalGaugeProjection ξ H = _
  rw [gaugeProjectionInfrared_one hξ, Complex.ofReal_one, one_smul]

private theorem principalGaugeProjection_re (ξ : E) (H : ComplexTensor2) :
    Matrix.of (tensorRe (principalGaugeProjection ξ H)) =
      euclideanGaugeProjection (fun i => ξ i) (Matrix.of (tensorRe H)) := by
  ext a b
  simp only [principalGaugeProjection, euclideanGaugeProjection, Matrix.of_apply, tensorRe,
    Matrix.mul_apply, Complex.re_sum, Complex.mul_re, Matrix.map_apply,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]

private theorem principalGaugeProjection_im (ξ : E) (H : ComplexTensor2) :
    Matrix.of (tensorIm (principalGaugeProjection ξ H)) =
      euclideanGaugeProjection (fun i => ξ i) (Matrix.of (tensorIm H)) := by
  ext a b
  simp only [principalGaugeProjection, euclideanGaugeProjection, Matrix.of_apply, tensorIm,
    Matrix.mul_apply, Complex.im_sum, Complex.mul_im, Matrix.map_apply,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, zero_add, add_zero]

/-- The change in a complex symmetric amplitude under the same projection is
a pure gauge amplitude. -/
theorem principalGaugeProjection_adds_pureGauge (ξ : E) (H : ComplexTensor2)
    (hH : IsSymmetricComplexTensor H) :
    ∃ v : ComplexCovector,
      (principalGaugeProjection ξ H : ComplexTensor2) = H + complexPureGauge (fun i => ξ i) v := by
  let x : Covector := fun i => ξ i
  let Hr := Matrix.of (tensorRe H)
  let Hi := Matrix.of (tensorIm H)
  have hHr : Hrᵀ = Hr := by
    ext a b
    exact congrArg Complex.re (hH b a)
  have hHi : Hiᵀ = Hi := by
    ext a b
    exact congrArg Complex.im (hH b a)
  let vr := euclideanGaugeRepresentative x Hr
  let vi := euclideanGaugeRepresentative x Hi
  refine ⟨fun a => -(Complex.mk (vr a) (vi a)), ?_⟩
  funext a b
  have hR := congrFun (congrFun (euclideanGaugeProjection_sub_eq x hHr) a) b
  have hI := congrFun (congrFun (euclideanGaugeProjection_sub_eq x hHi) a) b
  change Hr a b - euclideanGaugeProjection x Hr a b = x a * vr b + vr a * x b at hR
  change Hi a b - euclideanGaugeProjection x Hi a b = x a * vi b + vi a * x b at hI
  rw [← principalGaugeProjection_re ξ H] at hR
  rw [← principalGaugeProjection_im ξ H] at hI
  change (H a b).re - (principalGaugeProjection ξ H a b).re = _ at hR
  change (H a b).im - (principalGaugeProjection ξ H a b).im = _ at hI
  apply Complex.ext
  · simp only [Pi.add_apply, Complex.add_re, complexPureGauge, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, zero_mul, mul_zero, sub_zero]
    change _ = (H a b).re + (x a * (-vr b) + (-vr a) * x b)
    linarith only [hR]
  · simp only [Pi.add_apply, Complex.add_im, complexPureGauge, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_im, zero_mul, mul_zero, zero_add, add_zero]
    change _ = (H a b).im + (x a * (-vi b) + (-vi a) * x b)
    linarith only [hI]

/-- The noncharacteristic projected amplitude is zero because both real
components of the original amplitude are pure gauge. -/
theorem principalGaugeProjection_eq_zero_off_null (gInv : Tensor2) (ξ : E)
    (H : ComplexTensor2) (hξ : (fun i : Index => ξ i) ≠ 0)
    (hs : symbolNorm gInv (fun i => ξ i) ≠ 0)
    (hH : ∀ a b, complexRicciSymbol gInv (fun i => ξ i) H a b = 0) :
    principalGaugeProjection ξ H = 0 := by
  let x : Covector := fun i => ξ i
  obtain ⟨hr, hi⟩ := (complexRicci_kernel_iff gInv x H).1 hH
  have hR : Matrix.of (tensorRe H) = gaugeAmplitude x (kernelGaugeVector gInv x (tensorRe H)) := by
    ext a b
    have h := congrFun (congrFun (kernel_eq_pureGauge gInv x (tensorRe H) hs hr) a) b
    exact h
  have hI : Matrix.of (tensorIm H) = gaugeAmplitude x (kernelGaugeVector gInv x (tensorIm H)) := by
    ext a b
    have h := congrFun (congrFun (kernel_eq_pureGauge gInv x (tensorIm H) hs hi) a) b
    exact h
  have hzR := principalGaugeProjection_re ξ H
  have hzI := principalGaugeProjection_im ξ H
  rw [hR, euclideanGaugeProjection_kills_gauge hξ] at hzR
  rw [hI, euclideanGaugeProjection_kills_gauge hξ] at hzI
  ext a b
  apply Complex.ext
  · exact congrFun (congrFun hzR a) b
  · exact congrFun (congrFun hzI a) b

theorem principalGaugeProjection_ricci_kernel (gInv : Tensor2) (ξ : E) (H : ComplexTensor2)
    (hg : IsSymmetricTensor gInv) (hH : IsSymmetricComplexTensor H)
    (hK : ∀ a b, complexRicciSymbol gInv (fun i => ξ i) H a b = 0) :
    ∀ a b, complexRicciSymbol gInv (fun i => ξ i) (principalGaugeProjection ξ H) a b = 0 := by
  obtain ⟨v, hv⟩ := principalGaugeProjection_adds_pureGauge ξ H hH
  intro a b
  rw [hv, complexRicciSymbol_add, hK, complexRicciSymbol_pureGauge_eq_zero _ _ _ hg, add_zero]

/-- The projected null amplitude satisfies the Lorenz contraction equation. -/
theorem principalGaugeProjection_null_contracted (gInv : Tensor2) (ξ : E) (H : ComplexTensor2)
    (hg : IsSymmetricTensor gInv) (hH : IsSymmetricComplexTensor H)
    (hξ : (fun i : Index => ξ i) ≠ 0) (hs : symbolNorm gInv (fun i => ξ i) = 0)
    (hK : ∀ a b, complexRicciSymbol gInv (fun i => ξ i) H a b = 0) (b : Index) :
    complexContracted gInv (fun i => ξ i) (principalGaugeProjection ξ H) b =
      complexMetricTrace gInv (principalGaugeProjection ξ H) * ((ξ b / 2 : ℝ) : ℂ) := by
  let x : Covector := fun i => ξ i
  let P := principalGaugeProjection ξ H
  obtain ⟨hr, hi⟩ := (complexRicci_kernel_iff gInv x P).1
    (principalGaugeProjection_ricci_kernel gInv ξ H hg hH hK)
  apply Complex.ext
  · simp only [complexContracted_re, complexMetricTrace_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [(null_kernel_iff_contracted gInv x (tensorRe P) hξ hs).1 hr b]
    change _ = metricTrace gInv (tensorRe P) * (x b / 2)
    ring
  · simp only [complexContracted_im, complexMetricTrace_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
    rw [(null_kernel_iff_contracted gInv x (tensorIm P) hξ hs).1 hi b]
    change _ = metricTrace gInv (tensorIm P) * (x b / 2)
    ring

/-- The physical contraction on the same null kernel is unchanged in both
slots of the original Hermitian form. -/
theorem principalGaugeProjection_preserves_hermitianPhysicalPairing
    (gInv : Tensor2) (ξ : E) (H K : ComplexTensor2)
    (hg : IsSymmetricTensor gInv) (hH : IsSymmetricComplexTensor H) (hK : IsSymmetricComplexTensor K)
    (hξ : (fun i : Index => ξ i) ≠ 0) (hs : symbolNorm gInv (fun i => ξ i) = 0)
    (hHK : ∀ a b, complexRicciSymbol gInv (fun i => ξ i) H a b = 0)
    (hKK : ∀ a b, complexRicciSymbol gInv (fun i => ξ i) K a b = 0) :
    hermitianPhysicalPairing gInv (principalGaugeProjection ξ H) (principalGaugeProjection ξ K) =
      hermitianPhysicalPairing gInv H K := by
  obtain ⟨v, hv⟩ := principalGaugeProjection_adds_pureGauge ξ H hH
  obtain ⟨w, hw⟩ := principalGaugeProjection_adds_pureGauge ξ K hK
  rw [hv, hw]
  exact hermitianPhysicalPairing_add_pureGauge_both _ _ _ _ v w hg hH hK hξ hs hHK hKK

end Burnett.P01
