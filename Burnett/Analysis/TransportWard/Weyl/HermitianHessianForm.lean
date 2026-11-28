import Burnett.Analysis.FrozenScreen.Phase
import Burnett.Algebra.HermitianScreen

/-! Exact mixed Hermitian contraction of the weighted Einstein principal symbol. -/

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V02

open Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol (Mat inverseMatrix metricDensity)
open Burnett.V06 (einsteinDensitySymbol raiseBoth)
open scoped BigOperators ComplexConjugate

/-- Lowered de Donder covector of one complex amplitude. -/
def gaugeCovector (B : Tensor2) (ξ : Covector) (k : ComplexTensor2) (b : Index) : ℂ :=
  complexContracted B ξ k b - complexMetricTrace B k * (ξ b : ℂ) / 2

private def realGaugeCovector (B : Tensor2) (ξ : Covector) (k : Tensor2) (b : Index) : ℝ :=
  contracted B ξ k b - metricTrace B k * ξ b / 2

def raiseComplexCovector (B : Tensor2) (v : ComplexCovector) (i : Index) : ℂ :=
  ∑ j, (B i j : ℂ) * v j

/-- The inverse-metric pairing on lowered gauge covectors. -/
def gaugeHermitianPairing (B : Tensor2) (v z : ComplexCovector) : ℂ :=
  ∑ i, raiseComplexCovector B v i * conj (z i)

/-- The paper's quarter-normalized physical form. -/
def physicalForm (B : Tensor2) (k l : ComplexTensor2) : ℂ :=
  hermitianPhysicalPairing B k l / 4

/-- Ordered contraction with the actual density-weighted raised symbol. -/
def hessianPairing (B : Tensor2) (w : ℝ) (ξ : Covector) (k l : ComplexTensor2) : ℂ :=
  ∑ i, ∑ j, einsteinDensitySymbol B w ξ k i j * conj (l i j)

private theorem iteratedSum_exchange_pairs (f : Index → Index → Index → Index → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm

private theorem raiseBoth_ordered_pairing (B : Tensor2) (hB : IsSymmetricTensor B)
    (k l : ComplexTensor2) :
    (∑ a, ∑ b, raiseBoth B k a b * conj (l a b)) =
      ∑ c, ∑ d, ∑ a, ∑ b, (B c a : ℂ) * B d b * k c d * conj (l a b) := by
  simp only [raiseBoth, complexRaiseSecond, Finset.mul_sum, Finset.sum_mul]
  rw [iteratedSum_exchange_pairs]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hB a c, hB b d]
  ring

private theorem trace_ordered_pairing (B : Tensor2) (t : ℂ) (l : ComplexTensor2) :
    (∑ a, ∑ b, ((B a b : ℂ) * t / 2) * conj (l a b)) =
      t * conj (complexMetricTrace B l) / 2 := by
  have hTrace : conj (complexMetricTrace B l) = ∑ a, ∑ b, (B a b : ℂ) * conj (l a b) := by
    simp only [complexMetricTrace, map_sum, map_mul, Complex.conj_ofReal]
  rw [hTrace]
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Trace reversal and both raisings, paired in the original lower-component
coordinates, yield the original physical pairing with the Ricci symbol. -/
theorem hessianPairing_eq_physicalRicci (B : Tensor2) (hB : IsSymmetricTensor B)
    (w : ℝ) (ξ : Covector) (k l : ComplexTensor2) :
    hessianPairing B w ξ k l =
      (w : ℂ) * hermitianPhysicalPairing B (complexRicciSymbol B ξ k) l := by
  let R := complexRicciSymbol B ξ k
  unfold hessianPairing
  change (∑ a, ∑ b, ((w : ℂ) * (raiseBoth B R a b - (B a b : ℂ) * complexMetricTrace B R / 2)) *
      conj (l a b)) = _
  calc
    _ = (w : ℂ) * ∑ a, ∑ b,
          (raiseBoth B R a b - (B a b : ℂ) * complexMetricTrace B R / 2) * conj (l a b) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [raiseBoth_ordered_pairing B hB R l, trace_ordered_pairing]
      rfl

private theorem realPhysicalPairing_pureGauge_left (B : Tensor2) (hB : IsSymmetricTensor B)
    (ξ v : Covector) (l : Tensor2) (hl : IsSymmetricTensor l) :
    physicalPairing B (pureGauge ξ v) l =
      2 * ∑ i, realGaugeCovector B ξ l i * raiseCovector B v i := by
  have hSum : (∑ i, realGaugeCovector B ξ l i * raiseCovector B v i) =
      (∑ i, contracted B ξ l i * raiseCovector B v i) -
        metricTrace B l / 2 * ∑ i, ξ i * raiseCovector B v i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold realGaugeCovector
    ring
  rw [physicalPairing_comm B (pureGauge ξ v) l hB, physicalPairing,
    tensorPairing_pureGauge B l ξ v hl, metricTrace_pureGauge B ξ v hB, hSum]
  ring

private theorem gaugeCovector_re (B : Tensor2) (ξ : Covector) (k : ComplexTensor2) (i : Index) :
    (gaugeCovector B ξ k i).re = realGaugeCovector B ξ (tensorRe k) i := by
  simp [gaugeCovector, realGaugeCovector, Complex.mul_re]

private theorem gaugeCovector_im (B : Tensor2) (ξ : Covector) (k : ComplexTensor2) (i : Index) :
    (gaugeCovector B ξ k i).im = realGaugeCovector B ξ (tensorIm k) i := by
  simp [gaugeCovector, realGaugeCovector, Complex.mul_im]

private theorem raiseComplexCovector_re (B : Tensor2) (v : ComplexCovector) (i : Index) :
    (raiseComplexCovector B v i).re = raiseCovector B (fun j => (v j).re) i := by
  simp [raiseComplexCovector, raiseCovector, Complex.mul_re]

private theorem raiseComplexCovector_im (B : Tensor2) (v : ComplexCovector) (i : Index) :
    (raiseComplexCovector B v i).im = raiseCovector B (fun j => (v j).im) i := by
  simp [raiseComplexCovector, raiseCovector, Complex.mul_im]

private theorem physicalPairing_complexGauge (B : Tensor2) (hB : IsSymmetricTensor B)
    (ξ : Covector) (v : ComplexCovector) (l : ComplexTensor2) (hl : IsSymmetricComplexTensor l) :
    hermitianPhysicalPairing B (complexPureGauge ξ v) l =
      2 * gaugeHermitianPairing B v (gaugeCovector B ξ l) := by
  have hlr := tensorRe_symmetric l hl
  have hli := tensorIm_symmetric l hl
  apply Complex.ext
  · rw [hermitianPhysicalPairing_re, tensorRe_complexPureGauge, tensorIm_complexPureGauge,
      realPhysicalPairing_pureGauge_left B hB _ _ _ hlr,
      realPhysicalPairing_pureGauge_left B hB _ _ _ hli]
    simp only [gaugeHermitianPairing, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero, Complex.re_sum, Complex.conj_re, Complex.conj_im,
      raiseComplexCovector_re, raiseComplexCovector_im, gaugeCovector_re, gaugeCovector_im,
      mul_neg, sub_neg_eq_add, Finset.sum_add_distrib]
    simp only [mul_comm]
    ring
  · rw [hermitianPhysicalPairing_im, tensorRe_complexPureGauge, tensorIm_complexPureGauge,
      realPhysicalPairing_pureGauge_left B hB _ _ _ hlr,
      realPhysicalPairing_pureGauge_left B hB _ _ _ hli]
    simp only [gaugeHermitianPairing, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, add_zero, Complex.im_sum, Complex.conj_re, Complex.conj_im,
      raiseComplexCovector_re, raiseComplexCovector_im, gaugeCovector_re, gaugeCovector_im,
      mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    simp only [mul_comm]
    ring

/-- The Ricci symbol splits into phase times the amplitude and a pure gauge. -/
theorem complexRicciSymbol_eq_phase_sub_gauge (B : Tensor2) (ξ : Covector)
    (k : ComplexTensor2) :
    complexRicciSymbol B ξ k = ((symbolNorm B ξ : ℂ) / 2) • k +
      (-1 / 2 : ℂ) • complexPureGauge ξ (gaugeCovector B ξ k) := by
  funext i j
  simp only [complexRicciSymbol, gaugeCovector, complexPureGauge, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- The exact equation (var-hessian-form) on both complex slots, with
the paper's Hamiltonian `symbolNorm / 2` and the factor 4. -/
theorem hessianPairing_eq_phase_sub_gauge (B : Tensor2) (hB : IsSymmetricTensor B)
    (w : ℝ) (ξ : Covector) (k l : ComplexTensor2) (hl : IsSymmetricComplexTensor l) :
    hessianPairing B w ξ k l = (w : ℂ) *
      (4 * ((symbolNorm B ξ / 2 : ℝ) : ℂ) * physicalForm B k l -
        gaugeHermitianPairing B (gaugeCovector B ξ k) (gaugeCovector B ξ l)) := by
  rw [hessianPairing_eq_physicalRicci B hB w ξ k l, complexRicciSymbol_eq_phase_sub_gauge,
    hermitianPhysicalPairing_add_left, hermitianPhysicalPairing_smul_left,
    hermitianPhysicalPairing_smul_left, physicalPairing_complexGauge B hB ξ _ l hl]
  simp only [physicalForm, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

private theorem gaugeHermitianPairing_conj_symm (B : Tensor2) (hB : IsSymmetricTensor B)
    (v z : ComplexCovector) : gaugeHermitianPairing B v z = conj (gaugeHermitianPairing B z v) := by
  simp only [gaugeHermitianPairing, raiseComplexCovector, Finset.sum_mul, map_sum, map_mul,
    Complex.conj_ofReal, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hB j i]
  ring

/-- Hermitian symmetry of the actual raised Hessian symbol on symmetric tensors. -/
theorem hessianPairing_conj_symm (B : Tensor2) (hB : IsSymmetricTensor B)
    (w : ℝ) (ξ : Covector) (k l : ComplexTensor2) (hk : IsSymmetricComplexTensor k)
    (hl : IsSymmetricComplexTensor l) :
    hessianPairing B w ξ k l = conj (hessianPairing B w ξ l k) := by
  rw [hessianPairing_eq_phase_sub_gauge B hB w ξ k l hl,
    hessianPairing_eq_phase_sub_gauge B hB w ξ l k hk,
    gaugeHermitianPairing_conj_symm B hB (gaugeCovector B ξ k) (gaugeCovector B ξ l)]
  simp only [physicalForm, map_mul, map_sub, map_div₀, Complex.conj_ofReal, map_ofNat]
  rw [hermitianPhysicalPairing_conj_symm B k l hB]

/-- Both complex components of the exact null Ricci kernel obey the same
lowered gauge constraint. -/
theorem gaugeCovector_eq_zero_of_nullRicciKernel (B : Tensor2) (ξ : Covector)
    (hξ : ξ ≠ 0) (hs : symbolNorm B ξ = 0) (k : ComplexTensor2)
    (hk : ∀ a b, complexRicciSymbol B ξ k a b = 0) : gaugeCovector B ξ k = 0 := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff B ξ k).mp hk
  have hr := (null_kernel_iff_contracted B ξ (tensorRe k) hξ hs).mp hkr
  have hi := (null_kernel_iff_contracted B ξ (tensorIm k) hξ hs).mp hki
  funext i
  apply Complex.ext
  · simp [gaugeCovector_re, realGaugeCovector, hr]
  · simp [gaugeCovector_im, realGaugeCovector, hi]

/-- Every complex off-characteristic Ricci-kernel tensor is an actual pure gauge. -/
theorem complexRicciKernel_eq_pureGauge_of_offNull (B : Tensor2) (ξ : Covector)
    (hs : symbolNorm B ξ ≠ 0) (k : ComplexTensor2)
    (hk : ∀ a b, complexRicciSymbol B ξ k a b = 0) :
    ∃ v : ComplexCovector, k = complexPureGauge ξ v := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff B ξ k).mp hk
  let vr := kernelGaugeVector B ξ (tensorRe k)
  let vi := kernelGaugeVector B ξ (tensorIm k)
  let v : ComplexCovector := fun i => ⟨vr i, vi i⟩
  have hr : tensorRe k = tensorRe (complexPureGauge ξ v) := by
    rw [tensorRe_complexPureGauge]
    exact kernel_eq_pureGauge B ξ (tensorRe k) hs hkr
  have hi : tensorIm k = tensorIm (complexPureGauge ξ v) := by
    rw [tensorIm_complexPureGauge]
    exact kernel_eq_pureGauge B ξ (tensorIm k) hs hki
  exact ⟨v, funext fun a => funext fun b => Complex.ext (congrFun (congrFun hr a) b)
    (congrFun (congrFun hi a) b)⟩

/-- The exact density symbol annihilates pure gauge at every phase point. -/
theorem hessianPairing_pureGauge_left (B : Tensor2) (hB : IsSymmetricTensor B)
    (w : ℝ) (ξ : Covector) (v : ComplexCovector) (l : ComplexTensor2) :
    hessianPairing B w ξ (complexPureGauge ξ v) l = 0 := by
  have hz : complexRicciSymbol B ξ (complexPureGauge ξ v) = 0 :=
    funext fun i => funext fun j => complexRicciSymbol_pureGauge_eq_zero B ξ v hB i j
  simp [hessianPairing, einsteinDensitySymbol, hz, raiseBoth, complexRaiseSecond, complexMetricTrace]

theorem hessianPairing_pureGauge_right (B : Tensor2) (hB : IsSymmetricTensor B)
    (w : ℝ) (ξ : Covector) (k : ComplexTensor2) (hk : IsSymmetricComplexTensor k)
    (v : ComplexCovector) : hessianPairing B w ξ k (complexPureGauge ξ v) = 0 := by
  rw [hessianPairing_conj_symm B hB w ξ k (complexPureGauge ξ v) hk (complexPureGauge_symmetric ξ v),
    hessianPairing_pureGauge_left B hB w ξ v k, map_zero]

end Burnett.V02
