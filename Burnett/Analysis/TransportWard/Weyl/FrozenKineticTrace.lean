import Burnett.Analysis.TransportWard.Weyl.HermitianHessianForm
import Burnett.Algebra.QuadraticExpansion

/-! The real trace of the original F06 connection products. -/

set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option maxRecDepth 4300

noncomputable section

namespace Burnett.V02

open Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate

private def covectorPairing (B : Tensor2) (u v : Covector) : ℝ :=
  metricTrace B (fun i j => u i * v j)

private def gaugeCovectorReal (B : Tensor2) (p : Covector) (J : Tensor2) (i : Index) : ℝ :=
  contracted B p J i - metricTrace B J * p i / 2

private theorem covectorPairing_comm (B : Tensor2) (hB : IsSymmetricTensor B) (u v : Covector) :
    covectorPairing B u v = covectorPairing B v u := by
  unfold covectorPairing metricTrace
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hB j i]
  ring

private theorem covectorPairing_self_eq_symbolNorm (B : Tensor2) (p : Covector) :
    covectorPairing B p p = symbolNorm B p := by
  simp only [covectorPairing, metricTrace, symbolNorm, mul_assoc]

private theorem metricTrace_tensorSquare (B J : Tensor2) (hB : IsSymmetricTensor B)
    (hJ : IsSymmetricTensor J) : metricTrace B (tensorSquare B J) = tensorPairing B J J := by
  unfold metricTrace tensorSquare raiseSecond tensorPairing
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ j, ∑ d, ∑ a, B i j * (B a d * J i d * J a j) := by
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ d, ∑ j, ∑ a, B i j * (B a d * J i d * J a j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      rw [hB a d, hJ a j]
      ring

private theorem four_metricTrace_quadraticSymbol (B J : Tensor2) (p : Covector)
    (hB : IsSymmetricTensor B) (hJ : IsSymmetricTensor J) :
    let s := symbolNorm B p
    let t := metricTrace B J
    let q := contracted B p J
    4 * metricTrace B (quadraticSymbol B p J) =
      -(s * tensorPairing B J J) + 2 * covectorPairing B q q -
        2 * t * covectorPairing B p q + s * t ^ 2 := by
  intro s t q
  have hsum : 4 * metricTrace B (quadraticSymbol B p J) =
      tensorPairing B J J * covectorPairing B p p + 2 * covectorPairing B q q -
        (2 * s) * metricTrace B (tensorSquare B J) -
        t * (covectorPairing B p q + covectorPairing B q p - s * metricTrace B J) := by
    simp only [covectorPairing, metricTrace, mul_add, mul_sub, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    linear_combination B i j * four_quadraticSymbol_expansion B p J hB hJ i j
  rw [hsum, covectorPairing_self_eq_symbolNorm, metricTrace_tensorSquare B J hB hJ,
    covectorPairing_comm B hB q p]
  change tensorPairing B J J * s + 2 * covectorPairing B q q -
    (2 * s) * tensorPairing B J J - t * (covectorPairing B p q + covectorPairing B p q - s * t) = _
  ring

private theorem gaugeCovectorReal_square (B J : Tensor2) (p : Covector) (hB : IsSymmetricTensor B) :
    let s := symbolNorm B p
    let t := metricTrace B J
    let q := contracted B p J
    covectorPairing B (gaugeCovectorReal B p J) (gaugeCovectorReal B p J) =
      covectorPairing B q q - t * covectorPairing B p q + t ^ 2 / 4 * s := by
  intro s t q
  have h : covectorPairing B (gaugeCovectorReal B p J) (gaugeCovectorReal B p J) =
      covectorPairing B q q - (t / 2) * covectorPairing B p q -
        (t / 2) * covectorPairing B q p + (t / 2) ^ 2 * covectorPairing B p p := by
    simp only [covectorPairing, metricTrace, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change B i j * ((q i - t * p i / 2) * (q j - t * p j / 2)) = _
    ring
  rw [h, covectorPairing_comm B hB q p, covectorPairing_self_eq_symbolNorm B p]
  change _ = covectorPairing B q q - t * covectorPairing B p q + t ^ 2 / 4 * symbolNorm B p
  ring

private theorem gaugeCovector_ofReal (B : Tensor2) (p : Covector) (J : Tensor2) :
    gaugeCovector B p (tensorOfReal J) = fun i => (gaugeCovectorReal B p J i : ℂ) := by
  funext i
  simp only [gaugeCovector, gaugeCovectorReal, complexContracted, complexMetricTrace,
    contracted, metricTrace, tensorOfReal, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_ofNat]

private theorem gaugeHermitianPairing_ofReal (B : Tensor2) (u v : Covector) :
    gaugeHermitianPairing B (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) = (covectorPairing B v u : ℂ) := by
  simp only [gaugeHermitianPairing, raiseComplexCovector, covectorPairing, metricTrace,
    Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem tensorOfReal_ricciSymbol (B : Tensor2) (p : Covector) (J : Tensor2) :
    complexRicciSymbol B p (tensorOfReal J) = tensorOfReal (ricciSymbol B p J) := by
  funext i j
  simp only [complexRicciSymbol, ricciSymbol, complexMetricTrace, complexContracted,
    tensorOfReal, metricTrace, contracted, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat]

private theorem isSymmetricComplexTensor_ofReal (J : Tensor2) (hJ : IsSymmetricTensor J) :
    IsSymmetricComplexTensor (tensorOfReal J) :=
  fun i j => congrArg Complex.ofReal (hJ i j)

private theorem hessianPairing_ofReal_unit (B : Tensor2) (hB : IsSymmetricTensor B) (p : Covector)
    (J L : Tensor2) :
    hessianPairing B 1 p (tensorOfReal J) (tensorOfReal L) =
      (physicalPairing B (ricciSymbol B p J) L : ℂ) := by
  rw [hessianPairing_eq_physicalRicci B hB, tensorOfReal_ricciSymbol,
    hermitianPhysicalPairing_ofReal, Complex.ofReal_one, one_mul]

private theorem physicalRicci_diagonal (B J : Tensor2) (p : Covector)
    (hB : IsSymmetricTensor B) (hJ : IsSymmetricTensor J) :
    physicalPairing B (ricciSymbol B p J) J = -2 * metricTrace B (quadraticSymbol B p J) := by
  have h := hessianPairing_eq_phase_sub_gauge B hB 1 p (tensorOfReal J) (tensorOfReal J)
    (isSymmetricComplexTensor_ofReal J hJ)
  rw [hessianPairing_ofReal_unit B hB, Complex.ofReal_one, one_mul, physicalForm,
    hermitianPhysicalPairing_ofReal, gaugeCovector_ofReal, gaugeHermitianPairing_ofReal] at h
  have hReal : physicalPairing B (ricciSymbol B p J) J =
      4 * (symbolNorm B p / 2) * (physicalPairing B J J / 4) -
        covectorPairing B (gaugeCovectorReal B p J) (gaugeCovectorReal B p J) := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using h
  have hTrace := four_metricTrace_quadraticSymbol B J p hB hJ
  dsimp only at hTrace
  rw [hReal, gaugeCovectorReal_square B J p hB, physicalPairing]
  linear_combination 1 / 2 * hTrace

private theorem physicalRicci_comm (B : Tensor2) (p : Covector) (J L : Tensor2)
    (hB : IsSymmetricTensor B) (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L) :
    physicalPairing B (ricciSymbol B p J) L = physicalPairing B (ricciSymbol B p L) J := by
  have h := hessianPairing_conj_symm B hB 1 p (tensorOfReal J) (tensorOfReal L)
    (isSymmetricComplexTensor_ofReal J hJ) (isSymmetricComplexTensor_ofReal L hL)
  rw [hessianPairing_ofReal_unit B hB, hessianPairing_ofReal_unit B hB, Complex.conj_ofReal] at h
  exact Complex.ofReal_injective h

/-- Trace of the exact F06 mixed connection products, paired with the
trace-reversed, raised Ricci symbol. The real sign and factor are fixed by
the diagonal identity before polarizing. -/
theorem physicalRicci_eq_neg_two_trace_mixedQuadraticSymbol (B : Tensor2) (p : Covector)
    (J L : Tensor2) (hB : IsSymmetricTensor B) (hJ : IsSymmetricTensor J)
    (hL : IsSymmetricTensor L) :
    physicalPairing B (ricciSymbol B p J) L = -2 * metricTrace B (mixedQuadraticSymbol B p J L) := by
  have hJL : IsSymmetricTensor (J + L) := by
    intro i j
    simp only [Pi.add_apply, hJ i j, hL i j]
  have hAdd : ricciSymbol B p (J + L) = ricciSymbol B p J + ricciSymbol B p L :=
    funext fun i => funext fun j => ricciSymbol_add B p J L i j
  have hAll := physicalRicci_diagonal B (J + L) p hB hJL
  rw [hAdd, physicalPairing_add_left, physicalPairing_add_right, physicalPairing_add_right,
    physicalRicci_comm B p L J hB hL hJ] at hAll
  have hTrace : metricTrace B (mixedQuadraticSymbol B p J L) =
      (metricTrace B (quadraticSymbol B p (J + L)) - metricTrace B (quadraticSymbol B p J) -
        metricTrace B (quadraticSymbol B p L)) / 2 := by
    simp only [metricTrace, mixedQuadraticSymbol_polarization, div_eq_mul_inv, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hTrace]
  linarith [physicalRicci_diagonal B J p hB hJ, physicalRicci_diagonal B L p hB hL]

end Burnett.V02
