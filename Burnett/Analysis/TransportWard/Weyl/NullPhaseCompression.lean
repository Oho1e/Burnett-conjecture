import Burnett.Analysis.TransportWard.Weyl.CoordinatePhase

/-! Null Ricci-kernel compression of the actual Poisson derivative. -/

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 4300

noncomputable section

namespace Burnett.V02

open Function Filter Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Bianchi.RayIdentification (coordinateHamiltonian canonicalBracket)
open scoped BigOperators ComplexConjugate ContDiff Topology

local notation "E" => CoordinateSpace

private theorem hasFDerivAt_phaseGaugePair_zero (g : E → Mat) (z : Phase)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y : Phase => phaseInverse g y i j) z)
    (k l : ComplexTensor2) (hk : gaugeCovector (phaseInverse g z) z.2 k = 0)
    (hl : gaugeCovector (phaseInverse g z) z.2 l = 0) :
    HasFDerivAt (fun y : Phase => gaugeHermitianPairing (phaseInverse g y)
      (gaugeCovector (phaseInverse g y) y.2 k) (gaugeCovector (phaseInverse g y) y.2 l))
      (0 : Phase →L[ℝ] ℂ) z := by
  let u (i : Index) (y : Phase) := raiseComplexCovector (phaseInverse g y)
    (gaugeCovector (phaseInverse g y) y.2 k) i
  let v (i : Index) (y : Phase) := conj (gaugeCovector (phaseInverse g y) y.2 l i)
  have hu (i : Index) : DifferentiableAt ℝ (u i) z := by
    unfold u raiseComplexCovector
    refine DifferentiableAt.fun_sum fun j _ => ?_
    exact (Complex.ofRealCLM.differentiableAt.comp z (hB i j)).mul
      (differentiableAt_phaseGauge g z hB k j)
  have hv (i : Index) : DifferentiableAt ℝ (v i) z :=
    Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp z (differentiableAt_phaseGauge g z hB l i)
  have hu₀ (i : Index) : u i z = 0 := by simp [u, hk, raiseComplexCovector]
  have hv₀ (i : Index) : v i z = 0 := by simp [v, hl]
  have term (i : Index) : HasFDerivAt (fun y : Phase => u i y * v i y) (0 : Phase →L[ℝ] ℂ) z := by
    have hzMap : u i z • fderiv ℝ (v i) z + v i z • fderiv ℝ (u i) z = 0 := by
      apply ContinuousLinearMap.ext
      intro V
      simp [hu₀, hv₀, smul_eq_mul]
    rw [← hzMap]
    exact (hu i).hasFDerivAt.fun_mul (hv i).hasFDerivAt
  change HasFDerivAt (fun y : Phase => ∑ i, u i y * v i y) (0 : Phase →L[ℝ] ℂ) z
  simpa only [Finset.sum_const_zero] using (HasFDerivAt.fun_sum fun i _ => term i)

/-- The direction derivative of the exact Hermitian symbol, with both complex
coordinate amplitudes frozen at a nonzero null Ricci-kernel point. -/
theorem fderiv_phaseHessianPairing_of_nullRicciKernel
    (g : E → Mat) (U : Set E) (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U)
    (hn : ∀ x ∈ U, Matrix.det (g x) ≠ 0) (hSym : ∀ x ∈ U, IsSymmetricTensor (g x))
    (z : Phase) (hz : z.1 ∈ U) (hξ : z.2 ≠ 0)
    (hNull : symbolNorm (phaseInverse g z) z.2 = 0)
    (k l : ComplexTensor2) (hl : IsSymmetricComplexTensor l)
    (hkR : ∀ i j, complexRicciSymbol (phaseInverse g z) z.2 k i j = 0)
    (hlR : ∀ i j, complexRicciSymbol (phaseInverse g z) z.2 l i j = 0) (V : Phase) :
    fderiv ℝ (phaseHessianPairing g k l) z V =
      4 * (phaseDensity g z : ℂ) * (fderiv ℝ (phaseHamiltonian g) z V : ℂ) *
        physicalForm (phaseInverse g z) k l := by
  obtain ⟨hB, hw⟩ := differentiableAt_phaseInverse_density g U hU hg hn z hz
  have hP := differentiableAt_phaseHamiltonian g z hB
  have hC := differentiableAt_phasePhysical g z hB k l
  have hk := gaugeCovector_eq_zero_of_nullRicciKernel _ _ hξ hNull k hkR
  have hl₀ := gaugeCovector_eq_zero_of_nullRicciKernel _ _ hξ hNull l hlR
  let P (y : Phase) : ℂ := (phaseHamiltonian g y : ℂ)
  let C (y : Phase) := physicalForm (phaseInverse g y) k l
  let w (y : Phase) : ℂ := (phaseDensity g y : ℂ)
  let G (y : Phase) := gaugeHermitianPairing (phaseInverse g y)
    (gaugeCovector (phaseInverse g y) y.2 k) (gaugeCovector (phaseInverse g y) y.2 l)
  have hp₀ : P z = 0 := by
    change ((symbolNorm (phaseInverse g z) z.2 / 2 : ℝ) : ℂ) = 0
    rw [hNull, zero_div, Complex.ofReal_zero]
  have hG₀ : G z = 0 := by simp [G, hk, hl₀, gaugeHermitianPairing, raiseComplexCovector]
  have hEq : phaseHessianPairing g k l =ᶠ[𝓝 z] fun y => w y * (4 * P y * C y - G y) := by
    filter_upwards [(hU.preimage continuous_fst).mem_nhds hz] with y hy
    exact hessianPairing_eq_phase_sub_gauge (phaseInverse g y)
      (phaseInverse_symmetric g y (hSym y.1 hy)) (phaseDensity g y) y.2 k l hl
  have hPc : HasFDerivAt P (Complex.ofRealCLM.comp (fderiv ℝ (phaseHamiltonian g) z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hP.hasFDerivAt
  have hC' : DifferentiableAt ℝ C z := hC
  have hw' : DifferentiableAt ℝ w z := Complex.ofRealCLM.differentiableAt.comp z hw
  have hG : HasFDerivAt G (0 : Phase →L[ℝ] ℂ) z := hasFDerivAt_phaseGaugePair_zero g z hB k l hk hl₀
  have hProd := ((hPc.const_mul (4 : ℂ)).fun_mul hC'.hasFDerivAt).sub hG
  have hD := hw'.hasFDerivAt.fun_mul hProd
  have hD' : HasFDerivAt (fun y => w y * (4 * P y * C y - G y)) (_ : Phase →L[ℝ] ℂ) z := hD
  rw [hEq.fderiv_eq, hD'.fderiv]
  simp [hp₀, hG₀, w, C, smul_eq_mul]
  ring

/-- The actual componentwise Poisson bracket `{A,a}` in canonical coordinates. -/
def phaseEinsteinPoissonBracket (g : E → Mat) (k : ComplexTensor2)
    (a : E → Covector → ℝ) (z : Phase) (i j : Index) : ℂ :=
  fderiv ℝ (fun y : Phase => phaseEinsteinSymbol g k y i j) z (phasePoissonDirection a z)

/-- Differentiating the pairing with a fixed second amplitude is exactly
the ordered pairing with the differentiated symbol. -/
theorem phaseEinsteinPoissonBracket_ordered_pairing (g : E → Mat) (z : Phase)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y : Phase => phaseInverse g y i j) z)
    (hw : DifferentiableAt ℝ (phaseDensity g) z)
    (k l : ComplexTensor2) (a : E → Covector → ℝ) :
    (∑ i, ∑ j, phaseEinsteinPoissonBracket g k a z i j * conj (l i j)) =
      fderiv ℝ (phaseHessianPairing g k l) z (phasePoissonDirection a z) := by
  have theorem_deriv := HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) =>
    HasFDerivAt.fun_sum fun j (_ : j ∈ Finset.univ) =>
      ((differentiableAt_phaseEinsteinSymbol g z hB hw k i j).hasFDerivAt.mul_const (conj (l i j)))
  change _ = fderiv ℝ (fun y : Phase => ∑ i, ∑ j, phaseEinsteinSymbol g k y i j * conj (l i j)) z _
  rw [theorem_deriv.fderiv]
  simp only [phaseEinsteinPoissonBracket, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  congr 1
  funext i
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Formula (1799) on the entire mixed complex null kernel. The factor 4
multiplies the actual density and the canonical Hamilton bracket for P. -/
theorem phaseEinsteinPoissonBracket_nullRicciKernel
    (g : E → Mat) (U : Set E) (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U)
    (hn : ∀ x ∈ U, Matrix.det (g x) ≠ 0) (hSym : ∀ x ∈ U, IsSymmetricTensor (g x))
    (z : Phase) (hz : z.1 ∈ U) (hξ : z.2 ≠ 0) (hNull : symbolNorm (phaseInverse g z) z.2 = 0)
    (k l : ComplexTensor2) (hl : IsSymmetricComplexTensor l)
    (hkR : ∀ i j, complexRicciSymbol (phaseInverse g z) z.2 k i j = 0)
    (hlR : ∀ i j, complexRicciSymbol (phaseInverse g z) z.2 l i j = 0)
    (a : E → Covector → ℝ) :
    (∑ i, ∑ j, phaseEinsteinPoissonBracket g k a z i j * conj (l i j)) =
      4 * (phaseDensity g z : ℂ) * (canonicalBracket (coordinateHamiltonian g) a z.1 z.2 : ℂ) *
        physicalForm (phaseInverse g z) k l := by
  obtain ⟨hB, hw⟩ := differentiableAt_phaseInverse_density g U hU hg hn z hz
  rw [phaseEinsteinPoissonBracket_ordered_pairing g z hB hw k l a,
    fderiv_phaseHessianPairing_of_nullRicciKernel g U hU hg hn hSym z hz hξ hNull k l hl hkR hlR]
  have h := phasePoissonDirection_eq_canonicalBracket (coordinateHamiltonian g) a z
    (differentiableAt_phaseHamiltonian g z hB)
  exact congrArg (fun x : ℝ => 4 * (phaseDensity g z : ℂ) * (x : ℂ) *
    physicalForm (phaseInverse g z) k l) h

end Burnett.V02
