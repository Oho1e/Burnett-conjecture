import Burnett.Analysis.TransportWard.Weyl.NullPhaseCompression

/-! Off-characteristic compression of the same actual phase symbol. -/

set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option maxRecDepth 4300

noncomputable section

namespace Burnett.V02

open Function Filter Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Analysis.TransportWardSymbol (Mat)
open scoped BigOperators ComplexConjugate ContDiff Topology

local notation "E" => CoordinateSpace

private theorem complexRicciSymbol_smul (B : Tensor2) (ξ : Covector) (α : ℂ)
    (k : ComplexTensor2) : complexRicciSymbol B ξ (α • k) = α • complexRicciSymbol B ξ k := by
  have hQ (b : Index) : complexContracted B ξ (α • k) b = α * complexContracted B ξ k b := by
    simp only [complexContracted, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  funext i j
  simp only [complexRicciSymbol, hQ, complexMetricTrace_smul, Pi.smul_apply, smul_eq_mul]
  ring

private theorem hessianPairing_add_left (B : Tensor2) (hB : IsSymmetricTensor B)
    (w : ℝ) (ξ : Covector) (k₁ k₂ l : ComplexTensor2) :
    hessianPairing B w ξ (k₁ + k₂) l = hessianPairing B w ξ k₁ l + hessianPairing B w ξ k₂ l := by
  have h : complexRicciSymbol B ξ (k₁ + k₂) =
      complexRicciSymbol B ξ k₁ + complexRicciSymbol B ξ k₂ :=
    funext fun i => funext fun j => complexRicciSymbol_add B ξ k₁ k₂ i j
  simp only [hessianPairing_eq_physicalRicci B hB, h, hermitianPhysicalPairing_add_left, mul_add]

private theorem hessianPairing_add_right (B : Tensor2) (hB : IsSymmetricTensor B)
    (w : ℝ) (ξ : Covector) (k l₁ l₂ : ComplexTensor2) :
    hessianPairing B w ξ k (l₁ + l₂) = hessianPairing B w ξ k l₁ + hessianPairing B w ξ k l₂ := by
  simp only [hessianPairing_eq_physicalRicci B hB,
    hermitianPhysicalPairing_add_right B _ _ _ hB, mul_add]

private theorem hessianPairing_smul_left (B : Tensor2) (hB : IsSymmetricTensor B)
    (w : ℝ) (ξ : Covector) (α : ℂ) (k l : ComplexTensor2) :
    hessianPairing B w ξ (α • k) l = α * hessianPairing B w ξ k l := by
  simp only [hessianPairing_eq_physicalRicci B hB, complexRicciSymbol_smul,
    hermitianPhysicalPairing_smul_left]
  ring

private theorem hessianPairing_smul_right (B : Tensor2) (hB : IsSymmetricTensor B)
    (w : ℝ) (ξ : Covector) (α : ℂ) (k l : ComplexTensor2) :
    hessianPairing B w ξ k (α • l) = conj α * hessianPairing B w ξ k l := by
  simp only [hessianPairing_eq_physicalRicci B hB,
    hermitianPhysicalPairing_smul_right B _ _ _ hB]
  ring

private def phaseLine (z V : Phase) (t : ℝ) : Phase := z + t • V

private theorem phaseLine_zero (z V : Phase) : phaseLine z V 0 = z := by
  simp [phaseLine]

private theorem gauge_eq_gaugeLine_sub (z V : Phase) (t : ℝ) (v : ComplexCovector) :
    complexPureGauge z.2 v = complexPureGauge (phaseLine z V t).2 v +
      (-(t : ℂ)) • complexPureGauge V.2 v := by
  funext i j
  change _ = (complexPureGauge (z.2 + t • V.2) v + (-(t : ℂ)) • complexPureGauge V.2 v) i j
  simp only [complexPureGauge, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- When both frozen amplitudes are genuine gauges at the starting frequency,
their pairing along an arbitrary phase line has two vanishing gauge factors. -/
private theorem phaseHessianPairing_pureGauge_line (g : E → Mat) (z V : Phase) (t : ℝ)
    (hSym : IsSymmetricTensor (g (phaseLine z V t).1)) (v u : ComplexCovector) :
    phaseHessianPairing g (complexPureGauge z.2 v) (complexPureGauge z.2 u) (phaseLine z V t) =
      (t : ℂ)^2 * phaseHessianPairing g (complexPureGauge V.2 v) (complexPureGauge V.2 u) (phaseLine z V t) := by
  let y := phaseLine z V t
  let B := phaseInverse g y
  have hB : IsSymmetricTensor B := phaseInverse_symmetric g y hSym
  change hessianPairing B (phaseDensity g y) y.2 (complexPureGauge z.2 v) (complexPureGauge z.2 u) =
    (t : ℂ)^2 * hessianPairing B (phaseDensity g y) y.2 (complexPureGauge V.2 v) (complexPureGauge V.2 u)
  rw [gauge_eq_gaugeLine_sub z V t v, gauge_eq_gaugeLine_sub z V t u,
    hessianPairing_add_left B hB, hessianPairing_pureGauge_left B hB, zero_add,
    hessianPairing_smul_left B hB, hessianPairing_add_right B hB,
    hessianPairing_pureGauge_right B hB _ _ _ (complexPureGauge_symmetric _ _) _, zero_add,
    hessianPairing_smul_right B hB]
  simp only [map_neg, Complex.conj_ofReal]
  ring

/-- The derivative in every phase direction vanishes on two genuine gauge
amplitudes, with no characteristic assumption along the differentiating line. -/
theorem fderiv_phaseHessianPairing_pureGauge
    (g : E → Mat) (U : Set E) (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U)
    (hn : ∀ x ∈ U, Matrix.det (g x) ≠ 0) (hSym : ∀ x ∈ U, IsSymmetricTensor (g x))
    (z V : Phase) (hz : z.1 ∈ U) (v u : ComplexCovector) :
    fderiv ℝ (phaseHessianPairing g (complexPureGauge z.2 v) (complexPureGauge z.2 u)) z V = 0 := by
  obtain ⟨hB, hw⟩ := differentiableAt_phaseInverse_density g U hU hg hn z hz
  let F := phaseHessianPairing g (complexPureGauge z.2 v) (complexPureGauge z.2 u)
  let G := phaseHessianPairing g (complexPureGauge V.2 v) (complexPureGauge V.2 u)
  have hF : DifferentiableAt ℝ F z := differentiableAt_phaseHessianPairing g z hB hw _ _
  have hG : DifferentiableAt ℝ G z := differentiableAt_phaseHessianPairing g z hB hw _ _
  have hLine : HasDerivAt (phaseLine z V) V 0 := by
    have hd : HasDerivAt (fun t : ℝ => t • V) V 0 := by
      simpa only [one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const V
    change HasDerivAt (fun t : ℝ => z + t • V) V 0
    exact hd.const_add z
  have hF' := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hLine (phaseLine_zero z V).symm
  have hG' := hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hLine (phaseLine_zero z V).symm
  have hU' : ∀ᶠ t in 𝓝 (0 : ℝ), (phaseLine z V t).1 ∈ U :=
    hLine.continuousAt.eventually (by simpa only [phaseLine_zero] using
      (hU.preimage continuous_fst).mem_nhds hz)
  have hEq : (F ∘ phaseLine z V) =ᶠ[𝓝 (0 : ℝ)] fun t => (t : ℂ)^2 * G (phaseLine z V t) := by
    filter_upwards [hU'] with t ht
    exact phaseHessianPairing_pureGauge_line g z V t (hSym _ ht) v u
  have hCast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 :=
    by simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)))
  have hSq : HasDerivAt (fun t : ℝ => (t : ℂ)^2) 0 0 := by
    simpa using hCast.pow 2
  have hProd : HasDerivAt (fun t : ℝ => (t : ℂ)^2 * G (phaseLine z V t)) 0 0 := by
    simpa [Function.comp_def] using hSq.mul hG'
  exact hF'.unique (hProd.congr_of_eventuallyEq hEq)

/-- The full off-null Ricci kernel consists of actual complex gauges. The
ordered compression of the actual componentwise bracket is zero there. -/
theorem phaseEinsteinPoissonBracket_offNullRicciKernel
    (g : E → Mat) (U : Set E) (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U)
    (hn : ∀ x ∈ U, Matrix.det (g x) ≠ 0) (hSym : ∀ x ∈ U, IsSymmetricTensor (g x))
    (z : Phase) (hz : z.1 ∈ U) (hOff : symbolNorm (phaseInverse g z) z.2 ≠ 0)
    (k l : ComplexTensor2)
    (hkR : ∀ i j, complexRicciSymbol (phaseInverse g z) z.2 k i j = 0)
    (hlR : ∀ i j, complexRicciSymbol (phaseInverse g z) z.2 l i j = 0) (a : E → Covector → ℝ) :
    (∑ i, ∑ j, phaseEinsteinPoissonBracket g k a z i j * conj (l i j)) = 0 := by
  obtain ⟨hB, hw⟩ := differentiableAt_phaseInverse_density g U hU hg hn z hz
  obtain ⟨v, hv⟩ := complexRicciKernel_eq_pureGauge_of_offNull _ _ hOff k hkR
  obtain ⟨u, hu⟩ := complexRicciKernel_eq_pureGauge_of_offNull _ _ hOff l hlR
  rw [phaseEinsteinPoissonBracket_ordered_pairing g z hB hw k l a, hv, hu]
  exact fderiv_phaseHessianPairing_pureGauge g U hU hg hn hSym z (phasePoissonDirection a z) hz v u

end Burnett.V02
