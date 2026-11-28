import Burnett.Analysis.TransportWard.Weyl.HermitianHessianForm
import Burnett.Counterexamples.Bianchi.RayIdentification
import Burnett.Geometry.SmoothMetricConnection

/-! The actual smooth coordinate metric, density, and phase coefficients. -/

set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V02

open Function Filter Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.SmoothMetricConnection (contDiffOn_det contDiffOn_matrixInverse)
open Burnett.Analysis.TransportWardSymbol (Mat inverseMatrix metricDensity)
open Burnett.Bianchi.RayIdentification (coordinateHamiltonian canonicalBracket)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial momentumBasis)
open Burnett.V06 (einsteinDensitySymbol raiseBoth)
open scoped BigOperators ComplexConjugate ContDiff Matrix Topology

local notation "E" => CoordinateSpace

abbrev Phase := E × Covector

def phaseInverse (g : E → Mat) (z : Phase) : Tensor2 := inverseMatrix (g z.1)

def phaseDensity (g : E → Mat) (z : Phase) : ℝ := metricDensity (g z.1)

def phaseHamiltonian (g : E → Mat) (z : Phase) : ℝ := coordinateHamiltonian g z.1 z.2

def phaseEinsteinSymbol (g : E → Mat) (k : ComplexTensor2) (z : Phase) : ComplexTensor2 :=
  einsteinDensitySymbol (phaseInverse g z) (phaseDensity g z) z.2 k

def phaseHessianPairing (g : E → Mat) (k l : ComplexTensor2) (z : Phase) : ℂ :=
  hessianPairing (phaseInverse g z) (phaseDensity g z) z.2 k l

theorem phaseInverse_symmetric (g : E → Mat) (z : Phase) (hg : IsSymmetricTensor (g z.1)) :
    IsSymmetricTensor (phaseInverse g z) := by
  let m := g z.1
  have ht : mᵀ = m := by
    ext i j
    exact hg j i
  have hi : m⁻¹ᵀ = m⁻¹ := by rw [Matrix.transpose_nonsing_inv, ht]
  intro i j
  change m⁻¹ i j = m⁻¹ j i
  exact (congrFun (congrFun hi i) j).symm

theorem differentiableAt_phaseInverse_density (g : E → Mat) (U : Set E)
    (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U)
    (hn : ∀ x ∈ U, Matrix.det (g x) ≠ 0) (z : Phase) (hz : z.1 ∈ U) :
    (∀ i j, DifferentiableAt ℝ (fun y : Phase => phaseInverse g y i j) z) ∧
      DifferentiableAt ℝ (phaseDensity g) z := by
  have hnhood := hU.mem_nhds hz
  constructor
  · intro i j
    have hInv := (contDiffOn_matrixInverse g U hg hn i j).contDiffAt hnhood
    exact (hInv.differentiableAt (by simp)).comp z differentiableAt_fst
  · have hAbs := (contDiffOn_det g U hg).abs hn
    have hDensity := (hAbs.sqrt (fun x hx => abs_ne_zero.mpr (hn x hx))).contDiffAt hnhood
    exact (hDensity.differentiableAt (by simp)).comp z differentiableAt_fst

theorem differentiableAt_phaseMomentum (z : Phase) (i : Index) :
    DifferentiableAt ℝ (fun y : Phase => y.2 i) z :=
  differentiableAt_pi.mp (differentiableAt_snd : DifferentiableAt ℝ (Prod.snd : Phase → Covector) z) i

private theorem ofReal_differentiableAt {f : Phase → ℝ} {z : Phase}
    (hf : DifferentiableAt ℝ f z) : DifferentiableAt ℝ (fun y => (f y : ℂ)) z :=
  Complex.ofRealCLM.differentiableAt.comp z hf

private theorem conj_differentiableAt {f : Phase → ℂ} {z : Phase}
    (hf : DifferentiableAt ℝ f z) : DifferentiableAt ℝ (fun y => conj (f y)) z :=
  Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp z hf

theorem differentiableAt_phaseHamiltonian (g : E → Mat) (z : Phase)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y : Phase => phaseInverse g y i j) z) :
    DifferentiableAt ℝ (phaseHamiltonian g) z := by
  change DifferentiableAt ℝ (fun y : Phase => symbolNorm (phaseInverse g y) y.2 / 2) z
  simp only [symbolNorm, div_eq_mul_inv]
  refine (DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_).mul_const ((2 : ℝ)⁻¹)
  exact ((hB i j).mul (differentiableAt_phaseMomentum z i)).mul (differentiableAt_phaseMomentum z j)

private theorem differentiableAt_complexTrace (B : Phase → Tensor2) (z : Phase)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y : Phase => B y i j) z)
    (k : Phase → ComplexTensor2) (hk : ∀ i j, DifferentiableAt ℝ (fun y : Phase => k y i j) z) :
    DifferentiableAt ℝ (fun y : Phase => complexMetricTrace (B y) (k y)) z := by
  unfold complexMetricTrace
  exact DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ =>
    (ofReal_differentiableAt (hB i j)).mul (hk i j)

private theorem differentiableAt_complexContracted (B : Phase → Tensor2) (z : Phase)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y : Phase => B y i j) z)
    (k : Phase → ComplexTensor2) (hk : ∀ i j, DifferentiableAt ℝ (fun y : Phase => k y i j) z)
    (b : Index) : DifferentiableAt ℝ (fun y : Phase => complexContracted (B y) y.2 (k y) b) z := by
  unfold complexContracted raiseCovector
  refine DifferentiableAt.fun_sum fun i _ => ?_
  exact (ofReal_differentiableAt (DifferentiableAt.fun_sum fun j _ =>
    (hB i j).mul (differentiableAt_phaseMomentum z j))).mul (hk i b)

theorem differentiableAt_phaseGauge (g : E → Mat) (z : Phase)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y : Phase => phaseInverse g y i j) z)
    (k : ComplexTensor2) (i : Index) :
    DifferentiableAt ℝ (fun y : Phase => gaugeCovector (phaseInverse g y) y.2 k i) z := by
  have hk (i j : Index) : DifferentiableAt ℝ (fun _ : Phase => k i j) z := differentiableAt_const _
  simp only [gaugeCovector, div_eq_mul_inv]
  exact (differentiableAt_complexContracted (phaseInverse g) z hB _ hk i).sub
    (((differentiableAt_complexTrace (phaseInverse g) z hB _ hk).mul
      (ofReal_differentiableAt (differentiableAt_phaseMomentum z i))).mul_const ((2 : ℂ)⁻¹))

theorem differentiableAt_phasePhysical (g : E → Mat) (z : Phase)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y : Phase => phaseInverse g y i j) z)
    (k l : ComplexTensor2) :
    DifferentiableAt ℝ (fun y : Phase => physicalForm (phaseInverse g y) k l) z := by
  simp only [physicalForm, hermitianPhysicalPairing, div_eq_mul_inv]
  refine (DifferentiableAt.sub ?_ ?_).mul_const ((4 : ℂ)⁻¹)
  · exact DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ =>
      DifferentiableAt.fun_sum fun c _ => DifferentiableAt.fun_sum fun d _ =>
      (((ofReal_differentiableAt (hB i c)).mul (ofReal_differentiableAt (hB j d))).mul_const (k i j)).mul_const (conj (l c d))
  · have hTk := differentiableAt_complexTrace (phaseInverse g) z hB (fun _ => k)
      (fun i j => differentiableAt_const (k i j))
    have hTl := differentiableAt_complexTrace (phaseInverse g) z hB (fun _ => l)
      (fun i j => differentiableAt_const (l i j))
    exact (hTk.mul (conj_differentiableAt hTl)).mul_const ((2 : ℂ)⁻¹)

private theorem differentiableAt_phaseRicci (g : E → Mat) (z : Phase)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y : Phase => phaseInverse g y i j) z)
    (k : ComplexTensor2) (i j : Index) :
    DifferentiableAt ℝ (fun y : Phase => complexRicciSymbol (phaseInverse g y) y.2 k i j) z := by
  have hQ (b : Index) := differentiableAt_complexContracted (phaseInverse g) z hB (fun _ => k)
    (fun a b => differentiableAt_const (k a b)) b
  have hT := differentiableAt_complexTrace (phaseInverse g) z hB (fun _ => k)
    (fun a b => differentiableAt_const (k a b))
  have hS : DifferentiableAt ℝ (fun y : Phase => symbolNorm (phaseInverse g y) y.2) z := by
    unfold symbolNorm
    exact DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
      ((hB a b).mul (differentiableAt_phaseMomentum z a)).mul (differentiableAt_phaseMomentum z b)
  have hξ (b : Index) := ofReal_differentiableAt (differentiableAt_phaseMomentum z b)
  simp only [complexRicciSymbol, div_eq_mul_inv]
  exact ((((ofReal_differentiableAt hS).mul_const (k i j)).add
    (((hξ i).mul (hξ j)).mul hT)).sub ((hξ i).mul (hQ j)) |>.sub ((hξ j).mul (hQ i))).mul_const ((2 : ℂ)⁻¹)

theorem differentiableAt_phaseEinsteinSymbol (g : E → Mat) (z : Phase)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y : Phase => phaseInverse g y i j) z)
    (hw : DifferentiableAt ℝ (phaseDensity g) z) (k : ComplexTensor2) (i j : Index) :
    DifferentiableAt ℝ (fun y : Phase => phaseEinsteinSymbol g k y i j) z := by
  let R (y : Phase) := complexRicciSymbol (phaseInverse g y) y.2 k
  have hR (a b : Index) : DifferentiableAt ℝ (fun y : Phase => R y a b) z :=
    differentiableAt_phaseRicci g z hB k a b
  have hTrace := differentiableAt_complexTrace (phaseInverse g) z hB R hR
  change DifferentiableAt ℝ (fun y : Phase => (phaseDensity g y : ℂ) *
    (raiseBoth (phaseInverse g y) (R y) i j -
      (phaseInverse g y i j : ℂ) * complexMetricTrace (phaseInverse g y) (R y) / 2)) z
  refine (ofReal_differentiableAt hw).mul (DifferentiableAt.sub ?_ ?_)
  · unfold raiseBoth complexRaiseSecond
    exact DifferentiableAt.fun_sum fun a _ => (ofReal_differentiableAt (hB i a)).mul
      (DifferentiableAt.fun_sum fun b _ => (ofReal_differentiableAt (hB j b)).mul (hR a b))
  · simpa only [div_eq_mul_inv] using
      (((ofReal_differentiableAt (hB i j)).mul hTrace).mul_const ((2 : ℂ)⁻¹))

theorem differentiableAt_phaseHessianPairing (g : E → Mat) (z : Phase)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y : Phase => phaseInverse g y i j) z)
    (hw : DifferentiableAt ℝ (phaseDensity g) z) (k l : ComplexTensor2) :
    DifferentiableAt ℝ (phaseHessianPairing g k l) z := by
  change DifferentiableAt ℝ (fun y : Phase => ∑ i, ∑ j, phaseEinsteinSymbol g k y i j * conj (l i j)) z
  exact DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ =>
    (differentiableAt_phaseEinsteinSymbol g z hB hw k i j).mul_const (conj (l i j))

/-- Direction acting on the first slot of `{f,a}`. It is minus the canonical
Hamilton field of the second argument. -/
def phasePoissonDirection (a : E → Covector → ℝ) (z : Phase) : Phase :=
  (∑ i, basePartial i a z.1 z.2 • ((0 : E), momentumBasis i)) -
    ∑ i, momentumPartial i a z.1 z.2 • (Burnett.CubicExplicit.basis i, (0 : Covector))

private theorem basePartial_eq_phase_fderiv {a : E → Covector → ℝ} {z : Phase}
    (ha : DifferentiableAt ℝ (uncurry a) z) (i : Index) :
    basePartial i a z.1 z.2 = fderiv ℝ (uncurry a) z (Burnett.CubicExplicit.basis i, 0) := by
  have h := DFunLike.congr_fun (ha.hasFDerivAt.comp z.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)).fderiv (Burnett.CubicExplicit.basis i)
  exact h

private theorem momentumPartial_eq_phase_fderiv {a : E → Covector → ℝ} {z : Phase}
    (ha : DifferentiableAt ℝ (uncurry a) z) (i : Index) :
    momentumPartial i a z.1 z.2 = fderiv ℝ (uncurry a) z (0, momentumBasis i) := by
  have h := DFunLike.congr_fun (ha.hasFDerivAt.comp z.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)).fderiv (momentumBasis i)
  exact h

/-- This direction recovers the paper's canonical bracket with its sign. -/
theorem phasePoissonDirection_eq_canonicalBracket (P a : E → Covector → ℝ) (z : Phase)
    (hP : DifferentiableAt ℝ (uncurry P) z) :
    fderiv ℝ (uncurry P) z (phasePoissonDirection a z) = canonicalBracket P a z.1 z.2 := by
  simp only [phasePoissonDirection, map_sub, map_sum, map_smul, smul_eq_mul,
    ← basePartial_eq_phase_fderiv hP, ← momentumPartial_eq_phase_fderiv hP, canonicalBracket,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end Burnett.V02
