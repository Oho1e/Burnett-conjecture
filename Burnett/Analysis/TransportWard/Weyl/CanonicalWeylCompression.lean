import Burnett.Analysis.TransportWard.Weyl.FrozenDensityNormalizationBinding
import Burnett.Analysis.TransportWard.Weyl.NormalizedHessianBracket

set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxRecDepth 1700

noncomputable section

namespace Burnett.V03.Palatini

open Function Set Bundle Burnett.RicciSymbol Burnett.Geometry Burnett.V02
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear UnitNullCompactness
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Bianchi.RayIdentification (coordinateHamiltonian canonicalBracket)
open scoped ContDiff Manifold Topology Matrix.Norms.Elementwise ComplexConjugate BigOperators

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot
local notation "J" => Fin 4 × Fin 4

private theorem differentiableAt_densityPrincipalPhase {ι : Type*} (S : ι → Mat) (G : E₀ → Mat)
    (z : Phase) (i j : ι)
    (hC : ∀ d : J, DifferentiableAt ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) z.1) :
    DifferentiableAt ℝ (fun p : Phase => frozenDensityPrincipalPhase S (G p.1) p.2 i j) z := by
  have hp (k : Fin 4) : DifferentiableAt ℝ (fun p : Phase => p.2 k) z :=
    (ContinuousLinearMap.proj k : Covector →L[ℝ] ℝ).differentiableAt.comp z differentiableAt_snd
  unfold frozenDensityPrincipalPhase
  exact DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
    ((hC (a,b)).comp z differentiableAt_fst).mul ((hp a).mul (hp b))

/-- The entrywise Poisson bracket of the same V03 Weyl principal matrix
is the previously verified phase derivative of its ordered Hermitian form. -/
theorem canonicalBracket_densityWeylPrincipalMatrix_pairing {ι : Type*} [Fintype ι]
    (S : ι → Mat) (G : E₀ → Mat) (z : Phase) (test : E₀ → Covector → ℝ) (u v : ι → ℂ)
    (hC : ∀ i j (d : J), DifferentiableAt ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) z.1) :
    (∑ i, ∑ j, (canonicalBracket (fun y p => frozenDensityPrincipalPhase S (G y) p i j) test z.1 z.2 : ℂ) *
        u j * conj (v i)) =
      fderiv ℝ (fun y : Phase => densityEulerPrincipalForm S (G y.1) y.2 u v) z (phasePoissonDirection test z) := by
  let A (i j : ι) (p : Phase) := frozenDensityPrincipalPhase S (G p.1) p.2 i j
  let D (i j : ι) := Complex.ofRealCLM.comp (fderiv ℝ (A i j) z)
  have hA (i j : ι) : DifferentiableAt ℝ (A i j) z := differentiableAt_densityPrincipalPhase S G z i j (hC i j)
  have hD (i j : ι) : HasFDerivAt (fun p => (A i j p : ℂ)) (D i j) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z (hA i j).hasFDerivAt
  have hSum := HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) =>
    HasFDerivAt.fun_sum fun j (_ : j ∈ Finset.univ) => ((hD i j).mul_const (u j)).mul_const (conj (v i))
  change _ = fderiv ℝ (fun p : Phase => ∑ i, ∑ j, (A i j p : ℂ) * u j * conj (v i)) z _
  rw [hSum.fderiv]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    D,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hey : fderiv ℝ (A i j) z (phasePoissonDirection test z) =
      canonicalBracket (fun y p => frozenDensityPrincipalPhase S (G y) p i j) test z.1 z.2 :=
    phasePoissonDirection_eq_canonicalBracket (fun (y : E₀) (p : Covector) =>
      frozenDensityPrincipalPhase S (G y) p i j) test z (hA i j)
  rw [hey]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]

theorem canonicalBracket_actualDensityWeylMatrix_pairing_RicciKernel
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : M) (p : CotangentBundle M) (hp : p.proj ∈ (chartAt E₀ c).source)
    (hξ : cotangentCoords c p ≠ 0) (u v : I → ℂ)
    (hU : ∀ i j, complexRicciSymbol
      (phaseInverse (chartLowerMetric B c) (chartAt E₀ c p.proj,cotangentCoords c p))
      (cotangentCoords c p) (assembleComplexMetricComponents orthonormalMetricDirection u) i j = 0)
    (hV : ∀ i j, complexRicciSymbol
      (phaseInverse (chartLowerMetric B c) (chartAt E₀ c p.proj,cotangentCoords c p))
      (cotangentCoords c p) (assembleComplexMetricComponents orthonormalMetricDirection v) i j = 0)
    (test : E₀ → Covector → ℝ) :
    let G := chartLowerMetric B c
    let z : Phase := (chartAt E₀ c p.proj,cotangentCoords c p)
    let U := assembleComplexMetricComponents orthonormalMetricDirection u
    let V := assembleComplexMetricComponents orthonormalMetricDirection v
    (∑ i, ∑ j, (canonicalBracket (fun y q => frozenDensityPrincipalPhase orthonormalMetricDirection (G y) q i j)
        test z.1 z.2 : ℂ) * u j * conj (v i)) =
      if dualEnergy B hSig.isNondegenerate p = 0 then
        4 * (phaseDensity G z : ℂ) * (canonicalBracket (coordinateHamiltonian G) test z.1 z.2 : ℂ) *
          physicalForm (phaseInverse G z) U V
      else 0 := by
  intro G z U V
  let e := chartAt E₀ c
  obtain ⟨hEntries,hDet,_⟩ := chartLowerMetric_phase_inputs B hB hSig.isNondegenerate hSig.isSymmetric c
  have hG : ContDiffOn ℝ ∞ G e.target := contDiffOn_pi.mpr (fun a => contDiffOn_pi.mpr (fun b => hEntries a b))
  have hz : z.1 ∈ e.target := e.mapsTo hp
  have hCoeff (i j : I) (d : J) :
      DifferentiableAt ℝ (fun y => metricActionCoefficient orthonormalMetricDirection
        (d.1,i) (d.2,j) (G y)) z.1 :=
    (((contDiffOn_metricActionCoefficient orthonormalMetricDirection (d.1,i) (d.2,j)).comp
      hG (fun y hy => hDet y hy)).contDiffAt (e.open_target.mem_nhds hz)).differentiableAt (by simp)
  rw [canonicalBracket_densityWeylPrincipalMatrix_pairing orthonormalMetricDirection G z test u v hCoeff]
  exact normalizedDensityEulerPrincipalForm_bracket_actualChart_RicciKernel B hB hSig c p hp hξ u v hU hV test

end Burnett.V03.Palatini
