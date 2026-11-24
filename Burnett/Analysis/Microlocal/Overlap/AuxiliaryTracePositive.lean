import Burnett.Analysis.Microlocal.Overlap.ChartAmplitudeContractions
import Burnett.Geometry.CovariantTensorNorm
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Positive definiteness of the auxiliary Gram trace on positive amplitude covariances. -/

set_option autoImplicit false
set_option maxHeartbeats 640000

noncomputable section

namespace Burnett.F07.IntrinsicAmplitude

open Matrix Module Burnett.RicciSymbol
open LinearMap (BilinForm)
open Burnett.Geometry ConnectionDifference ManifoldMetric
open Burnett.Geometry.ContravariantTensor (tensorTangentBasis)
open Burnett.Geometry.IntrinsicScalarEinstein (inverseMetricTensor_isSymmetric)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryInverse)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (Pair)
open Burnett.Geometry.IntrinsicScalarEinstein (inverseMetricTensor)
open Burnett.Geometry.IntrinsicScalarEinstein (covariantForm)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity)
open scoped BigOperators ComplexOrder ContDiff Kronecker Manifold MatrixOrder

private def auxiliaryGram (R : Matrix Index Index ℝ) : Matrix Pair Pair ℂ :=
  (R ⊗ₖ R).map Complex.ofRealHom

private theorem auxiliaryTraceLinear_eq_trace_mul (R : Matrix Index Index ℝ) (hR : R.IsHermitian)
    (A : Matrix Pair Pair ℂ) :
    auxiliaryTraceLinear R A = (A * auxiliaryGram R).trace.re := by
  simp only [auxiliaryTraceLinear_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  rintro ⟨a,b⟩ _
  apply Finset.sum_congr rfl
  rintro ⟨c,d⟩ _
  have hac : R c a = R a c := by simpa only [star_trivial] using hR.apply a c
  have hbd : R d b = R b d := by simpa only [star_trivial] using hR.apply b d
  simp only [auxiliaryGram, Matrix.map_apply, kronecker_apply, Complex.ofRealHom_eq_coe,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hac, hbd, mul_comm]

private theorem auxiliaryGram_exists_factor (R : Matrix Index Index ℝ) (hR : R.PosDef) :
    ∃ U : Matrix Pair Pair ℂ, IsUnit U ∧ auxiliaryGram R = Uᴴ * U := by
  obtain ⟨S, hS, hRS⟩ := Matrix.posDef_iff_eq_conjTranspose_mul_self.mp hR
  let T : Matrix Pair Pair ℝ := S ⊗ₖ S
  let U : Matrix Pair Pair ℂ := T.map Complex.ofRealHom
  have hT : IsUnit T := CovariantTensorNorm.isUnit_kronecker_real S S hS hS
  have hTU : Uᴴ = Tᴴ.map Complex.ofRealHom := by
    ext i j
    simp only [U, conjTranspose_apply, Matrix.map_apply, star_trivial, Complex.ofRealHom_eq_coe,
      Complex.star_def, Complex.conj_ofReal]
  have hTT : Tᴴ * T = R ⊗ₖ R := by
    change (S ⊗ₖ S)ᴴ * (S ⊗ₖ S) = _
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← hRS]
  refine ⟨U, hT.map (Complex.ofRealHom.mapMatrix), ?_⟩
  rw [hTU]
  change (R ⊗ₖ R).map Complex.ofRealHom = Tᴴ.map Complex.ofRealHom * T.map Complex.ofRealHom
  rw [← Matrix.map_mul, hTT]

/-- For a positive definite auxiliary inverse and a positive covariance, the trace is
nonnegative and vanishes exactly when the whole complex covariance vanishes. -/
theorem auxiliaryTraceLinear_nonneg_and_eq_zero_iff (R : Matrix Index Index ℝ) (hR : R.PosDef)
    (A : Matrix Pair Pair ℂ) (hA : A.PosSemidef) :
    0 ≤ auxiliaryTraceLinear R A ∧ (auxiliaryTraceLinear R A = 0 ↔ A = 0) := by
  obtain ⟨U, hU, hGram⟩ := auxiliaryGram_exists_factor R hR
  have hTrace : auxiliaryTraceLinear R A = (U * A * Uᴴ).trace.re := by
    rw [auxiliaryTraceLinear_eq_trace_mul R hR.isHermitian A, hGram, Matrix.trace_mul_cycle',
      ← Matrix.mul_assoc]
  have hCov : (U * A * Uᴴ).PosSemidef := hA.mul_mul_conjTranspose_same U
  have hNonneg := Complex.nonneg_iff.mp hCov.trace_nonneg
  refine ⟨hTrace.symm ▸ hNonneg.1, ⟨?_, fun h => h.symm ▸ map_zero (auxiliaryTraceLinear R)⟩⟩
  intro h
  have hZeroTrace : (U * A * Uᴴ).trace = 0 := Complex.ext (hTrace.symm.trans h) hNonneg.2.symm
  have hZero := hCov.trace_eq_zero_iff.mp hZeroTrace
  have hU' : IsUnit Uᴴ := isUnit_star.mpr hU
  apply hU.mul_right_inj.mp
  apply hU'.mul_left_inj.mp
  simpa only [mul_zero, zero_mul] using hZero

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The inverse auxiliary matrix in any actual dual basis is positive definite. -/
theorem auxiliaryInverse_entries_posDef (r : Metric (M := M)) (x : M)
    (b : Basis Index ℝ (TangentSpace Model x)) :
    Matrix.PosDef (fun i j => inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r) x
      (b.dualBasis i) (b.dualBasis j)) := by
  let hn := GlobalLeviCivita.inner_nondegenerate r
  let H := inverseMetricTensor r.inner hn x
  have hSym : H.IsSymm := inverseMetricTensor_isSymmetric r.inner hn r.symm x
  have hMat : (fun i j => H (b.dualBasis i) (b.dualBasis j) : Matrix Index Index ℝ) =
      BilinForm.toMatrix b.dualBasis H := by
    ext i j
    rw [BilinForm.toMatrix_apply]
  rw [show (fun i j => inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r) x
    (b.dualBasis i) (b.dualBasis j)) = _ from hMat]
  refine ⟨Matrix.IsHermitian.ext (fun i j => ?_), fun u hu => ?_⟩
  · simp only [star_trivial, BilinForm.toMatrix_apply]
    exact hSym.eq _ _
  · simp only [star_trivial]
    rw [BilinForm.dotProduct_toMatrix_mulVec]
    let α := b.dualBasis.equivFun.symm u
    let sharp := FiberMetric.sharp (covariantForm r.inner x) (hn x)
      (tensorTangentBasis x x (mem_chart_source CoordinateSpace x))
    have hα : α ≠ 0 := by
      intro h
      apply hu
      exact b.dualBasis.equivFun.symm.injective (h.trans (map_zero _).symm)
    change 0 < r.inner x (sharp α) (sharp α)
    apply r.pos
    exact fun h => hα (sharp.injective (h.trans (map_zero sharp).symm))

/-- If the actual tensor has a positive ordered component matrix, its intrinsic trace
vanishes precisely when the tensor at that point vanishes. -/
theorem intrinsicAuxiliaryTrace_nonneg_and_eq_zero_iff (r : Metric (M := M))
    (J : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (b : Basis Index ℝ (TangentSpace Model (projection p)))
    (hJ : Matrix.PosSemidef (fun i j : Pair => J p ![b i.1, b i.2, b j.1, b j.2])) :
    0 ≤ intrinsicAuxiliaryTrace r J p ∧ (intrinsicAuxiliaryTrace r J p = 0 ↔ J p = 0) := by
  let R : Matrix Index Index ℝ := fun i j =>
    inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r) (projection p) (b.dualBasis i) (b.dualBasis j)
  let A : Matrix Pair Pair ℂ := fun i j => J p ![b i.1, b i.2, b j.1, b j.2]
  rw [intrinsicAuxiliaryTrace_eq_basis r J p b]
  change 0 ≤ auxiliaryTraceLinear R A ∧ (auxiliaryTraceLinear R A = 0 ↔ J p = 0)
  obtain ⟨hNonneg, hZero⟩ := auxiliaryTraceLinear_nonneg_and_eq_zero_iff R
    (auxiliaryInverse_entries_posDef r (projection p) b) A hJ
  refine ⟨hNonneg, hZero.trans ⟨?_, ?_⟩⟩
  · intro hA
    apply Module.Basis.ext_multilinear (fun _ : Fin 4 => b)
    intro v
    have hv : (fun i => b (v i)) = ![b (v 0), b (v 1), b (v 2), b (v 3)] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact congrArg (fun C : Matrix Pair Pair ℂ => C (v 0, v 1) (v 2, v 3)) hA
  · intro hJ0
    ext i j
    change J p ![b i.1, b i.2, b j.1, b j.2] = 0
    rw [hJ0]
    rfl

theorem chartAuxiliaryTraceLinear_nonneg_and_eq_zero_iff (r : Metric (M := M))
    (q : CompactChartInput M) (z : Chart q.ball) (A : Matrix Pair Pair ℂ) (hA : A.PosSemidef) :
    0 ≤ auxiliaryTraceLinear (chartAuxiliaryInverse r q z.1) A ∧
      (auxiliaryTraceLinear (chartAuxiliaryInverse r q z.1) A = 0 ↔ A = 0) :=
  auxiliaryTraceLinear_nonneg_and_eq_zero_iff _ (chartAuxiliaryInverse_posDef r q z) A hA

end Burnett.F07.IntrinsicAmplitude
