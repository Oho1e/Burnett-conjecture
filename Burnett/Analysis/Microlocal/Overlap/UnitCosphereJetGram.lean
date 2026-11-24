import Burnett.Analysis.Microlocal.Overlap.JetCovarianceOperatorGram
import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetAmplitudeTensor
import Burnett.Geometry.Cotangent.CosphereMeasure
import Burnett.Geometry.IntrinsicScalarEinstein

/-! The derivative embedding on the actual auxiliary unit cosphere is a Gram isometry. -/

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 850000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric UnitNullCompactness
open Burnett.Geometry.InverseField (matrixInverse det_covariant_ne_zero)
open Burnett.Geometry.IntrinsicScalarEinstein (covariantForm)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity components)
open UnitCosphere (Cosphere projection)
open Burnett.Microlocal.CurlDensity (Pair gradientEmbedding)
open scoped Manifold ContDiff Matrix Kronecker BigOperators

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The actual inverse auxiliary Gram matrix in an arbitrary real basis of
the tangent fiber, complexified for the Hermitian covariance. -/
def unitCosphereCovectorGram (r : Metric (M := M)) (p : Cosphere r)
    (b : Module.Basis Index ℝ (TangentSpace Model (projection p))) : Matrix Index Index ℂ :=
  let H : Matrix Index Index ℝ := FiberMetric.covariant (covariantForm r.inner (projection p)) b
  Complex.ofRealHom.mapMatrix H⁻¹

/-- At the actual r-unit covector the Gram norm is exactly one. -/
theorem unitCosphereCovectorGram_norm (r : Metric (M := M)) (p : Cosphere r)
    (b : Module.Basis Index ℝ (TangentSpace Model (projection p))) :
    let R := unitCosphereCovectorGram r p b
    let ξ := FiberMetric.covector b p.val.2.toLinearMap
    (∑ a : Index, ∑ d : Index, (ξ a : ℂ) * R a d * (ξ d : ℂ)) = 1 := by
  intro R ξ
  let R₀ := matrixInverse (FiberMetric.covariant (covariantForm r.inner (projection p)) b)
  have hReal : symbolNorm R₀ ξ = 1 := by
    have h := dualEnergy_in_basis r.inner (GlobalLeviCivita.inner_nondegenerate r) r.symm p.val b
    exact h.symm.trans p.property
  calc
    _ = (symbolNorm R₀ ξ : ℂ) := by
      simp only [symbolNorm, Complex.ofReal_sum, Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro d _
      change (ξ a : ℂ) * (R₀ a d : ℂ) * (ξ d : ℂ) = _
      ring
    _ = 1 := by rw [hReal, Complex.ofReal_one]

/-- The derivative insertion is isometric in the actual auxiliary Gram form
on the unit cosphere. The two undifferentiated ordered slots retain their
tensor Gram. -/
theorem unitCosphere_gradientEmbedding_gram (r : Metric (M := M)) (p : Cosphere r)
    (b : Module.Basis Index ℝ (TangentSpace Model (projection p))) :
    let R := unitCosphereCovectorGram r p b
    let ξ := FiberMetric.covector b p.val.2.toLinearMap
    let J := gradientEmbedding ξ
    Jᴴ * (R ⊗ₖ (R ⊗ₖ R)) * J = R ⊗ₖ R := by
  intro R ξ J
  exact gradientEmbedding_isometry_gram ξ R (R ⊗ₖ R) (unitCosphereCovectorGram_norm r p b)

def unitCosphereCovariantGram (r : Metric (M := M)) (p : Cosphere r)
    (b : Module.Basis Index ℝ (TangentSpace Model (projection p))) : Matrix Index Index ℂ :=
  Complex.ofRealHom.mapMatrix (FiberMetric.covariant (covariantForm r.inner (projection p)) b)

/-- The covariant matrix is the inverse of the auxiliary Gram on covectors. -/
theorem unitCosphere_gram_mul_covariant (r : Metric (M := M)) (p : Cosphere r)
    (b : Module.Basis Index ℝ (TangentSpace Model (projection p))) :
    unitCosphereCovectorGram r p b * unitCosphereCovariantGram r p b = 1 := by
  let form := covariantForm r.inner (projection p)
  let H : Matrix Index Index ℝ := FiberMetric.covariant form b
  have hFormN : form.Nondegenerate := fun u hu => GlobalLeviCivita.inner_nondegenerate r (projection p) u hu
  have hFormS : form.IsSymm := ⟨fun u v => r.symm (projection p) u v⟩
  have hH : IsUnit H.det := isUnit_iff_ne_zero.mpr (det_covariant_ne_zero form hFormN hFormS b)
  have hMapped := congrArg Complex.ofRealHom.mapMatrix (Matrix.nonsing_inv_mul H hH)
  simpa only [unitCosphereCovectorGram, unitCosphereCovariantGram, H, form, map_mul, map_one] using hMapped

private theorem unitCosphere_tensorGram_mul_covariant (r : Metric (M := M)) (p : Cosphere r)
    (b : Module.Basis Index ℝ (TangentSpace Model (projection p))) :
    let R := unitCosphereCovectorGram r p b
    let S := unitCosphereCovariantGram r p b
    (R ⊗ₖ R) * (S ⊗ₖ S) = 1 := by
  intro R S
  rw [← Matrix.mul_kronecker_mul, unitCosphere_gram_mul_covariant r p b, Matrix.one_kronecker_one]

/-- The actual Gram adjoint is a left inverse of covector insertion. -/
theorem unitCosphere_gradientEmbedding_adjoint_mul (r : Metric (M := M)) (p : Cosphere r)
    (b : Module.Basis Index ℝ (TangentSpace Model (projection p))) :
    let R := unitCosphereCovectorGram r p b
    let S := unitCosphereCovariantGram r p b
    let G := R ⊗ₖ R
    let H := R ⊗ₖ G
    let J := gradientEmbedding (FiberMetric.covector b p.val.2.toLinearMap)
    ((S ⊗ₖ S) * Jᴴ * H) * J = 1 := by
  intro R S G H J
  have hGram : Jᴴ * H * J = G := unitCosphere_gradientEmbedding_gram r p b
  have hInv : G * (S ⊗ₖ S) = 1 := unitCosphere_tensorGram_mul_covariant r p b
  calc
    _ = (S ⊗ₖ S) * (Jᴴ * H * J) := by simp only [Matrix.mul_assoc]
    _ = (S ⊗ₖ S) * G := by rw [hGram]
    _ = 1 := Matrix.mul_eq_one_comm.mp hInv

/-- The actual jet covariance operator is the amplitude covariance operator
conjugated by covector insertion and its auxiliary Gram adjoint. -/
theorem unitCosphere_jetCovariance_operator
    (r : Metric (M := M)) (A : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (b : Module.Basis Index ℝ (TangentSpace Model (projection p))) :
    let R := unitCosphereCovectorGram r p b
    let S := unitCosphereCovariantGram r p b
    let G := R ⊗ₖ R
    let H := R ⊗ₖ G
    let ξ := FiberMetric.covector b p.val.2.toLinearMap
    let J := gradientEmbedding ξ
    jetAmplitudeComponents b (intrinsicJetAmplitude A p) * H =
      J * (components b (A p) * G) * ((S ⊗ₖ S) * Jᴴ * H) := by
  intro R S G H ξ J
  have hInv : G * (S ⊗ₖ S) = 1 := unitCosphere_tensorGram_mul_covariant r p b
  have hJet : jetAmplitudeComponents b (intrinsicJetAmplitude A p) = J * components b (A p) * Jᴴ :=
    jetAmplitudeComponents_insertJetCovectors b p.val.2.toLinearMap (A p)
  rw [hJet]
  calc
    _ = J * (components b (A p) * ((1 : Matrix Pair Pair ℂ) * (Jᴴ * H))) := by simp [Matrix.mul_assoc]
    _ = _ := by rw [← hInv]; simp only [Matrix.mul_assoc]

end Burnett.Microlocal.Overlap
