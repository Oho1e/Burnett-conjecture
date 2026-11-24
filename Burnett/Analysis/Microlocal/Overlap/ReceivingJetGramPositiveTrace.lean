import Burnett.Analysis.Microlocal.Overlap.AtlasJetOperatorNaturality
import Burnett.Analysis.Microlocal.Overlap.AuxiliaryTracePositive

/-! Positivity and trace of the covariance endomorphism in the auxiliary metric. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2500000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.IntrinsicScalarEinstein (covariantForm inverseMetricTensor)
open Burnett.Geometry.InverseField (matrixInverse matrixInverse_covariant)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity chartTangentBasis components components_apply)
open Burnett.F07.IntrinsicAmplitude (intrinsicAuxiliaryTrace intrinsicAuxiliaryTrace_eq_basis
  auxiliaryTraceInBasis auxiliaryTraceLinear)
open Burnett.Microlocal.CurlDensity (JetSlot Pair gradientEmbedding)
open scoped ComplexOrder ContDiff Kronecker Manifold Matrix

open private auxiliaryGram auxiliaryTraceLinear_eq_trace_mul
  from Burnett.Analysis.Microlocal.Overlap.AuxiliaryTracePositive

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem atlasCovectorGram_isHermitian (r : Metric (M := M)) (c : AtlasChart M) (x : M)
    (hx : x ∈ c.chart.source) : (atlasCovectorGram r c x).IsHermitian := by
  let H : Matrix Index Index ℝ := metricComponents (fixedForm r.inner c) (c.chart x)
  have hH : H.PosDef := fixedRiemannian_posDef r c (c.chart.mapsTo hx)
  have hInv : (H⁻¹)ᵀ = H⁻¹ := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hH.isHermitian.inv
  change (Complex.ofRealHom.mapMatrix H⁻¹)ᴴ = Complex.ofRealHom.mapMatrix H⁻¹
  rw [complexified_realMatrix_conjTranspose, hInv]

/-- The amplitude Gram trace recovers the actual scalar auxiliary trace. -/
theorem intrinsicAuxiliaryTrace_eq_gramOperatorTrace (r : Metric (M := M))
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (b : Module.Basis Index ℝ (TangentSpace Model (projection p))) :
    let R := unitCosphereCovectorGram r p b
    intrinsicAuxiliaryTrace r A p = (components b (A p) * (R ⊗ₖ R)).trace.re := by
  intro R
  let g := covariantForm r.inner (projection p)
  let hn : g.Nondegenerate := GlobalLeviCivita.inner_nondegenerate r (projection p)
  let H : Matrix Index Index ℝ := FiberMetric.covariant g b
  let Q : Matrix Index Index ℝ := H⁻¹
  letI : FiniteDimensional ℝ (TangentSpace Model (projection p)) := Module.Finite.of_basis b
  have hSym : g.IsSymm := ⟨fun x y => r.symm (projection p) x y⟩
  have hH : H.IsHermitian := by
    change Hᴴ = H
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact r.symm (projection p) (b j) (b i)
  have hEntry (i j : Index) :
      inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r) (projection p)
        (b.dualBasis i) (b.dualBasis j) = Q i j := by
    change fiberInverseForm g hn (b.dualBasis i) (b.dualBasis j) = _
    exact (fiberInverseForm_eq_contravariant g hn b i j).trans
      (congrFun (congrFun (matrixInverse_covariant g hn hSym b).symm i) j)
  have hGram : auxiliaryGram Q = R ⊗ₖ R := by
    ext i j
    change ((Q i.1 j.1 * Q i.2 j.2 : ℝ) : ℂ) = (Q i.1 j.1 : ℂ) * (Q i.2 j.2 : ℂ)
    exact Complex.ofReal_mul _ _
  rw [intrinsicAuxiliaryTrace_eq_basis r A p b, auxiliaryTraceInBasis]
  have hE : (fun i j => inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r) (projection p)
    (b.dualBasis i) (b.dualBasis j)) = (Q : Tensor2) := funext fun i => funext fun j => hEntry i j
  have hC : (fun i j => (A p) ![b i.1, b i.2, b j.1, b j.2] : Matrix Pair Pair ℂ) = components b (A p) := by
    ext i j
    exact (components_apply b (A p) i j).symm
  rw [hE, hC, auxiliaryTraceLinear_eq_trace_mul Q hH.inv, hGram]

/-- On the unit cosphere the actual jet endomorphism has the trace of the
amplitude endomorphism, because insertion has the Gram adjoint as left inverse. -/
theorem atlasJetCovarianceOperator_trace_re {r : Metric (M := M)} (c : AtlasChart M)
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r) (hp : projection p ∈ c.chart.source) :
    (atlasJetCovarianceOperator c A p).trace.re = intrinsicAuxiliaryTrace r A p := by
  let b := chartTangentBasis c (projection p) hp
  let R := unitCosphereCovectorGram r p b
  let S := unitCosphereCovariantGram r p b
  let G := R ⊗ₖ R
  let H := R ⊗ₖ G
  let J := gradientEmbedding (FiberMetric.covector b p.val.2.toLinearMap)
  let D := (S ⊗ₖ S) * Jᴴ * H
  let T := components b (A p) * G
  have hFactor : atlasJetCovarianceOperator c A p = (J * T) * D :=
    (atlasJetCovarianceOperator_in_fiber c A p hp).trans (unitCosphere_jetCovariance_operator r A p b)
  have hLeft : D * J = 1 := unitCosphere_gradientEmbedding_adjoint_mul r p b
  calc
    _ = (((J * T) * D).trace).re := by rw [hFactor]
    _ = (((D * J) * T).trace).re := by rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    _ = _ := by rw [hLeft, Matrix.one_mul, intrinsicAuxiliaryTrace_eq_gramOperatorTrace r A p b]

variable [T2Space M] [MeasurableSpace M] [BorelSpace M]

/-- Multiplying the actual jet endomorphism on the left by its Gram gives
the positive semidefinite form. The trace is one on the original control. -/
theorem ae_original_atlasJetCovarianceOperator_gramPositive_unitTrace
    (r : Metric (M := M)) (B : ManifoldBilinear.Field (M := M)) (g : ℕ → ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hg : ∀ n, ManifoldBilinear.IsSmooth (g n))
    (hnB : ManifoldBilinear.IsNondegenerate B) (σ : ℕ → ℕ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) {K : Set M} (hK : IsCompact K) (hKc : K ⊆ c.chart.source) :
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K),
      let H := atlasJetGram r c (projection p)
      let O := atlasJetCovarianceOperator c A.density p
      (H * O).PosSemidef ∧ Oᴴ * H = H * O ∧ O.trace.re = 1 := by
  have hWin := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  filter_upwards [ae_restrict_of_ae hA.2.2.2.2.2, ae_restrict_mem (μ := A.control) hWin] with p hp hLoc
  intro H O
  let b := chartTangentBasis c (projection p) (hKc hLoc)
  let C := atlasJetCovarianceMatrix c A.density p
  have hCEq : C = jetAmplitudeComponents b (intrinsicJetAmplitude A.density p) := by
    ext i j
    change atlasIntrinsicJetComponent c A.density p i j = _
    rw [atlasIntrinsicJetComponent, dif_pos (hKc hLoc)]
  have hC : C.PosSemidef := by
    rw [hCEq]
    exact jetAmplitudeComponents_posSemidef b p.val.2.toLinearMap (A.density p) (hp.2.1 b)
  have hH : Hᴴ = H := by
    change (atlasJetGram r c (projection p))ᴴ = atlasJetGram r c (projection p)
    simp only [atlasJetGram, Matrix.conjTranspose_kronecker, (atlasCovectorGram_isHermitian r c _ (hKc hLoc)).eq]
  have hPositive : (H * O).PosSemidef := by
    change (H * (C * H)).PosSemidef
    simpa only [hH, Matrix.mul_assoc] using hC.conjTranspose_mul_mul_same H
  refine ⟨hPositive, ?_, (atlasJetCovarianceOperator_trace_re c A.density p (hKc hLoc)).trans hp.1⟩
  simpa only [Matrix.conjTranspose_mul, hH] using hPositive.isHermitian.eq

end Burnett.Microlocal.Overlap
