import Burnett.Analysis.Microlocal.Overlap.ReceivingJetOperatorEntries

/-! Passing ordered coordinate row equations to the raised jet operator. -/

set_option autoImplicit false
set_option maxRecDepth 3800

noncomputable section

namespace Burnett.Microlocal.Overlap

open Set Filter MeasureTheory Matrix Burnett.Geometry
open ConnectionDifference ManifoldMetric MaximalChart
open UnitCosphere (Cosphere projection)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold Matrix Kronecker

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M]

/-- Each row is supplied in the operator-second convention. On the support
where its common localization factor is nonzero, the actual Gram-raised
density has range in the kernel of the corresponding coordinate matrix. -/
theorem ae_receivingJetOperator_kernel_of_scaled_ordered_rows {r : Metric (M := M)}
    {Rows : Type*} [Fintype Rows] (c : AtlasChart M) (A : IntrinsicAmplitudeCovariance r)
    {K : Set M} (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (P : Cosphere r → Matrix Rows JetSlot ℂ) (factor : Cosphere r → ℂ)
    (hRows : ∀ s : Rows, ∀ᵐ p ∂A.control.restrict (projection ⁻¹' K),
      (factor p • P p s) ᵥ* ((fun i j => atlasOrderedJetEntry c A.density p i j) : Matrix JetSlot JetSlot ℂ)ᵀ = 0) :
    ∀ᵐ p ∂A.control.restrict (projection ⁻¹' K), factor p ≠ 0 →
      P p * atlasJetCovarianceOperator c A.density p = 0 ∧
      ∀ w : JetSlot → ℂ, P p *ᵥ (atlasJetCovarianceOperator c A.density p *ᵥ w) = 0 := by
  have hW : MeasurableSet (projection ⁻¹' K : Set (Cosphere r)) :=
    measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  filter_upwards [(ae_all_iff.mpr hRows), ae_restrict_mem (μ := A.control) hW] with p hp hMem hFactor
  let C : Matrix JetSlot JetSlot ℂ := fun i j => atlasIntrinsicJetComponent c A.density p i j
  have hTranspose : ((fun i j => atlasOrderedJetEntry c A.density p i j) : Matrix JetSlot JetSlot ℂ)ᵀ = C := by
    ext i j
    exact (atlasIntrinsicJetComponent_eq_ordered c A.density p (hKc hMem) i j).symm
  have hPC : P p * C = 0 := by
    ext s j
    have hEquation := hp s
    rw [hTranspose, Matrix.smul_vecMul] at hEquation
    have hEntry := congrFun hEquation j
    change factor p * ((P p s) ᵥ* C) j = 0 at hEntry
    exact (mul_eq_zero.mp hEntry).resolve_left hFactor
  have hRaised : P p * atlasJetCovarianceOperator c A.density p = 0 := by
    let R := atlasCovectorGram r c (projection p)
    change P p * (C * (R ⊗ₖ (R ⊗ₖ R))) = 0
    rw [← Matrix.mul_assoc, hPC, Matrix.zero_mul]
  refine ⟨hRaised, fun w => ?_⟩
  rw [Matrix.mulVec_mulVec, hRaised, Matrix.zero_mulVec]

end Burnett.Microlocal.Overlap
