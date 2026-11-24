import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetEndomorphism
import Burnett.Analysis.Microlocal.Overlap.OriginalVacuumIntrinsicAmplitude

/-! The covariance acts on the actual symmetric jet fiber. -/
set_option autoImplicit false
set_option maxRecDepth 4200
set_option maxHeartbeats 2700000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Module Matrix MeasureTheory Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity chartTangentBasis components components_apply)
open Burnett.Microlocal.CurlDensity (JetSlot gradient_factor_entry)
open scoped ContDiff Manifold Matrix Kronecker

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The trilinear description of the complexified covariant jet with a symmetric last pair. -/
def complexSymmetricJet (V : Type*) [AddCommGroup V] [Module ℝ V] :
    Submodule ℂ (ComplexCovariantJet V) where
  carrier := {F | ∀ u v w, F u v w = F u w v}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun hF hG u v w => congrArg₂ (· + ·) (hF u v w) (hG u v w)
  smul_mem' := fun c _ hF u v w => congrArg (c • ·) (hF u v w)

theorem mem_complexSymmetricJet_of_coordinates (b : Basis Index ℝ V) (F : ComplexCovariantJet V)
    (h : ∀ i j k : Index, jetFiberCoordinates b F (i, j, k) = jetFiberCoordinates b F (i, k, j)) :
    F ∈ complexSymmetricJet V := by
  let flip : ComplexBilinearForm V →ₗ[ℝ] ComplexBilinearForm V := LinearMap.lflip.toLinearMap
  have hEq : F = flip.comp F := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    apply b.ext
    intro k
    exact h i j k
  intro u v w
  exact LinearMap.congr_fun₂ (LinearMap.congr_fun hEq u) v w

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The original operator maps the entire ordered jet fiber into the actual symmetric subspace. -/
theorem intrinsicJetCovarianceEndomorphism_mem_symmetric {r : Metric (M := M)}
    {B : Field (M := M)} {hn : IsNondegenerate B} {A : AmplitudeCovarianceDensity r} {p : Cosphere r}
    (h : HasIntrinsicAmplitudeRicciKernel r B hn A p) (F : ComplexCovariantJet (TangentSpace Model (projection p))) :
    intrinsicJetCovarianceEndomorphism A p F ∈ complexSymmetricJet (TangentSpace Model (projection p)) := by
  let x := projection p
  let c := AtlasChart.atPoint x
  have hx : x ∈ c.chart.source := mem_chart_source CoordinateSpace x
  let b := chartTangentBasis c x hx
  have hCoords := intrinsicJetCovarianceEndomorphism_coordinates A p c hx F
  have hOp := atlasJetCovarianceOperator_in_fiber c A p hx
  dsimp only at hCoords hOp
  apply mem_complexSymmetricJet_of_coordinates b
  intro i j k
  rw [hCoords, hOp, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, intrinsicJetAmplitude, jetAmplitudeComponents_insertJetCovectors,
    gradient_factor_entry, components_apply]
  apply Finset.sum_congr rfl
  intro q _
  have hSlice : A p ![b j, b k, b q.2.1, b q.2.2] = A p ![b k, b j, b q.2.1, b q.2.2] :=
    (h (b q.2.1) (b q.2.2)).1 (b j) (b k)
  rw [hSlice]

/-- Restrict to the symmetric jet fiber without changing the action on any symmetric input. -/
def symmetricJetCovarianceEndomorphism {r : Metric (M := M)}
    {B : Field (M := M)} {hn : IsNondegenerate B} {A : AmplitudeCovarianceDensity r} {p : Cosphere r}
    (h : HasIntrinsicAmplitudeRicciKernel r B hn A p) :
    End ℂ (complexSymmetricJet (TangentSpace Model (projection p))) :=
  ((intrinsicJetCovarianceEndomorphism A p).comp (complexSymmetricJet (TangentSpace Model (projection p))).subtype)
    |>.codRestrict _ (fun F => intrinsicJetCovarianceEndomorphism_mem_symmetric h F)

theorem symmetricJetCovarianceEndomorphism_coe {r : Metric (M := M)}
    {B : Field (M := M)} {hn : IsNondegenerate B} {A : AmplitudeCovarianceDensity r} {p : Cosphere r}
    (h : HasIntrinsicAmplitudeRicciKernel r B hn A p)
    (F : complexSymmetricJet (TangentSpace Model (projection p))) :
    (symmetricJetCovarianceEndomorphism h F : ComplexCovariantJet (TangentSpace Model (projection p))) =
      intrinsicJetCovarianceEndomorphism A p F := rfl

/-- Symmetry holds simultaneously for all ordered jets on the original auxiliary control. -/
theorem ae_original_intrinsicJetCovarianceEndomorphism_mem_symmetric
    {r : Metric (M := M)} {B : Field (M := M)} {g : ℕ → Field (M := M)}
    {hB : IsSmooth B} {hg : ∀ n, IsSmooth (g n)} {hn : IsNondegenerate B}
    {σ : ℕ → ℕ} {A : IntrinsicAmplitudeCovariance r} (hA : HasOriginalIntrinsicAmplitude r B g hB hg hn σ A) :
    ∀ᵐ p ∂A.control, ∀ F : ComplexCovariantJet (TangentSpace Model (projection p)),
      intrinsicJetCovarianceEndomorphism A.density p F ∈ complexSymmetricJet (TangentSpace Model (projection p)) :=
  hA.2.2.2.2.2.mono fun _ hp F => intrinsicJetCovarianceEndomorphism_mem_symmetric hp.2.2 F

end Burnett.Microlocal.Overlap
