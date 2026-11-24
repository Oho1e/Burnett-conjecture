import Burnett.Analysis.Microlocal.Overlap.IntrinsicSymmetricJet

/-! Orthogonal symmetric restriction of the original ordered jet operator. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 3000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Module Matrix MeasureTheory Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity chartTangentBasis components components_apply)
open Burnett.Microlocal.CurlDensity (JetSlot gradient_factor_entry)
open scoped ComplexOrder ContDiff Manifold Matrix Kronecker

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Interchange the last two covariant slots. -/
def swapComplexCovariantJet (V : Type*) [AddCommGroup V] [Module ℝ V] : End ℂ (ComplexCovariantJet V) where
  toFun F := (LinearMap.lflip : ComplexBilinearForm V ≃ₗ[ℝ] ComplexBilinearForm V).toLinearMap.comp F
  map_add' _ _ := by ext x y z; rfl
  map_smul' _ _ := by ext x y z; rfl

/-- Symmetrization is the mean of the identity and exchange of the last pair. -/
def projectComplexSymmetricJet (V : Type*) [AddCommGroup V] [Module ℝ V] :
    ComplexCovariantJet V →ₗ[ℂ] complexSymmetricJet V :=
  ((2 : ℂ)⁻¹ • (LinearMap.id + swapComplexCovariantJet V)).codRestrict _ (by
    intro F x y z
    change (2 : ℂ)⁻¹ * (F x y z + F x z y) = (2 : ℂ)⁻¹ * (F x z y + F x y z)
    rw [add_comm (F x y z)])

theorem coe_projectComplexSymmetricJet_of_mem (F : ComplexCovariantJet V) (hF : F ∈ complexSymmetricJet V) :
    (projectComplexSymmetricJet V F : ComplexCovariantJet V) = F := by
  ext x y z
  change (2 : ℂ)⁻¹ * (F x y z + F x z y) = F x y z
  rw [← hF x y z]
  ring

def jetPairSwap : Equiv.Perm JetSlot := Equiv.prodCongr (Equiv.refl Index) (Equiv.prodComm Index Index)

theorem jetFiberCoordinates_swap (b : Basis Index ℝ V) (F : ComplexCovariantJet V) (i : JetSlot) :
    jetFiberCoordinates b (swapComplexCovariantJet V F) i = jetFiberCoordinates b F (jetPairSwap i) := rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Raising the input indices with the actual Gram still makes both input
slots symmetric. The Gram contains the same covector form on each of the two slots. -/
theorem atlasJetCovarianceOperator_input_swap {r : Metric (M := M)}
    {B : Field (M := M)} {hn : IsNondegenerate B} {A : AmplitudeCovarianceDensity r} {p : Cosphere r}
    (h : HasIntrinsicAmplitudeRicciKernel r B hn A p) (c : AtlasChart M) (hc : projection p ∈ c.chart.source)
    (hPos : (components (chartTangentBasis c (projection p) hc) (A p)).PosSemidef) (i j : JetSlot) :
    atlasJetCovarianceOperator c A p i (jetPairSwap j) = atlasJetCovarianceOperator c A p i j := by
  let b := chartTangentBasis c (projection p) hc
  let C := jetAmplitudeComponents b (intrinsicJetAmplitude A p)
  let R := unitCosphereCovectorGram r p b
  let G := R ⊗ₖ (R ⊗ₖ R)
  have hOut (k l : JetSlot) : C (jetPairSwap k) l = C k l := by
    have hSlice : A p ![b k.2.2, b k.2.1, b l.2.1, b l.2.2] = A p ![b k.2.1, b k.2.2, b l.2.1, b l.2.2] :=
      (h (b l.2.1) (b l.2.2)).1 (b k.2.2) (b k.2.1)
    simp only [C, intrinsicJetAmplitude, jetAmplitudeComponents_insertJetCovectors, gradient_factor_entry,
      components_apply]
    exact congrArg (fun a => (p.val.2 (b k.1) : ℂ) * (p.val.2 (b l.1) : ℂ) * a) hSlice
  have hSelf : C.IsHermitian := (jetAmplitudeComponents_posSemidef b p.val.2.toLinearMap (A p) hPos).isHermitian
  have hIn (k l : JetSlot) : C k (jetPairSwap l) = C k l := by
    rw [← hSelf.apply k (jetPairSwap l), hOut, hSelf.apply k l]
  have hG (k l : JetSlot) : G (jetPairSwap k) (jetPairSwap l) = G k l := by
    change R k.1 l.1 * (R k.2.2 l.2.2 * R k.2.1 l.2.1) = R k.1 l.1 * (R k.2.1 l.2.1 * R k.2.2 l.2.2)
    rw [mul_comm (R k.2.2 l.2.2)]
  have hOp : atlasJetCovarianceOperator c A p = C * G := atlasJetCovarianceOperator_in_fiber c A p hc
  rw [hOp, Matrix.mul_apply, Matrix.mul_apply]
  rw [← Equiv.sum_comp jetPairSwap (fun k => C i k * G k (jetPairSwap j))]
  exact Finset.sum_congr rfl (fun k _ => by rw [hIn, hG])

theorem intrinsicJetCovarianceEndomorphism_apply_swap {r : Metric (M := M)}
    {B : Field (M := M)} {hn : IsNondegenerate B} {A : AmplitudeCovarianceDensity r} {p : Cosphere r}
    (h : HasIntrinsicAmplitudeRicciKernel r B hn A p)
    (hPos : ∀ b : Basis Index ℝ (TangentSpace Model (projection p)), (components b (A p)).PosSemidef)
    (F : ComplexCovariantJet (TangentSpace Model (projection p))) :
    intrinsicJetCovarianceEndomorphism A p (swapComplexCovariantJet _ F) = intrinsicJetCovarianceEndomorphism A p F := by
  let x := projection p
  let c := AtlasChart.atPoint x
  have hc : x ∈ c.chart.source := mem_chart_source CoordinateSpace x
  let b := chartTangentBasis c x hc
  apply (jetFiberCoordinates b).injective
  rw [intrinsicJetCovarianceEndomorphism_coordinates A p c hc (swapComplexCovariantJet _ F),
    intrinsicJetCovarianceEndomorphism_coordinates A p c hc F]
  funext i
  simp only [Matrix.mulVec, dotProduct, jetFiberCoordinates_swap]
  rw [← Equiv.sum_comp jetPairSwap (fun j => atlasJetCovarianceOperator c A p i j * jetFiberCoordinates b F j)]
  exact Finset.sum_congr rfl (fun j _ => by rw [atlasJetCovarianceOperator_input_swap h c hc (hPos b)])

/-- A dependent section of endomorphisms of the symmetric jet fibers at every auxiliary unit covector. -/
def intrinsicSymmetricJetCovariance {r : Metric (M := M)} (A : AmplitudeCovarianceDensity r) (p : Cosphere r) :
    End ℂ (complexSymmetricJet (TangentSpace Model (projection p))) :=
  (projectComplexSymmetricJet _).comp ((intrinsicJetCovarianceEndomorphism A p).comp (complexSymmetricJet _).subtype)

/-- The genuine symmetric endomorphism gives the original ordered operator
when inputs are symmetrized, so every ordered coordinate entry is recovered. -/
theorem intrinsicSymmetricJetCovariance_extension {r : Metric (M := M)}
    {B : Field (M := M)} {hn : IsNondegenerate B} {A : AmplitudeCovarianceDensity r} {p : Cosphere r}
    (h : HasIntrinsicAmplitudeRicciKernel r B hn A p)
    (hPos : ∀ b : Basis Index ℝ (TangentSpace Model (projection p)), (components b (A p)).PosSemidef)
    (F : ComplexCovariantJet (TangentSpace Model (projection p))) :
    (intrinsicSymmetricJetCovariance A p (projectComplexSymmetricJet _ F) :
      ComplexCovariantJet (TangentSpace Model (projection p))) = intrinsicJetCovarianceEndomorphism A p F := by
  change (projectComplexSymmetricJet _ (intrinsicJetCovarianceEndomorphism A p (projectComplexSymmetricJet _ F)) :
    ComplexCovariantJet (TangentSpace Model (projection p))) = _
  rw [coe_projectComplexSymmetricJet_of_mem _ (intrinsicJetCovarianceEndomorphism_mem_symmetric h _)]
  change intrinsicJetCovarianceEndomorphism A p ((2 : ℂ)⁻¹ • (F + swapComplexCovariantJet _ F)) = _
  rw [map_smul, map_add, intrinsicJetCovarianceEndomorphism_apply_swap h hPos, ← two_smul ℂ,
    smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

end Burnett.Microlocal.Overlap
