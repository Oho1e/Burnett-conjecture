import Burnett.Analysis.TransportWard.Weyl.LeadingThirdVariationCoordinates
import Burnett.Analysis.TransportWard.Weyl.FrozenEulerQuadraticJet
import Burnett.Analysis.TransportWard.Weyl.OriginalWeylOrderedFields

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.V03.Palatini

open Set Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldBilinear ManifoldMetric MaximalChart Burnett.C02
open Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction FrequencyOrderOne)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff Manifold Matrix.Norms.Elementwise

/-- Read a real component field in the original ordered matrix entries. -/
def orderedRealEnergyField {J : Type} [Fintype J] (S : J → Mat)
    (z : RealEnergyField J) : RealEnergyField OrderedPair := by
  let Z (k : OrderedPair) := ∑ i, (S i k.1 k.2 : ℂ) • z.val i
  refine ⟨Z, fun k x => ?_⟩
  have hZ : Z k x = ∑ i, (S i k.1 k.2 : ℂ) * z.val i x := by
    change SchwartzMap.delta ℂ ℂ x (∑ i, (S i k.1 k.2 : ℂ) • z.val i) = _
    simp only [map_sum, map_smul, SchwartzMap.delta_apply, smul_eq_mul]
  have hReal (i : J) : conj (z.val i x) = z.val i x := z.property i x
  simp only [hZ, map_sum, map_mul, Complex.conj_ofReal, hReal]

theorem orderedRealEnergyField_apply {J : Type} [Fintype J] (S : J → Mat)
    (z : RealEnergyField J) (a b : Index) :
    (orderedRealEnergyField S z).val (a,b) = ∑ i, (S i a b : ℂ) • z.val i := rfl

theorem orderedRealEnergyField_assembledCoordinateMetric {J : Type} [Fintype J]
    (S : J → Mat) (z : RealEnergyField J) :
    assembledCoordinateMetric frozenActionOrderedBasis (fun y i => ((orderedRealEnergyField S z).val i y).re) =
      assembledCoordinateMetric S (fun y i => (z.val i y).re) := by
  funext x
  change assembleMetricComponents frozenActionOrderedBasis
      (fun i => ((orderedRealEnergyField S z).val i x).re) =
    assembleMetricComponents S (fun i => (z.val i x).re)
  rw [assembleMetricComponents_orderedBasis, assembleMetricComponents_apply]
  ext a b
  rw [Matrix.sum_apply]
  rw [orderedRealEnergyField_apply]
  change (SchwartzMap.delta ℂ ℂ x (∑ i, (S i a b : ℂ) • z.val i)).re = _
  simp only [map_sum, map_smul, SchwartzMap.delta_apply, smul_eq_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Matrix.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- The true A03 test is invariant under exact reassembly to the ordered
components that receive the C02 projected cubic energy. -/
theorem principalVariationDensity_re_eq_ordered {J : Type} [Fintype J]
    (S : J → Mat) (g : E → J → ℝ) (z w : RealEnergyField J) (x : E)
    (hG : assembleMetricComponents S (g x) ∈ nonsingularMetricDomain) :
    let b (y : E) (i : OrderedPair) := assembleMetricComponents S (g y) i.1 i.2
    let z' := orderedRealEnergyField S z
    let w' := orderedRealEnergyField S w
    (principalVariationDensity (eulerPrincipalVariationCoefficient S g) z.val (fun i => w.val i) x).re =
      (principalVariationDensity (eulerPrincipalVariationCoefficient frozenActionOrderedBasis b)
        z'.val (fun i => w'.val i) x).re := by
  intro b z' w'
  have hB : assembleMetricComponents S (g x) = assembleMetricComponents frozenActionOrderedBasis (b x) := by
    rw [assembleMetricComponents_orderedBasis]
  exact principalVariationDensity_re_eq_of_assembledFields S frozenActionOrderedBasis g b z w z' w' x hG hB
    (orderedRealEnergyField_assembledCoordinateMetric S z).symm
    (orderedRealEnergyField_assembledCoordinateMetric S w).symm

local notation "I" => SymmetricMetricSlot

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M]

theorem orderedRealEnergyField_eq_originalWeylFields
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hBs : IsSymmetric B) (hgs : ∀ n, IsSymmetric (g n))
    (c : M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ (chartAt E c).target)
    (p : E → E → ℂ) (hp : FrequencyOrderOne p) (n : ℕ) (z w : RealEnergyField I)
    (hz : ∀ i : I, z.val i = (symmetricMetricScale i : ℂ) •
      fixedWeylPerturbationSchwartz B g hB hg (AtlasChart.atPoint c) χ hχ n i.val)
    (hw : ∀ i x, w.val i x = (-Complex.I) * firstOrderAction p (z.val i) x) :
    (∀ a b : Index, (orderedRealEnergyField orthonormalMetricDirection z).val (a,b) =
      fixedWeylPerturbationSchwartz B g hB hg (AtlasChart.atPoint c) χ hχ n (a,b)) ∧
    ∀ (a b : Index) (x : E), (orderedRealEnergyField orthonormalMetricDirection w).val (a,b) x =
      (-Complex.I) * firstOrderAction p
        (fixedWeylPerturbationSchwartz B g hB hg (AtlasChart.atPoint c) χ hχ n (a,b)) x := by
  constructor
  · intro a b
    rw [orderedRealEnergyField_apply]
    simp only [hz]
    exact normalizedWeylPerturbation_reassemble_ordered B g hB hg hBs hgs c χ hχ n a b
  · intro a b x
    rw [orderedRealEnergyField_apply]
    change SchwartzMap.delta ℂ ℂ x
      (∑ i, (orthonormalMetricDirection i a b : ℂ) • w.val i) = _
    simp only [map_sum, map_smul, SchwartzMap.delta_apply, smul_eq_mul, hw, hz]
    exact originalWeylRealTest_reassemble_ordered B g hB hg hBs hgs c χ hχ p hp n a b x

end Burnett.V03.Palatini
