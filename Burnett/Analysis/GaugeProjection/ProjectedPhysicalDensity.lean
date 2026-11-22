import Burnett.Analysis.GaugeProjection.PrincipalGaugeProjectionAlgebra
import Burnett.Analysis.Microlocal.PhysicalDensity

set_option autoImplicit false
set_option maxHeartbeats 6200000

noncomputable section

namespace Burnett.P01

open Matrix MeasureTheory Filter Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity
open scoped BigOperators ComplexConjugate ComplexOrder Matrix MatrixOrder

/-- The very same principal symbol in the original ordered tensor coordinates
used by the F07 defect measure. -/
def principalGaugeProjectionMatrix (ξ : E) : Matrix OrderedPair OrderedPair ℂ :=
  fun i j => (gaugeProjectionSymbol i.1 i.2 j.1 j.2 ξ : ℂ)

theorem tensorOfVector_principalGaugeProjectionMatrix (ξ : E) (v : OrderedPair → ℂ) :
    tensorOfVector (principalGaugeProjectionMatrix ξ *ᵥ v) =
      (principalGaugeProjection ξ (tensorOfVector v) : ComplexTensor2) := by
  funext a b
  simp only [tensorOfVector, Matrix.mulVec, dotProduct, principalGaugeProjectionMatrix,
    principalGaugeProjection, gaugeProjectionSymbol, directionProjectionEntry, Matrix.mul_apply,
    Matrix.of_apply, Matrix.map_apply, Complex.ofReal_mul, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

private theorem projectedGramColumn {ι : Type*} [Fintype ι] (ξ : E)
    (U : Matrix OrderedPair ι ℂ) (M : Matrix ι ι ℂ) (j : ι) :
    tensorOfVector (((principalGaugeProjectionMatrix ξ * U) * densitySqrt M).col j) =
      (principalGaugeProjection ξ (tensorOfVector ((U * densitySqrt M).col j)) : ComplexTensor2) := by
  rw [← tensorOfVector_principalGaugeProjectionMatrix, Matrix.mul_assoc]
  rfl

private theorem gramColumn_in_kernel {ι : Type*} [Fintype ι]
    (G : Tensor2) (ξ : E) (U : Matrix OrderedPair ι ℂ) {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef)
    (hK : ∀ v ∈ LinearMap.range M.mulVecLin,
      IsSymmetricComplexTensor (tensorOfVector (U *ᵥ v)) ∧
      ∀ a b, complexRicciSymbol G (fun i => ξ i) (tensorOfVector (U *ᵥ v)) a b = 0)
    (j : ι) :
    let H := tensorOfVector ((U * densitySqrt M).col j)
    IsSymmetricComplexTensor H ∧ ∀ a b, complexRicciSymbol G (fun i => ξ i) H a b = 0 := by
  classical
  have hj : (densitySqrt M).col j ∈ LinearMap.range M.mulVecLin := by
    rw [← range_densitySqrt hM]
    exact ⟨Pi.single j 1, Matrix.mulVec_single_one _ _⟩
  exact hK _ hj

/-- On the same null density, pushing both ordered covariance slots forward
by the original principal gauge projection preserves the exact F07 scalar
contraction. -/
theorem projectedCoordinateCovariance_physicalContraction_eq {ι : Type*} [Fintype ι]
    (G : Tensor2) (ξ : E) (U : Matrix OrderedPair ι ℂ) {M : Matrix ι ι ℂ}
    (hG : IsSymmetricTensor G) (hξ : (fun i : Index => ξ i) ≠ 0)
    (hNull : symbolNorm G (fun i => ξ i) = 0) (hM : M.PosSemidef)
    (hK : ∀ v ∈ LinearMap.range M.mulVecLin,
      IsSymmetricComplexTensor (tensorOfVector (U *ᵥ v)) ∧
      ∀ a b, complexRicciSymbol G (fun i => ξ i) (tensorOfVector (U *ᵥ v)) a b = 0) :
    physicalContraction G (coordinateCovariance (principalGaugeProjectionMatrix ξ * U) M) =
      physicalContraction G (coordinateCovariance U M) := by
  rw [coordinateCovariance_eq_gram _ hM, coordinateCovariance_eq_gram _ hM,
    physicalContraction_gram, physicalContraction_gram]
  apply Finset.sum_congr rfl
  intro j _
  simp only [projectedGramColumn]
  obtain ⟨hSym, hKer⟩ := gramColumn_in_kernel G ξ U hM hK j
  exact principalGaugeProjection_preserves_hermitianPhysicalPairing G ξ _ _ hG hSym hSym hξ hNull hKer hKer

/-- Equality of the full measures on the original measurable angular space
using the same trace and its Borel null shell. -/
theorem nullPhysicalMeasure_principalGaugeProjection_eq
    {X ι : Type*} [MeasurableSpace X] [Fintype ι] (τ : Measure X)
    (G : X → Tensor2) (ξ : X → E) (U : X → Matrix OrderedPair ι ℂ) (M : X → Matrix ι ι ℂ)
    (hZ : MeasurableSet (nullShell G (fun x i => ξ x i)))
    (h : ∀ᵐ x ∂τ.restrict (nullShell G (fun x i => ξ x i)),
      IsSymmetricTensor (G x) ∧ NullDensityData G (fun y i => ξ y i) U M x) :
    nullPhysicalMeasure τ G (fun x i => ξ x i) (fun x => principalGaugeProjectionMatrix (ξ x) * U x) M =
      nullPhysicalMeasure τ G (fun x i => ξ x i) U M := by
  unfold nullPhysicalMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hZ, h] with x hx hdata
  obtain ⟨hG, _, hξ, hM, hK⟩ := hdata
  unfold quarterDensity
  rw [projectedCoordinateCovariance_physicalContraction_eq (G x) (ξ x) (U x) hG hξ hx hM hK]

end Burnett.P01
