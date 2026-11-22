import Burnett.Algebra.LorentzHermitian
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section

namespace Burnett.Microlocal.PhysicalDensity

open Matrix
open Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

abbrev OrderedPair := Index × Index

def tensorOfVector (v : OrderedPair → ℂ) : ComplexTensor2 :=
  fun a b => v (a, b)

/-- All ordered tensor pairs occur, including the two equal entries of each
off-diagonal pair on the symmetric fiber. -/
def physicalCoefficient (gInv : Tensor2) (i j : OrderedPair) : ℂ :=
  (gInv i.1 j.1 : ℂ) * gInv i.2 j.2 -
    (gInv i.1 i.2 : ℂ) * gInv j.1 j.2 / 2

/-- The contraction in the paper takes an entrywise covariance, rather than
the endomorphism matrix in the coordinate basis. -/
def physicalContraction (gInv : Tensor2) (cov : Matrix OrderedPair OrderedPair ℂ) : ℂ :=
  ∑ i, ∑ j, physicalCoefficient gInv i j * cov i j

/-- Columns of E are the ordered coordinates of the auxiliary orthonormal
basis. M is the endomorphism density in that orthonormal basis. -/
def coordinateCovariance {n : Type*} [Fintype n] (E : Matrix OrderedPair n ℂ)
    (M : Matrix n n ℂ) : Matrix OrderedPair OrderedPair ℂ :=
  E * M * Eᴴ

theorem hermitianPhysicalPairing_eq_sum (gInv : Tensor2)
    (v w : OrderedPair → ℂ) :
    hermitianPhysicalPairing gInv (tensorOfVector v) (tensorOfVector w) =
      ∑ i, ∑ j, physicalCoefficient gInv i j * (v i * conj (w j)) := by
  unfold hermitianPhysicalPairing complexMetricTrace
  simp only [Fintype.sum_prod_type, tensorOfVector, physicalCoefficient,
    map_sum, map_mul, Complex.conj_ofReal]
  have hproduct (f h : Index → Index → ℂ) :
      (∑ a, ∑ b, f a b) * (∑ c, ∑ d, h c d) =
        ∑ a, ∑ b, ∑ c, ∑ d, f a b * h c d := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    simp only [Finset.mul_sum]
  rw [hproduct]
  simp only [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem physicalContraction_gram {n : Type*} [Fintype n] (gInv : Tensor2)
    (B : Matrix OrderedPair n ℂ) :
    physicalContraction gInv (B * Bᴴ) =
      ∑ j, hermitianPhysicalPairing gInv (tensorOfVector (B.col j)) (tensorOfVector (B.col j)) := by
  simp only [physicalContraction, Matrix.mul_apply, Matrix.conjTranspose_apply,
    hermitianPhysicalPairing_eq_sum, Matrix.col_apply, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  rfl

/-- Mathlib's positive Hermitian square root in the finite coefficient space. -/
def densitySqrt {n : Type*} [Fintype n] (M : Matrix n n ℂ) : Matrix n n ℂ := by
  classical
  exact CFC.sqrt M

theorem densitySqrt_mul_self {n : Type*} [Fintype n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) :
    densitySqrt M * (densitySqrt M)ᴴ = M := by
  classical
  unfold densitySqrt
  have hS : (CFC.sqrt M).PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  rw [hS.isHermitian.eq]
  exact CFC.sqrt_mul_sqrt_self M hM.nonneg

theorem range_densitySqrt {n : Type*} [Fintype n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) :
    LinearMap.range (densitySqrt M).mulVecLin = LinearMap.range M.mulVecLin := by
  classical
  let S := densitySqrt M
  have hS : S.PosSemidef := by
    change (CFC.sqrt M).PosSemidef
    exact (CFC.sqrt_nonneg M).posSemidef
  have hker : LinearMap.ker M.mulVecLin = LinearMap.ker S.mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    have hprod : Sᴴ * S = M := calc
      Sᴴ * S = S * Sᴴ := by rw [hS.isHermitian.eq]
      _ = M := densitySqrt_mul_self hM
    rw [← hprod]
    exact Matrix.conjTranspose_mul_self_mulVec_eq_zero S v
  have hle : LinearMap.range M.mulVecLin ≤ LinearMap.range S.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    refine ⟨Sᴴ *ᵥ x, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, S, densitySqrt_mul_self hM]
  have hMdim := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hSdim := LinearMap.finrank_range_add_finrank_ker S.mulVecLin
  rw [hker] at hMdim
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

theorem coordinateCovariance_eq_gram {n : Type*} [Fintype n]
    (E : Matrix OrderedPair n ℂ) {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    coordinateCovariance E M = (E * densitySqrt M) * (E * densitySqrt M)ᴴ := by
  unfold coordinateCovariance
  calc
    E * M * Eᴴ = E * (densitySqrt M * (densitySqrt M)ᴴ) * Eᴴ := by
      rw [densitySqrt_mul_self hM]
    _ = (E * densitySqrt M) * (E * densitySqrt M)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Burnett.Microlocal.PhysicalDensity

namespace Burnett.Microlocal.PhysicalDensity

open Matrix Set MeasureTheory Filter TopologicalSpace
open Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal

variable {X : Type*} {n : Type*} [Fintype n]

/-- The null shell on the parameter space of unit covectors. -/
def nullShell (gInv : X → Tensor2) (ξ : X → Covector) : Set X :=
  {x | symbolNorm (gInv x) (ξ x) = 0}

/-- The real scalar density, with the actual factor one quarter. -/
def quarterDensity (gInv : X → Tensor2) (E : X → Matrix OrderedPair n ℂ)
    (M : X → Matrix n n ℂ) (x : X) : ℝ :=
  (physicalContraction (gInv x) (coordinateCovariance (E x) (M x))).re / 4

/-- The pointwise density inputs expected from the simultaneous F05 witness. -/
def NullDensityData (gInv : X → Tensor2) (ξ : X → Covector)
    (E : X → Matrix OrderedPair n ℂ) (M : X → Matrix n n ℂ) (x : X) : Prop :=
  (Nonempty (TensorFrame.LorentzFrame (gInv x))) ∧ ξ x ≠ 0 ∧ (M x).PosSemidef ∧
    ∀ v ∈ LinearMap.range (M x).mulVecLin,
      IsSymmetricComplexTensor (tensorOfVector (E x *ᵥ v)) ∧
      ∀ a b, complexRicciSymbol (gInv x) (ξ x) (tensorOfVector (E x *ᵥ v)) a b = 0

/-- Borel restriction is applied to the positive trace measure before the
physical weighting. -/
def nullPhysicalMeasure [MeasurableSpace X] (traceMeasure : Measure X)
    (gInv : X → Tensor2) (ξ : X → Covector)
    (E : X → Matrix OrderedPair n ℂ) (M : X → Matrix n n ℂ) : Measure X :=
  (traceMeasure.restrict (nullShell gInv ξ)).withDensity (fun x => ENNReal.ofReal (quarterDensity gInv E M x))

end Burnett.Microlocal.PhysicalDensity
