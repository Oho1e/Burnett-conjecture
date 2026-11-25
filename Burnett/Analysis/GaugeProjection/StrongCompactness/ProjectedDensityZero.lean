import Burnett.Analysis.GaugeProjection.ProjectedAmplitudeCovariance

/-! Zero physical density on the null cone is equivalent to zero projected covariance. -/
set_option autoImplicit false
set_option maxRecDepth 4200
set_option maxHeartbeats 3500000

noncomputable section
namespace Burnett.P01

open Matrix Burnett.RicciSymbol
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity
open scoped BigOperators ComplexOrder Matrix MatrixOrder

open private principalGaugeProjection_re principalGaugeProjection_im
  from Burnett.Analysis.GaugeProjection.PrincipalGaugeProjectionAlgebra
open private gramColumn_in_kernel from Burnett.Analysis.GaugeProjection.ProjectedPhysicalDensity

private theorem principalGaugeProjection_kills_complexPureGauge (ξ : E)
    (hξ : (fun i : Index => ξ i) ≠ 0) (v : ComplexCovector) :
    principalGaugeProjection ξ (complexPureGauge (fun i => ξ i) v) = 0 := by
  let x : Covector := fun i => ξ i
  let H := complexPureGauge x v
  have hR : Matrix.of (tensorRe H) = gaugeAmplitude x (fun i => (v i).re) := by
    ext i j
    simp [H, gaugeAmplitude, pureGauge, Matrix.vecMulVec]
  have hI : Matrix.of (tensorIm H) = gaugeAmplitude x (fun i => (v i).im) := by
    ext i j
    simp [H, gaugeAmplitude, pureGauge, Matrix.vecMulVec]
  have hzR := principalGaugeProjection_re ξ H
  have hzI := principalGaugeProjection_im ξ H
  rw [hR, euclideanGaugeProjection_kills_gauge hξ] at hzR
  rw [hI, euclideanGaugeProjection_kills_gauge hξ] at hzI
  ext i j
  apply Complex.ext
  · exact congrFun (congrFun hzR i) j
  · exact congrFun (congrFun hzI i) j

/-- On a complex Hermitian null Ricci covariance, the scalar used in the
physical measure vanishes exactly when the actual Euclidean gauge-complement
projection annihilates its covariance. No uniform coercivity choice is needed
for this zero-set implication. -/
theorem physicalContraction_re_eq_zero_iff_projectedCovariance_eq_zero
    {ι : Type*} [Fintype ι] (G : Tensor2) (frame : LorentzFrame G) (ξ : E)
    (U : Matrix OrderedPair ι ℂ) {M : Matrix ι ι ℂ} (hM : M.PosSemidef)
    (hξ : (fun i : Index => ξ i) ≠ 0) (hNull : symbolNorm G (fun i => ξ i) = 0)
    (hK : ∀ v ∈ LinearMap.range M.mulVecLin,
      IsSymmetricComplexTensor (tensorOfVector (U *ᵥ v)) ∧
      ∀ a b, complexRicciSymbol G (fun i => ξ i) (tensorOfVector (U *ᵥ v)) a b = 0) :
    (physicalContraction G (coordinateCovariance U M)).re = 0 ↔
      coordinateCovariance (principalGaugeProjectionMatrix ξ * U) M = 0 := by
  classical
  let C := U * densitySqrt M
  let P := principalGaugeProjectionMatrix ξ
  let H (j : ι) := tensorOfVector (C.col j)
  have hKer (j : ι) := gramColumn_in_kernel G ξ U hM hK j
  constructor
  · intro hz
    rw [coordinateCovariance_eq_gram _ hM, physicalContraction_gram, Complex.re_sum] at hz
    have hn (j : ι) : 0 ≤ (hermitianPhysicalPairing G (H j) (H j)).re :=
      LorentzHermitian.physicalPairing_self_re_nonneg G frame _ _ (hKer j).1 hξ hNull (hKer j).2
    have hCol (j : ι) : hermitianPhysicalPairing G (H j) (H j) = 0 := by
      apply Complex.ext
      · exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hz j (Finset.mem_univ j)
      · exact LorentzHermitian.physicalPairing_self_im_eq_zero G frame (H j)
    have hPC : P * C = 0 := by
      ext i j
      obtain ⟨v, hv⟩ := (LorentzHermitian.physicalPairing_self_eq_zero_iff_pureGauge
        G frame (fun i => ξ i) (H j) (hKer j).1 hξ hNull (hKer j).2).mp (hCol j)
      have h := tensorOfVector_principalGaugeProjectionMatrix ξ (C.col j)
      change tensorOfVector (P *ᵥ C.col j) = (principalGaugeProjection ξ (H j) : ComplexTensor2) at h
      rw [hv, principalGaugeProjection_kills_complexPureGauge ξ hξ] at h
      exact congrFun (congrFun h i.1) i.2
    rw [coordinateCovariance_eq_gram _ hM]
    change ((P * U) * densitySqrt M) * ((P * U) * densitySqrt M)ᴴ = 0
    rw [Matrix.mul_assoc P U, show P * (U * densitySqrt M) = 0 from hPC]
    simp
  · intro hz
    rw [← projectedCoordinateCovariance_physicalContraction_eq G ξ U
      (LorentzPhysical.metric_symmetric G frame) hξ hNull hM hK, hz]
    simp [physicalContraction]

end Burnett.P01
