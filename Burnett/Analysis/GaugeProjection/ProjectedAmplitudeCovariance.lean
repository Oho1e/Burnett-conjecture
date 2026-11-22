import Burnett.Analysis.GaugeProjection.ProjectedPhysicalDensity

set_option autoImplicit false
set_option maxHeartbeats 4600000

noncomputable section

namespace Burnett.P01

open Matrix MeasureTheory Filter Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity
open scoped BigOperators Matrix MatrixOrder ComplexOrder

/-- The ordered-coordinate symbol is homogeneous in the same nonzero
covector. It is therefore the same on the auxiliary cosphere and on the
Euclidean angular section used in Fourier tests. -/
theorem principalGaugeProjectionMatrix_scale (ξ : E) (r : ℝ) (hr : 0 < r) :
    principalGaugeProjectionMatrix (r • ξ) = principalGaugeProjectionMatrix ξ := by
  ext i j
  simp only [principalGaugeProjectionMatrix, gaugeProjectionSymbol_scale _ _ _ _ r hr]

/-- The projected covariance keeps the original two coordinate derivative
factors of the same amplitude. -/
theorem projectedCoordinateCovariance_preserves_gradient_factor
    (ξ : E) (N : Matrix OrderedPair OrderedPair ℂ) (d e : Index) :
    principalGaugeProjectionMatrix ξ * (((ξ d * ξ e : ℝ) : ℂ) • N) *
      (principalGaugeProjectionMatrix ξ)ᴴ =
    ((ξ d * ξ e : ℝ) : ℂ) •
      (principalGaugeProjectionMatrix ξ * N * (principalGaugeProjectionMatrix ξ)ᴴ) := by
  rw [mul_smul_comm, smul_mul_assoc]

/-- The amplitude covariance pushed forward by the same principal projection
vanishes off the null cone. -/
theorem projectedCoordinateCovariance_eq_zero_off_null
    (G : Tensor2) (ξ : E) (A : Matrix OrderedPair OrderedPair ℂ)
    (hξ : (fun i : Index => ξ i) ≠ 0) (hs : symbolNorm G (fun i => ξ i) ≠ 0)
    (hK : ∀ v : OrderedPair → ℂ, ∀ a b,
      complexRicciSymbol G (fun i => ξ i) (tensorOfVector (A *ᵥ v)) a b = 0) :
    principalGaugeProjectionMatrix ξ * A * (principalGaugeProjectionMatrix ξ)ᴴ = 0 := by
  classical
  have hPA : principalGaugeProjectionMatrix ξ * A = 0 := by
    ext i j
    have h := hK (Pi.single j 1)
    rw [Matrix.mulVec_single_one] at h
    have hz := principalGaugeProjection_eq_zero_off_null G ξ (tensorOfVector (A.col j)) hξ hs h
    have he := tensorOfVector_principalGaugeProjectionMatrix ξ (A.col j)
    rw [hz] at he
    exact congrFun (congrFun he i.1) i.2
  rw [hPA, zero_mul]

/-- The image of the projected null amplitude covariance satisfies the
original coordinate Lorenz polarization equation. -/
theorem projectedCoordinateCovariance_null_contracted
    (G : Tensor2) (ξ : E) (A : Matrix OrderedPair OrderedPair ℂ)
    (hG : IsSymmetricTensor G) (hξ : (fun i : Index => ξ i) ≠ 0)
    (hs : symbolNorm G (fun i => ξ i) = 0)
    (hK : ∀ v : OrderedPair → ℂ,
      IsSymmetricComplexTensor (tensorOfVector (A *ᵥ v)) ∧
      ∀ a b, complexRicciSymbol G (fun i => ξ i) (tensorOfVector (A *ᵥ v)) a b = 0)
    (v : OrderedPair → ℂ) (b : Index) :
    let H := tensorOfVector
      ((principalGaugeProjectionMatrix ξ * A * (principalGaugeProjectionMatrix ξ)ᴴ) *ᵥ v)
    IsSymmetricComplexTensor H ∧ complexContracted G (fun i => ξ i) H b =
      complexMetricTrace G H * ((ξ b / 2 : ℝ) : ℂ) := by
  dsimp only
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tensorOfVector_principalGaugeProjectionMatrix]
  let K := tensorOfVector (A *ᵥ ((principalGaugeProjectionMatrix ξ)ᴴ *ᵥ v))
  obtain ⟨hS, hC⟩ := hK ((principalGaugeProjectionMatrix ξ)ᴴ *ᵥ v)
  change IsSymmetricComplexTensor K at hS
  constructor
  · obtain ⟨w, hw⟩ := principalGaugeProjection_adds_pureGauge ξ K hS
    rw [hw]
    intro i j
    change K i j + complexPureGauge (fun t => ξ t) w i j =
      K j i + complexPureGauge (fun t => ξ t) w j i
    rw [hS i j, complexPureGauge_symmetric _ _ i j]
  · exact principalGaugeProjection_null_contracted G ξ K hG hS hξ hs hC b

/-- The F07 physical measure built directly from a positive original
covariance is unchanged by its projected covariance on the same trace. -/
theorem nullPhysicalMeasure_projectedAmplitudeCovariance_eq
    {X : Type*} [MeasurableSpace X] (τ : Measure X)
    (G : X → Tensor2) (ξ : X → E) (A : X → Matrix OrderedPair OrderedPair ℂ)
    (hZ : MeasurableSet (nullShell G (fun x i => ξ x i)))
    (h : ∀ᵐ x ∂τ.restrict (nullShell G (fun x i => ξ x i)),
      IsSymmetricTensor (G x) ∧ (fun i : Index => ξ x i) ≠ 0 ∧ (A x).PosSemidef ∧
      ∀ v : OrderedPair → ℂ, IsSymmetricComplexTensor (tensorOfVector (A x *ᵥ v)) ∧
        ∀ a b, complexRicciSymbol (G x) (fun i => ξ x i) (tensorOfVector (A x *ᵥ v)) a b = 0) :
    nullPhysicalMeasure τ G (fun x i => ξ x i) (fun _ => (1 : Matrix OrderedPair OrderedPair ℂ))
       (fun x => principalGaugeProjectionMatrix (ξ x) * A x * (principalGaugeProjectionMatrix (ξ x))ᴴ) =
    nullPhysicalMeasure τ G (fun x i => ξ x i) (fun _ => 1) A := by
  classical
  unfold nullPhysicalMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hZ, h] with x hx hData
  obtain ⟨hG, hξ, hPos, hK⟩ := hData
  have hRange : ∀ v ∈ LinearMap.range (A x).mulVecLin,
      IsSymmetricComplexTensor
        (tensorOfVector ((1 : Matrix OrderedPair OrderedPair ℂ) *ᵥ v)) ∧
      ∀ a b, complexRicciSymbol (G x) (fun i => ξ x i)
        (tensorOfVector ((1 : Matrix OrderedPair OrderedPair ℂ) *ᵥ v)) a b = 0 := by
    rintro v ⟨w, rfl⟩
    simpa only [Matrix.one_mulVec, Matrix.mulVecLin_apply] using hK w
  have hc := projectedCoordinateCovariance_physicalContraction_eq
    (G x) (ξ x) (1 : Matrix OrderedPair OrderedPair ℂ) hG hξ hx hPos hRange
  simp only [coordinateCovariance, mul_one, Matrix.conjTranspose_one, one_mul] at hc
  unfold quarterDensity
  simp only [coordinateCovariance, Matrix.conjTranspose_one, one_mul, mul_one, hc]

end Burnett.P01
