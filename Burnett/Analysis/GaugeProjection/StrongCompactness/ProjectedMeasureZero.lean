import Burnett.Analysis.GaugeProjection.StrongCompactness.ProjectedDensityZero

/-! The same positive physical measure detects the projected defect on every measurable window. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 3800000

noncomputable section
namespace Burnett.P01

open Set Matrix MeasureTheory Filter Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity
open scoped ComplexOrder Matrix MatrixOrder ENNReal

open private gramColumn_in_kernel from Burnett.Analysis.GaugeProjection.ProjectedPhysicalDensity

/-- The null restriction and its positive Lorentz contraction vanish on a
window exactly when the full projected covariance vanishes there relative
to the original control. The non-null part is removed by the same projection. -/
theorem nullPhysicalMeasure_apply_eq_zero_iff_projectedCovariance_ae_eq_zero
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (τ : Measure X) (G : X → Tensor2) (ξ : X → E) (U : X → Matrix OrderedPair ι ℂ)
    (M : X → Matrix ι ι ℂ) (W : Set X) (hW : MeasurableSet W)
    (hZ : MeasurableSet (nullShell G (fun x i => ξ x i)))
    (hM : Measurable (fun x => ENNReal.ofReal (quarterDensity G U M x)))
    (hData : ∀ᵐ x ∂τ.restrict W, NullDensityData G (fun x i => ξ x i) U M x) :
    nullPhysicalMeasure τ G (fun x i => ξ x i) U M W = 0 ↔
      ∀ᵐ x ∂τ.restrict W, coordinateCovariance (principalGaugeProjectionMatrix (ξ x) * U x) (M x) = 0 := by
  classical
  let Z := nullShell G (fun x i => ξ x i)
  let w (x : X) := ENNReal.ofReal (quarterDensity G U M x)
  let P (x : X) := principalGaugeProjectionMatrix (ξ x)
  rw [nullPhysicalMeasure, withDensity_apply _ hW, Measure.restrict_comm hW, lintegral_eq_zero_iff hM]
  constructor
  · intro hz
    have hZero : ∀ᵐ x ∂τ.restrict W, x ∈ Z → w x = 0 := (ae_restrict_iff' hZ).mp hz
    filter_upwards [hData, hZero] with x hx hZx
    obtain ⟨⟨frame⟩, hξ, hPos, hKer⟩ := hx
    by_cases hNull : x ∈ Z
    · have hNonneg : 0 ≤ quarterDensity G U M x := by
        unfold quarterDensity
        rw [coordinateCovariance_eq_gram _ hPos, physicalContraction_gram, Complex.re_sum]
        apply div_nonneg _ (by norm_num)
        apply Finset.sum_nonneg
        intro j _
        have h := gramColumn_in_kernel (G x) (ξ x) (U x) hPos hKer j
        exact LorentzHermitian.physicalPairing_self_re_nonneg (G x) frame _ _ h.1 hξ hNull h.2
      have hQ : quarterDensity G U M x = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp (hZx hNull)) hNonneg
      have hC : (physicalContraction (G x) (coordinateCovariance (U x) (M x))).re = 0 := by
        change (physicalContraction (G x) (coordinateCovariance (U x) (M x))).re / 4 = 0 at hQ
        linarith
      exact (physicalContraction_re_eq_zero_iff_projectedCovariance_eq_zero (G x) frame
        (ξ x) (U x) hPos hξ hNull hKer).mp hC
    · have hOrdered (v : OrderedPair → ℂ) :
          ∀ i j, complexRicciSymbol (G x) (fun k => ξ x k)
            (tensorOfVector (coordinateCovariance (U x) (M x) *ᵥ v)) i j = 0 := by
        let z := M x *ᵥ ((U x)ᴴ *ᵥ v)
        have hz : z ∈ LinearMap.range (M x).mulVecLin := ⟨(U x)ᴴ *ᵥ v, rfl⟩
        simpa only [coordinateCovariance, ← Matrix.mulVec_mulVec, z] using (hKer z hz).2
      have hOff := projectedCoordinateCovariance_eq_zero_off_null (G x) (ξ x)
        (coordinateCovariance (U x) (M x)) hξ hNull hOrdered
      change coordinateCovariance (P x * U x) (M x) = 0
      simpa only [coordinateCovariance, Matrix.conjTranspose_mul, Matrix.mul_assoc, P] using hOff
  · intro hProj
    have hData' := ae_restrict_of_ae (s := Z) hData
    have hProj' := ae_restrict_of_ae (s := Z) hProj
    filter_upwards [hData', hProj', ae_restrict_mem (μ := τ.restrict W) hZ] with x hx hp hNull
    obtain ⟨⟨frame⟩, hξ, hPos, hKer⟩ := hx
    have hC := (physicalContraction_re_eq_zero_iff_projectedCovariance_eq_zero (G x) frame
      (ξ x) (U x) hPos hξ hNull hKer).mpr hp
    change w x = 0
    simp only [w, quarterDensity, hC, zero_div, ENNReal.ofReal_zero]

end Burnett.P01
