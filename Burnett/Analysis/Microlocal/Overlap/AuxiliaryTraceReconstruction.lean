import Burnett.Analysis.Microlocal.Overlap.AuxiliaryTracePositive
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-! The positive auxiliary trace gives a normalized density of the same entry measures. -/

set_option autoImplicit false
set_option maxHeartbeats 550000

noncomputable section

namespace Burnett.F07.IntrinsicAmplitude

open Matrix MeasureTheory Burnett.RicciSymbol
open Burnett.Microlocal.CurlDensity (Pair)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity)
open scoped ComplexOrder

variable {X : Type*} [MeasurableSpace X]

/-- Normalizing a positive covariance by its positive auxiliary trace
preserves every complex entry measure. The new density is positive with
unit auxiliary trace almost everywhere on the new control. -/
theorem auxiliaryTrace_normalization_recovers_entry_measures
    (μ : Measure X) (R : X → Tensor2) (A : X → Matrix Pair Pair ℂ)
    (hPositive : ∀ᵐ x ∂μ, Matrix.PosDef (R x) ∧ (A x).PosSemidef)
    (hTrace : AEMeasurable (fun x => auxiliaryTraceLinear (R x) (A x)) μ)
    (hA : ∀ i j, Integrable (fun x => A x i j) μ) :
    let t (x : X) := auxiliaryTraceLinear (R x) (A x)
    let τ := μ.withDensity (fun x => ENNReal.ofReal (t x))
    let D (x : X) := (t x)⁻¹ • A x
    (∀ᵐ x ∂τ, (D x).PosSemidef ∧ auxiliaryTraceLinear (R x) (D x) = 1) ∧
      ∀ i j, Integrable (fun x => D x i j) τ ∧
        τ.withDensityᵥ (fun x => D x i j) = μ.withDensityᵥ (fun x => A x i j) := by
  intro t τ D
  let w (x : X) := ENNReal.ofReal (t x)
  have hw : AEMeasurable w μ := ENNReal.measurable_ofReal.comp_aemeasurable hTrace
  have hwFinite : ∀ᵐ x ∂μ, w x < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  refine ⟨?_, ?_⟩
  · change ∀ᵐ x ∂μ.withDensity w, (D x).PosSemidef ∧ auxiliaryTraceLinear (R x) (D x) = 1
    rw [ae_withDensity_iff' hw]
    filter_upwards [hPositive] with x hx hpos
    have hn : 0 ≤ t x := (auxiliaryTraceLinear_nonneg_and_eq_zero_iff (R x) hx.1 (A x) hx.2).1
    have hne : t x ≠ 0 := fun h => hpos (by simp [w, h])
    refine ⟨hx.2.smul (inv_nonneg.mpr hn), ?_⟩
    change auxiliaryTraceLinear (R x) ((t x)⁻¹ • A x) = 1
    rw [map_smul, smul_eq_mul, show auxiliaryTraceLinear (R x) (A x) = t x from rfl,
      inv_mul_cancel₀ hne]
  · intro i j
    have hRec : (fun x => (w x).toReal • D x i j) =ᵐ[μ] (fun x => A x i j) := by
      filter_upwards [hPositive] with x hx
      obtain ⟨hn, hzero⟩ := auxiliaryTraceLinear_nonneg_and_eq_zero_iff (R x) hx.1 (A x) hx.2
      by_cases h : t x = 0
      · have hZ : A x = 0 := hzero.mp h
        change (w x).toReal • D x i j = A x i j
        simp [D, hZ]
      · change (ENNReal.ofReal (t x)).toReal • ((t x)⁻¹ • A x) i j = A x i j
        rw [ENNReal.toReal_ofReal hn, Matrix.smul_apply, smul_smul, mul_inv_cancel₀ h, one_smul]
    have hRecInt : Integrable (fun x => (w x).toReal • D x i j) μ := (hA i j).congr hRec.symm
    refine ⟨(integrable_withDensity_iff_integrable_smul₀' hw hwFinite).2 hRecInt, ?_⟩
    exact (withDensityᵥ_smul_eq_withDensityᵥ_withDensity' hw hwFinite hRecInt).symm.trans
      (WithDensityᵥEq.congr_ae hRec)

/-- The same trace normalization preserves the positive measure obtained by a
real-linear contraction on a specified measurable phase region. -/
theorem auxiliaryTrace_normalization_preserves_positive_contraction
    (μ : Measure X) (R : X → Tensor2) (A : X → Matrix Pair Pair ℂ)
    (hPositive : ∀ᵐ x ∂μ, Matrix.PosDef (R x) ∧ (A x).PosSemidef)
    (hTrace : AEMeasurable (fun x => auxiliaryTraceLinear (R x) (A x)) μ)
    (L : X → Matrix Pair Pair ℂ →ₗ[ℝ] ℝ)
    (hL : AEMeasurable (fun x => L x (A x)) μ) (S : Set X) (hS : MeasurableSet S) :
    let t (x : X) := auxiliaryTraceLinear (R x) (A x)
    let τ := μ.withDensity (fun x => ENNReal.ofReal (t x))
    let D (x : X) := (t x)⁻¹ • A x
    (τ.restrict S).withDensity (fun x => ENNReal.ofReal (L x (D x))) =
      (μ.restrict S).withDensity (fun x => ENNReal.ofReal (L x (A x))) := by
  intro t τ D
  let w (x : X) := ENNReal.ofReal (t x)
  have hw : AEMeasurable w (μ.restrict S) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hTrace).restrict
  have hLD : AEMeasurable (fun x => L x (D x)) μ := by
    refine (hTrace.inv.mul hL).congr (Filter.Eventually.of_forall (fun x => ?_))
    change (t x)⁻¹ * L x (A x) = L x ((t x)⁻¹ • A x)
    rw [map_smul, smul_eq_mul]
  have hQ : AEMeasurable (fun x => ENNReal.ofReal (L x (D x))) (μ.restrict S) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hLD).restrict
  change ((μ.withDensity w).restrict S).withDensity _ = _
  rw [restrict_withDensity hS, ← withDensity_mul₀ hw hQ]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_of_ae (s := S) hPositive] with x hx
  obtain ⟨hn, hzero⟩ := auxiliaryTraceLinear_nonneg_and_eq_zero_iff (R x) hx.1 (A x) hx.2
  change ENNReal.ofReal (t x) * ENNReal.ofReal (L x (D x)) = ENNReal.ofReal (L x (A x))
  rw [← ENNReal.ofReal_mul hn]
  congr 1
  by_cases h : t x = 0
  · simp [hzero.mp h]
  · change t x * L x ((t x)⁻¹ • A x) = _
    rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

end Burnett.F07.IntrinsicAmplitude
