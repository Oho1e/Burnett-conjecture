import Burnett.Analysis.TransportPatches.PatchProjectedLpScale
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 4600000

noncomputable section

namespace Burnett.C03

open Set MeasureTheory Burnett.P01 Burnett.RicciSymbol Burnett.A08
open Burnett.Geometry.ConnectionDifference
open Burnett.A02.FrequencySplit (E)
open Burnett.A07 (coordinateDerivative)
open scoped ENNReal BigOperators

open private derivativeArray from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator

/-- The correction uses the Euclidean four-component gradient. Its norm
is bounded by the sum of the actual coordinate derivatives. -/
theorem schwartzGradientNorm_le_sum_eLpNorm (p : ℝ≥0∞) (hp : 1 ≤ p) (f : SchwartzMap E ℂ) :
    schwartzGradientNorm p f ≤
      ∑ a : Index, (eLpNorm (coordinateDerivative a f : E → ℂ) p volume).toReal := by
  classical
  let A (a : Index) (x : E) : PiLp 2 (fun _ : Index => ℂ) :=
    WithLp.toLp 2 (Pi.single a (coordinateDerivative a f x))
  have hA (a : Index) : Continuous (A a) :=
    (PiLp.continuous_toLp 2 (fun _ : Index => ℂ)).comp
      (continuous_pi (fun i => by
        by_cases h : i = a
        · subst i
          simpa only [Pi.single_eq_same] using (coordinateDerivative a f).continuous
        · simpa only [Pi.single_eq_of_ne h] using (continuous_const : Continuous fun _ : E => (0 : ℂ))))
  have hSum : derivativeArray f = ∑ a, A a := by
    funext x
    ext b
    rw [Finset.sum_apply]
    change _ = PiLp.proj (𝕜 := ℝ) 2 (fun _ : Index => ℂ) b (∑ a, A a x)
    rw [map_sum]
    simp [A, derivativeArray]
  have hNorm (a : Index) :
      eLpNorm (A a) p volume = eLpNorm (coordinateDerivative a f : E → ℂ) p volume := by
    rw [← eLpNorm_norm (f := A a), ← eLpNorm_norm (f := (coordinateDerivative a f : E → ℂ))]
    simp only [A, PiLp.norm_toLp_single]
  have hUpper : eLpNorm (derivativeArray f) p volume ≤
      ∑ a : Index, eLpNorm (coordinateDerivative a f : E → ℂ) p volume := by
    rw [hSum]
    refine (eLpNorm_sum_le (fun a _ => (hA a).aestronglyMeasurable) hp).trans_eq ?_
    simp only [hNorm]
  have hFinite (a : Index) : eLpNorm (coordinateDerivative a f : E → ℂ) p volume ≠ ⊤ :=
    ((coordinateDerivative a f).memLp p volume).2.ne
  unfold schwartzGradientNorm
  rw [← ENNReal.toReal_sum (fun a _ => hFinite a)]
  exact ENNReal.toReal_mono (ENNReal.sum_lt_top.mpr (fun a _ => (hFinite a).lt_top)).ne hUpper

theorem projectedPatchLp_gradients {p : ℝ} (hp : 1 < p) {z : ProjectionSchwartzMatrix}
    {K : Set CoordinateSpace} {value gradient : ℝ}
    (h : ProjectedPatchLpBounds p z K value gradient) (i j : Index) :
    schwartzGradientNorm (ENNReal.ofReal p) (projectionFullSchwartz z i j) ≤
      (4 * gradient) * (volume K ^ (1 / p)).toReal ∧
    schwartzGradientNorm (ENNReal.ofReal p) (projectedGaugeComplement z i j) ≤
      (4 * gradient) * (volume K ^ (1 / p)).toReal := by
  have hp₁ : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  constructor
  · refine (schwartzGradientNorm_le_sum_eLpNorm _ hp₁ _).trans ?_
    calc
      _ ≤ ∑ _ : Index, gradient * (volume K ^ (1 / p)).toReal :=
        Finset.sum_le_sum fun a _ => ((h i j).2 a).1
      _ = _ := by simp [nsmul_eq_mul, mul_assoc]
  · refine (schwartzGradientNorm_le_sum_eLpNorm _ hp₁ _).trans ?_
    calc
      _ ≤ ∑ _ : Index, gradient * (volume K ^ (1 / p)).toReal :=
        Finset.sum_le_sum fun a _ => ((h i j).2 a).2
      _ = _ := by simp [nsmul_eq_mul, mul_assoc]

end Burnett.C03
