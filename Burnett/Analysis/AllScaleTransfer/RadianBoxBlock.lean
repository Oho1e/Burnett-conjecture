import Burnett.Analysis.AllScaleTransfer.ActualGapBoxSeries
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearModeSeries
import Burnett.Analysis.AllScaleTransfer.RadianRadialSeries

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.A05

open Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A03 (spatialLatticeVector spatialModePhase spatialModeFrequency)
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier (radianTrilinearForm)
open scoped RealInnerProductSpace

/-- The actual angular or normalized-box profile on one radial block,
with the third, negative-sum window kept throughout the expansion. -/
def radianBoxBlock (a b d : SchwartzMap E ℂ) (t u v : ℝ)
    (G : BoxSpace → ℂ) (p : Joint) : ℂ :=
  let ξ := tau⁻¹ • p.1
  let η := tau⁻¹ • p.2
  let ζ := t • ξ
  let υ := u • η
  G (joinedInputs ζ υ) * (a ζ * b υ * d (v • (-(ξ + η))))

private theorem spatialModePhase_eq_radian (P : ℝ) (hP : 0 < P) (k : FourierMode) (ζ : E) :
    tau * inner ℝ ζ ((1 / (2 * P)) • spatialLatticeVector k) = spatialModePhase P k ζ := by
  simp only [spatialModePhase, spatialModeFrequency, real_inner_smul_right, tau]
  field_simp

/-- Each separated box mode produces the two literal phase shifts on the
first and second scaled windows, with the same unmodulated third window. -/
theorem radianSeparatedWindowSymbol_eq_boxMode (P : ℝ) (hP : 0 < P)
    (a b d : SchwartzMap E ℂ) (t u v : ℝ) (k : FourierModePair) (p : Joint) :
    radianSeparatedWindowSymbol a b d t u v
      ((1 / (2 * P)) • spatialLatticeVector k.1) ((1 / (2 * P)) • spatialLatticeVector k.2) p =
      radianBoxBlock a b d t u v (separatedBoxMode P k) p := by
  let ξ := tau⁻¹ • p.1
  let η := tau⁻¹ • p.2
  let ζ := t • ξ
  let υ := u • η
  change (Complex.exp ((↑(tau * inner ℝ ζ ((1 / (2 * P)) • spatialLatticeVector k.1)) : ℂ) * Complex.I) *
      a ζ) *
    (Complex.exp ((↑(tau * inner ℝ υ ((1 / (2 * P)) • spatialLatticeVector k.2)) : ℂ) * Complex.I) *
      b υ) * d (v • (-(ξ + η))) = _
  rw [spatialModePhase_eq_radian P hP, spatialModePhase_eq_radian P hP]
  change _ = separatedBoxMode P k (joinedInputs ζ υ) * (a ζ * b υ * d (v • (-(ξ + η))))
  simp only [separatedBoxMode, firstInput_joined, secondInput_joined]
  ring

/-- A separated mode on the true radial windows is continuous in the two
radian frequencies. -/
theorem continuous_radianBoxBlock_mode (P : ℝ) (hP : 0 < P)
    (a b d : SchwartzMap E ℂ) (t u v : ℝ) (k : FourierModePair) :
    Continuous (radianSeparatedWindowSymbol a b d t u v
      ((1 / (2 * P)) • spatialLatticeVector k.1) ((1 / (2 * P)) • spatialLatticeVector k.2)) := by
  change Continuous (fun p : Joint => radianSeparatedWindowSymbol a b d t u v
    ((1 / (2 * P)) • spatialLatticeVector k.1) ((1 / (2 * P)) • spatialLatticeVector k.2) p)
  simp only [radianSeparatedWindowSymbol_eq_boxMode P hP, radianBoxBlock, separatedBoxMode,
    firstInput_joined, secondInput_joined, spatialModePhase]
  fun_prop

theorem norm_radianBoxBlock_mode_le (P : ℝ) (hP : 0 < P)
    (a b d : SchwartzMap E ℂ) (t u v : ℝ) (k : FourierModePair) (p : Joint) :
    ‖radianSeparatedWindowSymbol a b d t u v
      ((1 / (2 * P)) • spatialLatticeVector k.1) ((1 / (2 * P)) • spatialLatticeVector k.2) p‖ ≤
     SchwartzMap.seminorm ℝ 0 0 a * SchwartzMap.seminorm ℝ 0 0 b * SchwartzMap.seminorm ℝ 0 0 d := by
  simp only [radianSeparatedWindowSymbol_eq_boxMode P hP, radianBoxBlock, norm_mul,
    norm_separatedBoxMode, one_mul]
  exact mul_le_mul
    (mul_le_mul (a.norm_le_seminorm ℝ _) (b.norm_le_seminorm ℝ _) (norm_nonneg _) (apply_nonneg _ _))
    (d.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)

/-- Pointwise reconstruction only uses the normalized box series where
the first and second annular factors are nonzero. -/
theorem hasSum_radianBoxBlock_modes_at (P : ℝ) (hP : 0 < P)
    (a b d : SchwartzMap E ℂ) (t u v : ℝ) (G : BoxSpace → ℂ) (c : FourierModePair → ℂ)
    (hSeries : ∀ ζ υ : E, a ζ ≠ 0 → b υ ≠ 0 →
      HasSum (fun k => c k * separatedBoxMode P k (joinedInputs ζ υ)) (G (joinedInputs ζ υ)))
    (p : Joint) :
    HasSum (fun k => c k * radianSeparatedWindowSymbol a b d t u v
      ((1 / (2 * P)) • spatialLatticeVector k.1) ((1 / (2 * P)) • spatialLatticeVector k.2) p)
      (radianBoxBlock a b d t u v G p) := by
  simp only [radianSeparatedWindowSymbol_eq_boxMode P hP, radianBoxBlock]
  let ζ := t • (tau⁻¹ • p.1)
  let υ := u • (tau⁻¹ • p.2)
  let W := a ζ * b υ * d (v • (-((tau⁻¹ • p.1) + (tau⁻¹ • p.2))))
  change HasSum (fun k => c k * (separatedBoxMode P k (joinedInputs ζ υ) * W)) (G (joinedInputs ζ υ) * W)
  simp only [← mul_assoc]
  by_cases hw : W = 0
  · simp only [hw, mul_zero]
    exact hasSum_zero
  · have ha : a ζ ≠ 0 := by
      intro h
      apply hw
      simp only [W, h, zero_mul]
    have hb : b υ ≠ 0 := by
      intro h
      apply hw
      simp only [W, h, mul_zero, zero_mul]
    exact (hSeries ζ υ ha hb).mul_right W

/-- The actual block Fourier integral equals the sum of the integrals
of the separated translated modes. Reconstruction is needed only where
both retained windows are nonzero. -/
theorem radianTrilinearForm_hasSum_boxBlock_modes (P : ℝ) (hP : 0 < P)
    (a b d f g h : SchwartzMap E ℂ) (t u v : ℝ) (G : BoxSpace → ℂ)
    (c : FourierModePair → ℂ) (hc : Summable fun k => ‖c k‖)
    (hSeries : ∀ ζ υ : E, a ζ ≠ 0 → b υ ≠ 0 →
      HasSum (fun k => c k * separatedBoxMode P k (joinedInputs ζ υ)) (G (joinedInputs ζ υ))) :
    HasSum
      (fun k => radianTrilinearForm
        (fun p => c k * radianSeparatedWindowSymbol a b d t u v
          ((1 / (2 * P)) • spatialLatticeVector k.1) ((1 / (2 * P)) • spatialLatticeVector k.2) p) f g h)
      (radianTrilinearForm (radianBoxBlock a b d t u v G) f g h) := by
  let F (k : FourierModePair) (p : Joint) :=
    c k * radianSeparatedWindowSymbol a b d t u v
      ((1 / (2 * P)) • spatialLatticeVector k.1) ((1 / (2 * P)) • spatialLatticeVector k.2) p
  let B := SchwartzMap.seminorm ℝ 0 0 a * SchwartzMap.seminorm ℝ 0 0 b *
    SchwartzMap.seminorm ℝ 0 0 d
  apply radianTrilinearForm_hasSum_of_symbol_expansion F _ (fun k => ‖c k‖ * B)
  · intro k
    exact (continuous_const.mul (continuous_radianBoxBlock_mode P hP a b d t u v k)).aestronglyMeasurable
  · exact hc.mul_right B
  · intro k p
    rw [show ‖F k p‖ = ‖c k‖ * ‖radianSeparatedWindowSymbol a b d t u v
      ((1 / (2 * P)) • spatialLatticeVector k.1) ((1 / (2 * P)) • spatialLatticeVector k.2) p‖ from
       norm_mul _ _]
    exact mul_le_mul_of_nonneg_left (norm_radianBoxBlock_mode_le P hP a b d t u v k p) (norm_nonneg _)
  · exact Eventually.of_forall (hasSum_radianBoxBlock_modes_at P hP a b d t u v G c hSeries)

end Burnett.A05
