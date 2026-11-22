import Burnett.Analysis.GaugeProjection.ProjectedDefectScalarPairing
import Burnett.Analysis.GaugeProjection.MatrixProjectionRealization

set_option autoImplicit false
set_option maxHeartbeats 4300000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.A02.FrequencySplit (E tau radianFourier_scaled mikhlin_bounded_symbol)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.X02.SobolevTestJet (D)
open Burnett.Microlocal.AngularCommutator
open scoped ContDiff ComplexConjugate FourierTransform Topology

private theorem radianScale_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

/-- The homogeneous scalar coefficient of the same four-index projection,
in the cycle-frequency convention of the F05 tests. -/
def principalProjectionComponentSymbol (a b c d : Fin 4) : BoundedSymbol E :=
  Classical.choose (mikhlin_bounded_symbol (gaugeProjectionSymbol a b c d)
    (gaugeProjectionSymbol_contDiffOn a b c d) (gaugeProjectionSymbol_scale a b c d))

theorem principalProjectionComponentSymbol_apply (a b c d : Fin 4) (ξ : E) :
    principalProjectionComponentSymbol a b c d ξ = (gaugeProjectionSymbol a b c d ξ : ℂ) :=
  Classical.choose_spec (mikhlin_bounded_symbol (gaugeProjectionSymbol a b c d)
    (gaugeProjectionSymbol_contDiffOn a b c d) (gaugeProjectionSymbol_scale a b c d)) ξ

/-- The exact infrared-regularized scalar coefficient of the projection used
on the actual fluctuation. -/
def regularizedProjectionComponentSymbol (a b c d : Fin 4) : BoundedSymbol E where
  toFun ξ := (regularizedGaugeProjectionSymbol a b c d (tau • ξ) : ℂ)
  measurable := (Complex.ofRealCLM.continuous.comp
    ((regularizedGaugeProjectionSymbol_contDiff a b c d).continuous.comp
      (continuous_const.smul continuous_id))).aestronglyMeasurable
  bound := (principalProjectionComponentSymbol a b c d).bound
  bound_nonneg := (principalProjectionComponentSymbol a b c d).bound_nonneg
  norm_le ξ := by
    have hIR : ‖(gaugeProjectionInfrared ‖tau • ξ‖ : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, gaugeProjectionInfrared,
        Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    rw [regularizedGaugeProjectionSymbol, Complex.ofReal_mul, norm_mul,
      ← principalProjectionComponentSymbol_apply]
    exact (mul_le_mul_of_nonneg_right hIR (norm_nonneg _)).trans
      (by simpa only [one_mul] using (principalProjectionComponentSymbol a b c d).norm_le (tau • ξ))

private theorem regularizedProjectionComponentSymbol_eq_off_ball
    (a b c d : Fin 4) (ξ : E) (hξ : ξ ∉ Metric.closedBall 0 (2 / tau)) :
    regularizedProjectionComponentSymbol a b c d ξ = principalProjectionComponentSymbol a b c d ξ := by
  have hNorm : 2 / tau < ‖ξ‖ := (not_le.mp (by simpa only [Metric.mem_closedBall, dist_zero_right] using hξ))
  have hHigh : 2 ≤ ‖tau • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg radianScale_pos.le, mul_comm]
    exact ((div_lt_iff₀ radianScale_pos).1 hNorm).le
  change (regularizedGaugeProjectionSymbol a b c d (tau • ξ) : ℂ) = _
  rw [regularizedGaugeProjectionSymbol_high a b c d hHigh, gaugeProjectionSymbol_scale a b c d _ radianScale_pos,
    principalProjectionComponentSymbol_apply]

/-- The exact Schwartz action is the same bounded Fourier multiplier in the
physical \(L^2\) test pairing. -/
theorem gaugeProjectionComponent_toLp_eq_multiplier (a b c d : Fin 4) (u : SchwartzMap E ℂ) :
    (gaugeProjectionSchwartzComponent a b c d u).toLp 2 volume =
      fourierMultiplier (regularizedProjectionComponentSymbol a b c d) (u.toLp 2 volume) := by
  apply (fourierL2Equiv (V := E)).injective
  rw [fourier_fourierMultiplier]
  apply Lp.ext
  filter_upwards [fourierL2Equiv_schwartz_ae (gaugeProjectionSchwartzComponent a b c d u),
    fourierL2Equiv_schwartz_ae u,
    symbolL2_ae (regularizedProjectionComponentSymbol a b c d) (fourierL2Equiv (u.toLp 2 volume))]
    with ν hP hU hM
  rw [hP, hM, hU]
  change 𝓕 (gaugeProjectionSchwartzComponent a b c d u : E → ℂ) ν =
    (regularizedGaugeProjectionSymbol a b c d (tau • ν) : ℂ) * 𝓕 (u : E → ℂ) ν
  rw [← radianFourier_scaled, ← radianFourier_scaled,
    gaugeProjectionSchwartzComponent_radianFourier]

/-- The actual projected scalar component tests have the same limit as the
original compactly localized sequences tested against the angular product
symbol. -/
theorem projectedDefectActualComponent_sub_tendsto_zero
    (i j k l i' j' k' l' : Fin 4) (a χ : BoundedSymbol E)
    (hχReal : ∀ x, conj (χ x) = χ x)
    (hχ : ContDiff ℝ ∞ (χ : E → ℂ)) (hχc : HasCompactSupport (χ : E → ℂ))
    (f g : ℕ → E → ℝ) (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hg : ∀ n, ContDiff ℝ ∞ (g n))
    (fLp : ∀ n, MemLp (f n) 2 (volume : Measure E)) (gLp : ∀ n, MemLp (g n) 2 (volume : Measure E))
    (χ₀ : D) (hχf : ∀ n x, f n x ≠ 0 → (χ₀ : E → ℝ) x = 1)
    (hχg : ∀ n x, g n x ≠ 0 → (χ₀ : E → ℝ) x = 1)
    (Bf Bg : ℝ) (hBf : ∀ n, ‖(fLp n).toLp (f n)‖ ≤ Bf) (hBg : ∀ n, ‖(gLp n).toLp (g n)‖ ≤ Bg)
    (htf : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : E → ℝ) x) atTop (𝓝 0))
    (htg : ∀ φ : D, Tendsto (fun n => ∫ x, g n x * (φ : E → ℝ) x) atTop (𝓝 0)) :
    let u := fun n => sourceSchwartz (hf n) χ₀ (hχf n)
    let v := fun n => sourceSchwartz (hg n) χ₀ (hχg n)
    let a' := projectedPairingSymbol (principalProjectionComponentSymbol i j k l) a
      (principalProjectionComponentSymbol i' j' k' l')
    Tendsto (fun n =>
      inner ℂ ((gaugeProjectionSchwartzComponent i j k l (u n)).toLp 2 volume)
        (symbolCLM χ (fourierMultiplier a ((gaugeProjectionSchwartzComponent i' j' k' l' (v n)).toLp 2 volume))) -
      inner ℂ ((u n).toLp 2 volume) (symbolCLM χ (fourierMultiplier a' ((v n).toLp 2 volume))))
      atTop (𝓝 0) := by
  intro u v a'
  let m := principalProjectionComponentSymbol i j k l
  let p := principalProjectionComponentSymbol i' j' k' l'
  let mR := regularizedProjectionComponentSymbol i j k l
  let pR := regularizedProjectionComponentSymbol i' j' k' l'
  have hM : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E) := by
    have he : (m : E → ℂ) = fun x => (gaugeProjectionSymbol i j k l x : ℂ) :=
      funext (principalProjectionComponentSymbol_apply i j k l)
    rw [he]
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (gaugeProjectionSymbol_contDiffOn i j k l)
  have hDeg : DegreeZero (m : E → ℂ) := by
    intro t ht x
    change principalProjectionComponentSymbol i j k l (t • x) = principalProjectionComponentSymbol i j k l x
    rw [principalProjectionComponentSymbol_apply, principalProjectionComponentSymbol_apply,
      gaugeProjectionSymbol_scale i j k l _ ht]
  have hReal (x : E) : conj (mR x) = mR x := Complex.conj_ofReal _
  simp only [gaugeProjectionComponent_toLp_eq_multiplier]
  exact projectedDefectScalarPairing_sub_tendsto_zero m mR p pR a χ (2 / tau)
    (regularizedProjectionComponentSymbol_eq_off_ball i j k l)
    (regularizedProjectionComponentSymbol_eq_off_ball i' j' k' l') hM hDeg hReal hχReal hχ hχc
    f g hf hg fLp gLp χ₀ hχf hχg Bf Bg hBf hBg htf htg

end Burnett.P01
