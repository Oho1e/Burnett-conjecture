import Burnett.Analysis.GaugeProjection.ProjectedDefectActualComponents

set_option autoImplicit false
set_option maxHeartbeats 3900000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.A02.FrequencySplit (E tau)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.Microlocal.AngularCommutator
open scoped ContDiff Topology

private theorem weighted_input_eq
    (ρ : BoundedSymbol E) (d : D) (hρ : ∀ x, ρ x = ((d : E → ℝ) x : ℂ))
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (χ₀ : D)
    (hCut : ∀ x, f x ≠ 0 → (χ₀ : E → ℝ) x = 1)
    (hCut' : ∀ x, (d : E → ℝ) x * f x ≠ 0 → (χ₀ : E → ℝ) x = 1) :
    (sourceSchwartz ((test_smooth d).mul hf) χ₀ hCut').toLp 2 volume =
      symbolCLM ρ ((sourceSchwartz hf χ₀ hCut).toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(sourceSchwartz ((test_smooth d).mul hf) χ₀ hCut').coeFn_toLp 2 volume,
    (sourceSchwartz hf χ₀ hCut).coeFn_toLp 2 volume,
    symbolL2_ae ρ ((sourceSchwartz hf χ₀ hCut).toLp 2 volume)]
    with x h₁ h₂ h₃
  change _ = symbolL2 ρ ((sourceSchwartz hf χ₀ hCut).toLp 2 volume) x
  rw [h₁, h₃, h₂, hρ]
  exact Complex.ofReal_mul _ _

/-- In the actual physical-space pairing the fixed smooth half-density may
be moved through the original projection, with strongly vanishing
commutator. The result uses the same compact weakly null input sequence. -/
theorem projectedDefectComponent_halfDensity_commutator_tendsto_zero
    (i j k l : Fin 4) (ρ : BoundedSymbol E) (d : D)
    (hρ : ∀ x, ρ x = ((d : E → ℝ) x : ℂ))
    (f : ℕ → E → ℝ) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (fLp : ∀ n, MemLp (f n) 2 (volume : Measure E))
    (χ₀ : D) (hCut : ∀ n x, f n x ≠ 0 → (χ₀ : E → ℝ) x = 1)
    (B : ℝ) (hB : ∀ n, ‖(fLp n).toLp (f n)‖ ≤ B)
    (hWeak : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : E → ℝ) x) atTop (𝓝 0)) :
    let w := fun n => sourceSchwartz (hf n) χ₀ (hCut n)
    let v := fun n => sourceSchwartz ((test_smooth d).mul (hf n)) χ₀
      (fun x h => hCut n x (fun h₀ => h (mul_eq_zero.mpr (Or.inr h₀))))
    Tendsto (fun n =>
      (gaugeProjectionSchwartzComponent i j k l (v n)).toLp 2 volume -
      symbolCLM ρ ((gaugeProjectionSchwartzComponent i j k l (w n)).toLp 2 volume))
      atTop (𝓝 0) := by
  intro w v
  let m := principalProjectionComponentSymbol i j k l
  let mR := regularizedProjectionComponentSymbol i j k l
  have htau : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hR (x : E) (hx : x ∉ Metric.closedBall 0 (2 / tau)) : mR x = m x := by
    have hnorm : 2 / tau < ‖x‖ := not_le.mp (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
    have hHigh : 2 ≤ ‖tau • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg htau.le, mul_comm]
      exact ((div_lt_iff₀ htau).1 hnorm).le
    change (regularizedGaugeProjectionSymbol i j k l (tau • x) : ℂ) = _
    rw [regularizedGaugeProjectionSymbol_high i j k l hHigh, gaugeProjectionSymbol_scale i j k l _ htau,
      principalProjectionComponentSymbol_apply]
  have hM : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E) := by
    rw [show (m : E → ℂ) = (fun x => (gaugeProjectionSymbol i j k l x : ℂ)) from
      funext (principalProjectionComponentSymbol_apply i j k l)]
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (gaugeProjectionSymbol_contDiffOn i j k l)
  have hDeg : DegreeZero (m : E → ℂ) := by
    intro t ht x
    change principalProjectionComponentSymbol i j k l (t • x) = principalProjectionComponentSymbol i j k l x
    rw [principalProjectionComponentSymbol_apply, principalProjectionComponentSymbol_apply,
      gaugeProjectionSymbol_scale i j k l _ ht]
  have hρSmooth : ContDiff ℝ ∞ (ρ : E → ℂ) := by
    rw [funext hρ]
    exact Complex.ofRealCLM.contDiff.comp (test_smooth d)
  have hρComp : HasCompactSupport (ρ : E → ℂ) := by
    rw [funext hρ]
    exact (test_compactSupport d).comp_left Complex.ofReal_zero
  have ht := cutoffCommutator_tendsto_zero_of_infrared_regularization m mR ρ (2 / tau) hR
    hM hDeg hρSmooth hρComp f hf fLp χ₀ hCut B hB hWeak
  refine ht.congr ?_
  intro n
  rw [gaugeProjectionComponent_toLp_eq_multiplier, gaugeProjectionComponent_toLp_eq_multiplier,
    weighted_input_eq ρ d hρ (f n) (hf n) χ₀ (hCut n)]
  rfl

end Burnett.P01
