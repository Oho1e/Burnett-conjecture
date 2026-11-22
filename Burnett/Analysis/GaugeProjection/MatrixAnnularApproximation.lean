import Burnett.Analysis.GaugeProjection.MatrixProjectionSlots
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualCutoff

set_option autoImplicit false
set_option maxHeartbeats 2900000

noncomputable section

namespace Burnett.P01

open MeasureTheory Set Metric Filter
open Burnett.Fourier
open Burnett.A02.FrequencySplit
open Burnett.A02.FrequencySplit.CMBilinearDual
open Burnett.A02.FrequencySplit (E)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open scoped ContDiff FourierTransform Topology

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private def annularSchwartzApproximation (w : SchwartzMap E ℂ) (n : ℕ) : SchwartzMap E ℂ :=
  annularInput (SchwartzMap.fourierTransformCLM ℂ w)
    ((SchwartzMap.fourierTransformCLM ℂ w).smooth ⊤).contDiffOn n

private theorem annularSchwartzApproximation_fourier (w : SchwartzMap E ℂ) (n : ℕ) (ν : E) :
    𝓕 (annularSchwartzApproximation w n : E → ℂ) ν = (inputAnnularMask n ν : ℂ) * 𝓕 (w : E → ℂ) ν :=
  annularInput_fourier _ _ _ _

private def annularL2Symbol (n : ℕ) : BoundedSymbol E :=
  { toFun := fun ν => (inputAnnularMask n ν : ℂ)
    measurable := (Complex.continuous_ofReal.comp (inputAnnularMask_contDiff n).continuous).aestronglyMeasurable
    bound := 1
    bound_nonneg := zero_le_one
    norm_le := fun ν => by simpa only [Complex.norm_real] using inputAnnularMask_norm_le n ν }

private def unitL2Symbol : BoundedSymbol E :=
  { toFun := fun _ => 1
    measurable := aestronglyMeasurable_const
    bound := 1
    bound_nonneg := zero_le_one
    norm_le := fun _ => by simp }

private theorem fourierMultiplier_unitL2 (u : ComplexL2 E) :
    fourierMultiplier unitL2Symbol u = u := by
  apply fourierL2Equiv.injective
  rw [fourier_fourierMultiplier]
  apply Lp.ext
  simpa only [unitL2Symbol, one_mul] using symbolL2_ae unitL2Symbol (fourierL2Equiv u)

private theorem annularSchwartzApproximation_toLp (w : SchwartzMap E ℂ) (n : ℕ) :
    (annularSchwartzApproximation w n).toLp 2 volume =
      fourierMultiplier (annularL2Symbol n) (w.toLp 2 volume) := by
  apply fourierL2Equiv.injective
  rw [fourier_fourierMultiplier]
  apply Lp.ext
  filter_upwards [fourierL2Equiv_schwartz_ae (annularSchwartzApproximation w n),
    symbolL2_ae (annularL2Symbol n) (fourierL2Equiv (w.toLp 2 volume)),
    fourierL2Equiv_schwartz_ae w] with ν ha hb hw
  rw [ha, hb, hw, annularSchwartzApproximation_fourier]
  rfl

private theorem annularSchwartzApproximation_tendsto (w : SchwartzMap E ℂ) :
    Tendsto (fun n => (annularSchwartzApproximation w n).toLp 2 volume) atTop (𝓝 (w.toLp 2 volume)) := by
  have hm : ∀ᵐ ν ∂(volume : Measure E), ∀ᶠ n : ℕ in atTop,
      annularL2Symbol n ν = unitL2Symbol ν := by
    filter_upwards [(Set.countable_singleton (0 : E)).ae_notMem volume] with ν hν
    filter_upwards [inputAnnularMask_eventually_one (fun hz => hν (Set.mem_singleton_iff.mpr hz))]
      with n hn
    simp only [annularL2Symbol, unitL2Symbol, hn, Complex.ofReal_one]
  have ht := mikhlin_strong_L2 unitL2Symbol annularL2Symbol 1
    (fun n ν => (annularL2Symbol n).norm_le ν) hm (w.toLp 2 volume)
  simpa only [← annularSchwartzApproximation_toLp, fourierMultiplier_unitL2] using ht

private theorem annularSchwartzApproximation_derivative (b : Fin 4) (w : SchwartzMap E ℂ) (n : ℕ) :
    coordinateDerivative b (annularSchwartzApproximation w n) =
      annularSchwartzApproximation (coordinateDerivative b w) n := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext ν
  change 𝓕 (coordinateDerivative b (annularSchwartzApproximation w n) : E → ℂ) ν =
      𝓕 (annularSchwartzApproximation (coordinateDerivative b w) n : E → ℂ) ν
  have h (u : SchwartzMap E ℂ) :
      𝓕 (coordinateDerivative b u : E → ℂ) ν = Complex.I * ((tau • ν) b : ℂ) * 𝓕 (u : E → ℂ) ν := by
    rw [← radianFourier_scaled, ← radianFourier_scaled, radianFourier_coordinateDerivative]
  rw [h, annularSchwartzApproximation_fourier, annularSchwartzApproximation_fourier, h]
  ring

private theorem annularMask_norms (n : ℕ) {ν : E} (hn : inputAnnularMask n ν ≠ 0) :
    (inputCutoffRadius n)⁻¹ ≤ ‖ν‖ ∧ ‖ν‖ ≤ 2 * inputCutoffRadius n := by
  have hR := inputCutoffRadius_pos n
  have hR₁ : 1 ≤ inputCutoffRadius n := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hn₀ : 0 ≤ ‖ν‖ := norm_nonneg _
  have lo (u : E) (h : ‖u‖ ≤ 1) : mikhlinBall u = 1 :=
    mikhlinBall.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr h)
  have hi (u : E) (h : 2 ≤ ‖u‖) : mikhlinBall u = 0 :=
    mikhlinBall.zero_of_le_dist (by simpa only [dist_zero_right] using h)
  have hd r (hr : 0 ≤ r) : ‖r • ν‖ = r * ‖ν‖ := by rw [norm_smul, Real.norm_of_nonneg hr]
  have hinv : (inputCutoffRadius n)⁻¹ ≤ inputCutoffRadius n :=
    (inv_le_one_of_one_le₀ hR₁).trans hR₁
  constructor
  · by_contra h
    have hh : inputCutoffRadius n * ‖ν‖ ≤ 1 :=
      (mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) hR.le).trans_eq
        (mul_inv_cancel₀ hR.ne')
    have hsmall : ‖(inputCutoffRadius n)⁻¹ • ν‖ ≤ 1 := by
      rw [hd _ (inv_nonneg.mpr hR.le)]
      exact (mul_le_mul_of_nonneg_right hinv hn₀).trans hh
    rw [inputAnnularMask, lo _ hsmall, lo _ (by rw [hd _ hR.le]; exact hh), sub_self] at hn
    exact hn rfl
  · by_contra h
    have hh : 2 ≤ (inputCutoffRadius n)⁻¹ * ‖ν‖ := by
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hR).mpr (le_of_lt (lt_of_not_ge h))
    have hlarge : 2 ≤ ‖inputCutoffRadius n • ν‖ := by
      rw [hd _ hR.le]
      exact hh.trans (mul_le_mul_of_nonneg_right hinv hn₀)
    rw [inputAnnularMask, hi _ (by rw [hd _ (inv_nonneg.mpr hR.le)]; exact hh),
      hi _ hlarge, sub_self] at hn
    exact hn rfl

/-- The original field and each of its coordinate derivatives are approximated
by the same genuine compact annular Fourier cutoff. -/
def projectionMatrixAnnularApproximation (w : ProjectionSchwartzMatrix) (n : ℕ) :
    ProjectionSchwartzMatrix := fun i j => annularSchwartzApproximation (w i j) n

theorem projectionMatrixAnnularApproximation_compact (w : ProjectionSchwartzMatrix) (n : ℕ) :
    ∃ K : Set E, IsCompact K ∧ (0 : E) ∉ K ∧
      ∀ i j, tsupport (radianFourier (projectionMatrixAnnularApproximation w n i j : E → ℂ)) ⊆ K := by
  let r := inputCutoffRadius n
  let S : Set E := {ν | r⁻¹ ≤ ‖ν‖} ∩ closedBall 0 (2 * r)
  have hS : IsCompact S :=
    (isCompact_closedBall (0 : E) (2 * r)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter isClosed_closedBall) inter_subset_right
  let K := (fun ν : E => tau • ν) '' S
  have hK : IsCompact K := hS.image (continuous_const.smul continuous_id)
  have h0 : (0 : E) ∉ K := by
    rintro ⟨ν, hν, hz⟩
    have heq : ν = 0 := (smul_eq_zero.mp hz).resolve_left tau_pos.ne'
    have h : r⁻¹ ≤ ‖ν‖ := hν.1
    rw [heq, norm_zero] at h
    exact (inv_pos.mpr (inputCutoffRadius_pos n)).not_ge h
  refine ⟨K, hK, h0, fun i j => closure_minimal (fun ξ hξ => ?_) hK.isClosed⟩
  let ν := tau⁻¹ • ξ
  have hx : tau • ν = ξ := by dsimp only [ν]; rw [smul_smul, mul_inv_cancel₀ tau_pos.ne', one_smul]
  have hν : inputAnnularMask n ν ≠ 0 := by
    intro hz
    apply hξ
    change radianFourier (annularSchwartzApproximation (w i j) n) ξ = 0
    rw [← hx, radianFourier_scaled, annularSchwartzApproximation_fourier, hz, Complex.ofReal_zero, zero_mul]
  obtain ⟨hl, hu⟩ := annularMask_norms n hν
  exact ⟨ν, ⟨hl, mem_closedBall_zero_iff.mpr hu⟩, hx⟩

theorem projectionMatrixAnnularApproximation_tendsto (w : ProjectionSchwartzMatrix) :
    Tendsto (fun n => projectionMatrixToL2 (projectionMatrixAnnularApproximation w n))
      atTop (𝓝 (projectionMatrixToL2 w)) := by
  apply tendsto_pi_nhds.2
  intro i
  exact tendsto_pi_nhds.2 fun j => annularSchwartzApproximation_tendsto (w i j)

theorem projectionMatrixAnnularApproximation_derivative_tendsto (b : Fin 4)
    (w : ProjectionSchwartzMatrix) :
    Tendsto (fun n => projectionMatrixToL2
      (projectionMatrixDerivative b (projectionMatrixAnnularApproximation w n)))
      atTop (𝓝 (projectionMatrixToL2 (projectionMatrixDerivative b w))) := by
  have e (n : ℕ) : projectionMatrixDerivative b (projectionMatrixAnnularApproximation w n) =
      projectionMatrixAnnularApproximation (projectionMatrixDerivative b w) n :=
    funext fun i => funext fun j => annularSchwartzApproximation_derivative b (w i j) n
  simp_rw [e]
  exact projectionMatrixAnnularApproximation_tendsto (projectionMatrixDerivative b w)

end Burnett.P01
