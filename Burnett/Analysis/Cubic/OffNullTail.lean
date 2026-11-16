import Burnett.Analysis.Cubic.OffNullGeometry
import Burnett.Analysis.Fourier.SchwartzTail
import Burnett.Analysis.Fourier.Modulation

noncomputable section

namespace Burnett.CubicOffNull

open MeasureTheory Filter CubicExplicit CubicFrequencies
open scoped Topology FourierTransform

theorem minkowskiQ_continuous : Continuous minkowskiQ := by
  unfold minkowskiQ
  fun_prop

theorem offNullRegion_measurableSet (δ : ℝ) : MeasurableSet (offNullRegion δ) := by
  apply MeasurableSet.inter (isClosed_singleton.measurableSet.compl)
  exact (isClosed_le (continuous_const.mul (continuous_norm.pow 2))
    minkowskiQ_continuous.abs).measurableSet

/-- An actual global integral of the translated Fourier density. The input
conditions concern only frequency geometry, not an operator's action on a
chosen sequence. -/
theorem offNull_translated_fourier_energy_tendsto_zero
    {δ : ℝ} (hδ : 0 < δ) (χ : SchwartzMap Space ℂ)
    {κ : ℕ → Space} (hκ : ∀ n, κ n ≠ 0)
    (hκnorm : Tendsto (fun n => ‖κ n‖) atTop atTop)
    (hq : ∀ᶠ n in atTop, |minkowskiQ (κ n)| ≤ (δ/8) * ‖κ n‖^2) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ, ‖𝓕 (χ : Space → ℂ) (ξ - κ n)‖^2)
      atTop (𝓝 0) := by
  let S : ℕ → Set Space := fun n => {ζ | ζ + κ n ∈ offNullRegion δ}
  have hS (n : ℕ) : MeasurableSet (S n) :=
    (offNullRegion_measurableSet δ).preimage (continuous_id.add continuous_const).measurable
  have hescape (ζ : Space) : ∀ᶠ n in atTop, ζ ∉ S n := by
    have hlim : Tendsto (fun n => separationConstant δ * ‖κ n‖) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (separationConstant_pos hδ) hκnorm
    filter_upwards [hq, hlim.eventually (Ioi_mem_atTop ‖ζ‖)] with n hqn hn
    intro hmem
    have hb := offNull_separation hδ (hκ n) hqn hmem
    simp only [add_sub_cancel_right] at hb
    linarith
  have ht := Fourier.integral_indicator_norm_sq_tendsto_zero
    (Fourier.fourier_norm_sq_integrable χ) hS hescape
  apply ht.congr'
  filter_upwards with n
  rw [← integral_indicator (offNullRegion_measurableSet δ)]
  rw [← integral_add_right_eq_self (fun ξ : Space =>
    (offNullRegion δ).indicator (fun η => ‖𝓕 (χ : Space → ℂ) (η - κ n)‖^2) ξ) (κ n)]
  apply integral_congr_ae
  filter_upwards with ζ
  by_cases h : ζ + κ n ∈ offNullRegion δ
  · simp [S, h]
  · simp [S, h]

theorem fAngularFrequency_offNull_energy_tendsto_zero
    {δ : ℝ} (hδ : 0 < δ) (χ : SchwartzMap Space ℂ) {s : ℝ} (hs : s^2 = 1) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ,
      ‖𝓕 (χ : Space → ℂ) (ξ - fAngularFrequency n s)‖^2) atTop (𝓝 0) :=
  offNull_translated_fourier_energy_tendsto_zero hδ χ
    (fun n => fAngularFrequency_ne_zero n hs) (tendsto_norm_fAngularFrequency hs)
    (fAngularFrequency_eventually_near_null hδ hs)

theorem wAngularFrequency_offNull_energy_tendsto_zero
    {δ : ℝ} (hδ : 0 < δ) (χ : SchwartzMap Space ℂ) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ,
      ‖𝓕 (χ : Space → ℂ) (ξ - wAngularFrequency n)‖^2) atTop (𝓝 0) := by
  apply offNull_translated_fourier_energy_tendsto_zero hδ χ wAngularFrequency_ne_zero
    tendsto_norm_wAngularFrequency
  filter_upwards with n
  rw [minkowskiQ_wAngularFrequency, abs_zero]
  positivity

theorem offNull_scaled_modulation_energy_tendsto_zero
    {δ c : ℝ} (hδ : 0 < δ) (hc : c ≠ 0) (χ : SchwartzMap Space ℂ)
    {κ : ℕ → Space} (hκ : ∀ n, κ n ≠ 0)
    (hκnorm : Tendsto (fun n => ‖κ n‖) atTop atTop)
    (hq : ∀ᶠ n in atTop, |minkowskiQ (κ n)| ≤ (δ/8) * ‖κ n‖^2) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ,
      ‖𝓕 (Fourier.modulate (c • κ n) (χ : Space → ℂ)) ξ‖^2) atTop (𝓝 0) := by
  have hne (n : ℕ) : c • κ n ≠ 0 := smul_ne_zero hc (hκ n)
  have hnorm : Tendsto (fun n => ‖c • κ n‖) atTop atTop := by
    simpa only [norm_smul, Real.norm_eq_abs] using
      Filter.Tendsto.const_mul_atTop (abs_pos.mpr hc) hκnorm
  have hnear : ∀ᶠ n in atTop, |minkowskiQ (c • κ n)| ≤ (δ/8) * ‖c • κ n‖^2 :=
    hq.mono (fun _ hn => near_null_smul hn)
  simpa only [Fourier.fourier_modulate] using
    offNull_translated_fourier_energy_tendsto_zero hδ χ hne hnorm hnear

/-- Both positive and negative, correctly normalized modulations of each
of the two real f-gradient phases satisfy the whole-space Fourier energy
conclusion. Their finite-sum reconstruction and the L² multiplier remain
separate obligations. -/
theorem f_normalized_mode_offNull_energy_tendsto_zero
    {δ : ℝ} (hδ : 0 < δ) (χ : SchwartzMap Space ℂ)
    {s ε : ℝ} (hs : s^2 = 1) (hε : ε ≠ 0) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ,
      ‖𝓕 (Fourier.modulate ((ε / (2 * Real.pi)) • fAngularFrequency n s)
        (χ : Space → ℂ)) ξ‖^2) atTop (𝓝 0) :=
  offNull_scaled_modulation_energy_tendsto_zero hδ
    (div_ne_zero hε (mul_ne_zero (by norm_num) Real.pi_ne_zero)) χ
    (fun n => fAngularFrequency_ne_zero n hs) (tendsto_norm_fAngularFrequency hs)
    (fAngularFrequency_eventually_near_null hδ hs)

theorem w_normalized_mode_offNull_energy_tendsto_zero
    {δ : ℝ} (hδ : 0 < δ) (χ : SchwartzMap Space ℂ)
    {ε : ℝ} (hε : ε ≠ 0) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ,
      ‖𝓕 (Fourier.modulate ((ε / (2 * Real.pi)) • wAngularFrequency n)
        (χ : Space → ℂ)) ξ‖^2) atTop (𝓝 0) := by
  apply offNull_scaled_modulation_energy_tendsto_zero hδ
    (div_ne_zero hε (mul_ne_zero (by norm_num) Real.pi_ne_zero)) χ
    wAngularFrequency_ne_zero tendsto_norm_wAngularFrequency
  filter_upwards with n
  rw [minkowskiQ_wAngularFrequency, abs_zero]
  positivity

end Burnett.CubicOffNull
