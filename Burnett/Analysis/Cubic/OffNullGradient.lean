import Burnett.Analysis.Cubic.OffNullTail
import Burnett.Analysis.Fourier.Cosine
import Burnett.Analysis.Fourier.FiniteEnergy

noncomputable section

namespace Burnett.CubicOffNull

open MeasureTheory Filter CubicExplicit CubicFrequencies
open scoped Topology FourierTransform RealInnerProductSpace BigOperators

def fModeFrequency (n : ℕ) (j : Fin 4) : Space :=
  if j = 0 then (2 * Real.pi)⁻¹ • fAngularFrequency n 1 else
  if j = 1 then -((2 * Real.pi)⁻¹ • fAngularFrequency n 1) else
  if j = 2 then (2 * Real.pi)⁻¹ • fAngularFrequency n (-1) else
    -((2 * Real.pi)⁻¹ • fAngularFrequency n (-1))

def fModeCoefficient (n : ℕ) (i : Index) (j : Fin 4) : ℝ :=
  if j = 0 ∨ j = 1 then (u (basis i) + (N n)⁻¹ * v (basis i)) / 4
    else (u (basis i) - (N n)⁻¹ * v (basis i)) / 4

theorem fModeCoefficient_abs_le_one (n : ℕ) (i : Index) (j : Fin 4) :
    |fModeCoefficient n i j| ≤ 1 := by
  have hi0 : 0 ≤ (N n)⁻¹ := inv_nonneg.mpr (N_pos n).le
  have hi1 : (N n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (N_ge_one n)
  fin_cases i <;> fin_cases j <;>
    norm_num [fModeCoefficient, u_basis, v_basis] <;>
    apply abs_le.mpr <;> constructor <;> linarith

/-- The Fourier transform of the actual compactly localized coordinate
gradient of the original f sequence, with all four signed modes. -/
theorem fourier_localized_fGradient (χ : SchwartzMap Space ℂ) (n : ℕ) (i : Index) (ξ : Space) :
    𝓕 (fun x => χ x * (CubicExplicit.D i (fSequence n) x : ℂ)) ξ =
      ∑ j : Fin 4, (fModeCoefficient n i j : ℂ) *
        𝓕 (χ : Space → ℂ) (ξ - fModeFrequency n j) := by
  let a : ℝ := (u (basis i) + (N n)⁻¹ * v (basis i)) / 2
  let b : ℝ := (u (basis i) - (N n)⁻¹ * v (basis i)) / 2
  have hfun : (fun x => χ x * (CubicExplicit.D i (fSequence n) x : ℂ)) =
      (a : ℂ) • (fun x => χ x * (Real.cos ⟪fAngularFrequency n 1, x⟫ : ℂ)) +
      (b : ℂ) • (fun x => χ x * (Real.cos ⟪fAngularFrequency n (-1), x⟫ : ℂ)) := by
    funext x
    rw [D_fSequence_two_cosines]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
      Complex.ofReal_mul]
    dsimp [a, b]
    push_cast
    ring
  rw [hfun, Fourier.fourier_add
    ((Fourier.cosine_integrable _ χ.integrable).smul (a : ℂ))
    ((Fourier.cosine_integrable _ χ.integrable).smul (b : ℂ)),
    Fourier.fourier_const_smul, Fourier.fourier_const_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Fourier.fourier_cosine _ χ.integrable]
  simp [fModeCoefficient, fModeFrequency, Fin.sum_univ_succ, sub_neg_eq_add, a, b]
  ring

theorem fMode_offNull_energy_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (χ : SchwartzMap Space ℂ) (j : Fin 4) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ,
      ‖𝓕 (χ : Space → ℂ) (ξ - fModeFrequency n j)‖^2) atTop (𝓝 0) := by
  have hp := f_normalized_mode_offNull_energy_tendsto_zero hδ χ
    (s := 1) (ε := 1) (by norm_num) (by norm_num)
  have hn := f_normalized_mode_offNull_energy_tendsto_zero hδ χ
    (s := 1) (ε := -1) (by norm_num) (by norm_num)
  have hmp := f_normalized_mode_offNull_energy_tendsto_zero hδ χ
    (s := -1) (ε := 1) (by norm_num) (by norm_num)
  have hmn := f_normalized_mode_offNull_energy_tendsto_zero hδ χ
    (s := -1) (ε := -1) (by norm_num) (by norm_num)
  fin_cases j
  · simpa [Fourier.fourier_modulate, fModeFrequency] using hp
  · simpa [Fourier.fourier_modulate, fModeFrequency, neg_div, one_div, neg_smul] using hn
  · simpa [Fourier.fourier_modulate, fModeFrequency] using hmp
  · simpa [Fourier.fourier_modulate, fModeFrequency, neg_div, one_div, neg_smul] using hmn

/-- Whole-space Fourier off-null energy for each actual component χ∂fₙ,
with the same fSequence and every fixed Schwartz cutoff χ and δ>0. -/
theorem localized_fGradient_offNull_energy_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (χ : SchwartzMap Space ℂ) (i : Index) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ,
      ‖𝓕 (fun x => χ x * (CubicExplicit.D i (fSequence n) x : ℂ)) ξ‖^2)
      atTop (𝓝 0) := by
  let G : ℕ → Fin 4 → Space → ℂ :=
    fun n j ξ => 𝓕 (χ : Space → ℂ) (ξ - fModeFrequency n j)
  have hm (n : ℕ) (j : Fin 4) : AEStronglyMeasurable (G n j)
      (volume.restrict (offNullRegion δ)) :=
    (((SchwartzMap.fourierTransformCLM ℂ χ).continuous.comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable).restrict
  have hi (n : ℕ) (j : Fin 4) : Integrable (fun ξ => ‖G n j ξ‖^2)
      (volume.restrict (offNullRegion δ)) := by
    have ht := (Fourier.fourier_norm_sq_integrable χ).comp_add_right (-fModeFrequency n j)
    have hwhole : Integrable (fun ξ => ‖G n j ξ‖^2) (volume : Measure Space) := by
      simpa only [G, sub_eq_add_neg] using ht
    exact hwhole.restrict
  have ha (n : ℕ) (j : Fin 4) : ‖(fModeCoefficient n i j : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using fModeCoefficient_abs_le_one n i j
  have ht := Fourier.finite_energy_tendsto_zero hm hi ha
    (fun j => fMode_offNull_energy_tendsto_zero hδ χ j)
  simpa only [G, ← fourier_localized_fGradient] using ht

def wModeFrequency (n : ℕ) (j : Fin 2) : Space :=
  if j = 0 then (2 * Real.pi)⁻¹ • wAngularFrequency n
    else -((2 * Real.pi)⁻¹ • wAngularFrequency n)

theorem fourier_localized_wGradient (χ : SchwartzMap Space ℂ) (n : ℕ) (i : Index) (ξ : Space) :
    𝓕 (fun x => χ x * (CubicExplicit.D i (wSequence n) x : ℂ)) ξ =
      ∑ j : Fin 2, ((v (basis i) / 2 : ℝ) : ℂ) *
        𝓕 (χ : Space → ℂ) (ξ - wModeFrequency n j) := by
  have hfun : (fun x => χ x * (CubicExplicit.D i (wSequence n) x : ℂ)) =
      (v (basis i) : ℂ) • (fun x => χ x * (Real.cos ⟪wAngularFrequency n, x⟫ : ℂ)) := by
    funext x
    rw [D_wSequence_cosine]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  rw [hfun, Fourier.fourier_const_smul]
  simp only [Pi.smul_apply, smul_eq_mul, Fourier.fourier_cosine _ χ.integrable]
  simp [wModeFrequency, Fin.sum_univ_succ, sub_neg_eq_add]
  ring

theorem wMode_offNull_energy_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (χ : SchwartzMap Space ℂ) (j : Fin 2) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ,
      ‖𝓕 (χ : Space → ℂ) (ξ - wModeFrequency n j)‖^2) atTop (𝓝 0) := by
  have hp := w_normalized_mode_offNull_energy_tendsto_zero hδ χ (ε := 1) (by norm_num)
  have hn := w_normalized_mode_offNull_energy_tendsto_zero hδ χ (ε := -1) (by norm_num)
  fin_cases j
  · simpa [Fourier.fourier_modulate, wModeFrequency] using hp
  · simpa [Fourier.fourier_modulate, wModeFrequency, neg_div, one_div, neg_smul] using hn

theorem localized_wGradient_offNull_energy_tendsto_zero {δ : ℝ} (hδ : 0 < δ)
    (χ : SchwartzMap Space ℂ) (i : Index) :
    Tendsto (fun n => ∫ ξ in offNullRegion δ,
      ‖𝓕 (fun x => χ x * (CubicExplicit.D i (wSequence n) x : ℂ)) ξ‖^2)
      atTop (𝓝 0) := by
  let G : ℕ → Fin 2 → Space → ℂ :=
    fun n j ξ => 𝓕 (χ : Space → ℂ) (ξ - wModeFrequency n j)
  have hm (n : ℕ) (j : Fin 2) : AEStronglyMeasurable (G n j)
      (volume.restrict (offNullRegion δ)) :=
    (((SchwartzMap.fourierTransformCLM ℂ χ).continuous.comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable).restrict
  have hi (n : ℕ) (j : Fin 2) : Integrable (fun ξ => ‖G n j ξ‖^2)
      (volume.restrict (offNullRegion δ)) := by
    have ht := (Fourier.fourier_norm_sq_integrable χ).comp_add_right (-wModeFrequency n j)
    have hwhole : Integrable (fun ξ => ‖G n j ξ‖^2) (volume : Measure Space) := by
      simpa only [G, sub_eq_add_neg] using ht
    exact hwhole.restrict
  have ha (n : ℕ) (j : Fin 2) : ‖((v (basis i) / 2 : ℝ) : ℂ)‖ ≤ 1 := by
    fin_cases i <;> norm_num [v_basis]
  have ht := Fourier.finite_energy_tendsto_zero hm hi ha
    (fun j => wMode_offNull_energy_tendsto_zero hδ χ j)
  simpa only [G, ← fourier_localized_wGradient] using ht

end Burnett.CubicOffNull
