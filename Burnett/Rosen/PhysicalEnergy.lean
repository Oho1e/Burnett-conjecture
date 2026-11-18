import Burnett.Rosen.Closure

/-!
# General Rosen plane waves

The original physical data give both weak-star limits on every compact interval.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenPlaneWave

open MeasureTheory Set Filter Matrix Burnett.RosenScreen Burnett.RosenGeneralLSC AdmissibleLocal
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.CurvatureDifference
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise

private theorem physical_screen_interval_controls {I : Set ℝ} (hI : IsOpen I)
    {γn : ℕ → ℝ → Screen} {γ : ℝ → Screen}
    {r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace} (h : ScreenPhysicalSequence I γn γ r)
    (a b : ℝ) (hJ : Icc a b ⊆ I) :
    (∀ i j, TendstoUniformlyOn (fun n u => γn n u i j) (fun u => γ u i j) atTop (Icc a b)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n i j u, u ∈ Icc a b → ‖deriv (fun t => γn n t i j) u‖ ≤ C := by
  obtain ⟨hU, C, hC, hD⟩ := screen_local_controls_of_physical_admissible I hI γ γn h.limit_smooth
    h.sequence_smooth h.limit_positive r h.auxiliary_regular h.auxiliary_positive
    h.convergence h.derivative_bound (Icc a b) isCompact_Icc hJ
  refine ⟨tendstoUniformlyOn_screen2_iff_entries.mp hU, C, hC, ?_⟩
  intro n i j u hu
  rw [Real.norm_eq_abs]
  exact (screenDerivative_entry_abs_le (γn n) u i j).trans (hD n u hu)

/-- The symmetric screens converge against every fixed L¹ test on each compact interval. -/
theorem ScreenPhysicalSequence.shear_weakStar {I : Set ℝ} (hI : IsOpen I)
    {γn : ℕ → ℝ → Screen} {γ : ℝ → Screen}
    {r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace} (h : ScreenPhysicalSequence I γn γ r)
    {a b : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ I) :
    let μ : Measure ℝ := volume.restrict (Icc a b)
    ∃ C : ℝ, 0 ≤ C ∧ (∀ n, eLpNorm (screenShear (γn n)) ⊤ μ ≤ ENNReal.ofReal C) ∧
      eLpNorm (screenShear γ) ⊤ μ ≤ ENNReal.ofReal C ∧
      ∀ w : ℝ → ℝ, Integrable w μ → ∀ i j,
        (∀ n, Integrable (fun u => w u * screenShear (γn n) u i j) μ) ∧
        Integrable (fun u => w u * screenShear γ u i j) μ ∧
        Tendsto (fun n => ∫ u, w u * screenShear (γn n) u i j ∂μ) atTop
          (𝓝 (∫ u, w u * screenShear γ u i j ∂μ)) := by
  obtain ⟨hU, C, hC, hD⟩ := physical_screen_interval_controls hI h a b hJ
  exact screenS_deriv_LInf_weakStar_Icc hab hI hJ h.sequence_smooth h.limit_smooth
    h.sequence_positive h.limit_positive hU hC hD

/-- The vacuum squared energy has the actual weak-star limit `-τ'`, where `τ = tr L`. -/
theorem ScreenPhysicalSequence.energy_weakStar {I : Set ℝ} (hI : IsOpen I)
    {γn : ℕ → ℝ → Screen} {γ : ℝ → Screen}
    {r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace} (h : ScreenPhysicalSequence I γn γ r)
    {a b : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ I) :
    let μ : Measure ℝ := volume.restrict (Icc a b)
    let E := fun (n : ℕ) u => frameEnergy (screenShear (γn n) u)
    let Q := fun u => -deriv (fun t => Matrix.trace (opticalMatrix γ t)) u
    ∃ C : ℝ, 0 ≤ C ∧ (∀ n, eLpNorm (E n) ⊤ μ ≤ ENNReal.ofReal C) ∧
      eLpNorm Q ⊤ μ ≤ ENNReal.ofReal C ∧
      ∀ w : ℝ → ℝ, Integrable w μ →
        (∀ n, Integrable (fun u => w u * E n u) μ) ∧ Integrable (fun u => w u * Q u) μ ∧
          Tendsto (fun n => ∫ u, w u * E n u ∂μ) atTop (𝓝 (∫ u, w u * Q u ∂μ)) := by
  have hU (l b : ℝ) (_ : l ≤ b) (hJ : Icc l b ⊆ I) := (physical_screen_interval_controls hI h l b hJ).1
  have hD (l b : ℝ) (_ : l ≤ b) (hJ : Icc l b ⊆ I) := (physical_screen_interval_controls hI h l b hJ).2
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  have htrace (δ : ℝ → Screen) : curveScreenTrace δ = fun t => Matrix.trace (opticalMatrix δ t) := by
    funext t
    rw [opticalMatrix_eq_screenL]
    rfl
  have hVac (n : ℕ) (u : ℝ) (hu : u ∈ I) :
      -deriv (curveScreenTrace (γn n)) u = Matrix.trace ((curveScreenShape (γn n) u) ^ 2) := by
    rw [htrace, pow_two]
    change -deriv (fun t => Matrix.trace (opticalMatrix (γn n) t)) u =
      Matrix.trace (screenL (γn n u) (screenDerivative (γn n) u) * screenL (γn n u) (screenDerivative (γn n) u))
    rw [← opticalMatrix_eq_screenL]
    have hv := screenVacuum_shearLaw (γn n) I hI (fun i j => (h.sequence_smooth n i j).of_le h2)
      (h.sequence_positive n) (h.vacuum n) u hu
    have ht : (fun t => Matrix.trace (opticalMatrix (γn n) t)) =ᶠ[𝓝 u]
        (fun t => Matrix.trace (screenShear (γn n) t)) := by
      filter_upwards [hI.mem_nhds hu] with t ht
      exact opticalMatrix_trace_eq_shear (γn n) t (h.sequence_positive n t ht)
    rw [ht.deriv_eq, opticalMatrix_trace_sq (γn n) I hI (h.sequence_positive n) u hu]
    exact hv
  have hh := screenFrobeniusEnergy_LInf_weakStar_Icc hI h.sequence_smooth h.limit_smooth
    h.sequence_positive h.limit_positive hU hD hVac hab hJ
  simpa only [htrace, curveScreenMatrix, screenShear, screenDerivative] using hh

end Burnett.RosenPlaneWave
