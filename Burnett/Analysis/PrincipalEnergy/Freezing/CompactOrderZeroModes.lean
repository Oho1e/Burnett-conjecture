import Burnett.Analysis.PrincipalEnergy.Freezing.CompactBaseFourierModes
import Burnett.Analysis.PrincipalEnergy.Freezing.RadianOrderZeroSymbols
import Burnett.Analysis.PrincipalEnergy.Freezing.SummableModeFourierMoments

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal

/-- The real cosine and sine angular profiles of the same compact-base
symbol. The normalization uses all lattice points. -/
def compactBaseRealMode (P : ℝ) (a : E → E → ℝ) (k : Index → ℤ) (j : Fin 2) (ξ : E) : ℝ :=
  let c := compactBaseCubeCoefficient P (fun x q => (a x q : ℂ)) k ξ
  if j = 0 then c.re else -c.im

/-- Fixed physical cutoff modes, using a unit rescaling at the origin. -/
def compactBaseSpatialMode (P : ℝ) (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (support : tsupport ρ ⊆ ball (0 : E) P) (k : Index → ℤ) (j : Fin 2) : SchwartzMap E ℂ :=
  localizedRealSpatialModeSchwartz P k ρ hρ support 0 1 zero_lt_one j

theorem compact_base_spatial_mode_apply (P : ℝ) (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (support : tsupport ρ ⊆ ball (0 : E) P) (k : Index → ℤ) (j : Fin 2) (x : E) :
    compactBaseSpatialMode P ρ hρ support k j x =
      (ρ x * (if j = 0 then Real.cos (spatialModePhase P k x)
        else Real.sin (spatialModePhase P k x)) : ℝ) := by
  rw [compactBaseSpatialMode, localized_real_spatial_mode_schwartz_apply]
  by_cases h : j = 0
  · simp [localizedRealSpatialModeProfile, localizedSpatialCosineProfile, h]
  · simp [localizedRealSpatialModeProfile, localizedSpatialSineProfile, h]

private def compactBaseReadCoefficient (j : Fin 2) : ℂ →L[ℝ] ℝ :=
  if j = 0 then Complex.reCLM else -Complex.imCLM

private theorem compact_base_read_coefficient_norm (j : Fin 2) :
    ‖compactBaseReadCoefficient j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  by_cases h : j = 0
  · simpa [compactBaseReadCoefficient, h, Real.norm_eq_abs] using Complex.abs_re_le_norm z
  · simpa [compactBaseReadCoefficient, h, Real.norm_eq_abs] using Complex.abs_im_le_norm z

private theorem compact_base_real_mode_eq_comp (P : ℝ) (a : E → E → ℝ)
    (k : Index → ℤ) (j : Fin 2) :
    compactBaseRealMode P a k j =
      compactBaseReadCoefficient j ∘ compactBaseCubeCoefficient P (fun x q => (a x q : ℂ)) k := by
  funext ξ
  by_cases h : j = 0 <;> simp [compactBaseRealMode, compactBaseReadCoefficient, h]

theorem compact_base_real_mode_smooth (P : ℝ) (a : E → E → ℝ)
    (U : Set E) (hU : IsOpen U) (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) U)
    (k : Index → ℤ) (j : Fin 2) :
    ContDiffOn ℝ ∞ (compactBaseRealMode P a k j) U := by
  rw [compact_base_real_mode_eq_comp]
  exact (compactBaseReadCoefficient j).contDiff.fun_comp_contDiffOn
    (compact_base_cube_coefficient_smooth P _ U hU ha k)

/-- Compact-base reconstruction using the same real symbol, physical modes,
and complex cube coefficients. -/
theorem compact_base_real_symbol_hasSum (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (a : E → E → ℝ) (ξ : E) (hC : Continuous (fun x => a x ξ))
    (support : ∀ x, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (s : Summable (fun k => compactBaseCubeCoefficient P (fun x q => (a x q : ℂ)) k ξ))
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1) (x : E) :
    HasSum (fun k : Index → ℤ => ∑ j : Fin 2,
      compactBaseSpatialMode P ρ hρ hS k j x * (compactBaseRealMode P a k j ξ : ℂ)) (a x ξ : ℂ) := by
  have aS : tsupport (fun y => a y ξ) ⊆ closedBall (0 : E) R := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    by_contra bad
    exact hy (support y bad)
  have ρS : Function.support ρ ⊆ spatialFourierCube P :=
    subset_closure.trans (hS.trans (ball_subset_closedBall.trans (closed_ball_subset_spatial_fourier_cube P P le_rfl)))
  have H := hasSum_cutoff_spatial_cube_real_series P R hP hRP (fun y => a y ξ) hC aS s ρ ρS
    (fun y hy => ρone y (aS hy)) x
  apply (Complex.ofRealCLM.hasSum H).congr_fun
  intro k
  simp [Fin.sum_univ_two, compact_base_spatial_mode_apply, compactBaseRealMode,
    spatialRealProfileCoefficient, compactBaseCubeCoefficient]

/-- A fixed compact-base order-zero full symbol budget, with the eight base
derivatives needed for the absolute mode sum. These are mixed jets of the
actual symbol rather than independent coefficient assumptions. -/
def CompactBaseOrderZeroBudget (a : E → E → ℝ) (M : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ 8 → ∀ ξ : E, ξ ≠ 0 → ∀ x : E,
    ‖ξ‖ ^ n * ‖iteratedFDeriv ℝ n (fun q => (a x q : ℂ)) ξ‖ ≤ M ∧
      ‖ξ‖ ^ n * ‖iteratedFDeriv ℝ 8
        (fun y => iteratedFDeriv ℝ n (fun q => (a y q : ℂ)) ξ) x‖ ≤ M

/-- The exact real angular coefficients of a compact-base nonhomogeneous
order-zero full symbol inherit a summably decaying Mikhlin budget. -/
theorem compact_base_order_zero_real_mode_budget (P R : ℝ) (hP : 0 < P) (hRP : R ≤ P)
    (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) univ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderZeroBudget a M)
    (k : Index → ℤ) (j : Fin 2) :
    ContDiff ℝ ∞ (compactBaseRealMode P a k j) ∧
      MikhlinOrderZeroBudget (compactBaseRealMode P a k j)
        (max 1 ((3 / spatialModeRate P)^8) * M / spatialLatticeWeight k ^ 8) := by
  let β := compactBaseCubeCoefficient P (fun x q => (a x q : ℂ)) k
  let L := compactBaseReadCoefficient j
  have hβ : ContDiff ℝ ∞ β := contDiffOn_univ.mp
    (compact_base_cube_coefficient_smooth P _ univ isOpen_univ ha k)
  have hL := compact_base_read_coefficient_norm j
  refine ⟨contDiffOn_univ.mp (compact_base_real_mode_smooth P a univ isOpen_univ ha k j), ?_⟩
  intro n hn ξ hξ
  have positive : 0 < ‖ξ‖ ^ n := pow_pos (norm_pos_iff.mpr hξ) n
  let D := M / ‖ξ‖ ^ n
  have D0 : 0 ≤ D := div_nonneg M0 positive.le
  have B := compact_base_cube_coefficient_jet_decay P R hP hRP
    (fun x q => (a x q : ℂ)) (fun x q hx => by simp [support x q hx])
    univ isOpen_univ ha n 8 ξ (mem_univ _) D D0
    (fun x => (le_div_iff₀ positive).mpr (by simpa [mul_comm] using (hM n hn ξ hξ x).1))
    (fun x => (le_div_iff₀ positive).mpr (by simpa [mul_comm] using (hM n hn ξ hξ x).2)) k
  have reg : (n : WithTop ℕ∞) ≤ ⊤ := le_top
  rw [compact_base_real_mode_eq_comp, L.iteratedFDeriv_comp_left hβ.contDiffAt (by exact_mod_cast le_top)]
  have comp : ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ n β ξ)‖ ≤ ‖iteratedFDeriv ℝ n β ξ‖ :=
    (L.norm_compContinuousMultilinearMap_le _).trans (mul_le_of_le_one_left (norm_nonneg _) hL)
  calc
    _ ≤ ‖ξ‖ ^ n * ‖iteratedFDeriv ℝ n β ξ‖ := mul_le_mul_of_nonneg_left comp positive.le
    _ ≤ ‖ξ‖ ^ n * ((max 1 ((3 / spatialModeRate P)^8) * D) / spatialLatticeWeight k ^ 8) :=
      mul_le_mul_of_nonneg_left B positive.le
    _ = _ := by
      dsimp only [D]
      field_simp [positive.ne']

end Burnett.A03
