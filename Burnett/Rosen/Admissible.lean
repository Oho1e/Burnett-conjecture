import Burnett.Rosen.Geometry
import Burnett.Geometry.AuxiliaryPhysicalBound
import Burnett.Analysis.PositiveDensity
import Mathlib.Analysis.Matrix

/-!
# General Rosen plane waves

The physical local assumptions imply the one-dimensional screen estimates.
-/

set_option autoImplicit false

noncomputable section

noncomputable section

namespace Burnett.RosenPlaneWave.AdmissibleLocal

open Set Filter MeasureTheory Burnett.RicciSymbol
open Burnett.RosenPlaneWave
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.AuxiliaryConnection Burnett.Geometry.AuxiliaryPhysicalBound
open Burnett.Geometry.CovariantTensorNorm
open scoped Topology ContDiff ENNReal BigOperators Matrix.Norms.Elementwise

def screenSlab (I : Set ℝ) : Set CoordinateSpace := {x | x 0 ∈ I}

theorem screenSlab_isOpen {I : Set ℝ} (hI : IsOpen I) : IsOpen (screenSlab I) :=
  hI.preimage (EuclideanSpace.proj (0 : Index)).continuous

def screenAxis (u : ℝ) : CoordinateSpace := EuclideanSpace.single 0 u

theorem screenAxis_zero (u : ℝ) : screenAxis u 0 = u := by
  simp [screenAxis]

theorem screenAxis_continuous : Continuous screenAxis := by
  have he : screenAxis = fun u : ℝ => u • (EuclideanSpace.single 0 1 : CoordinateSpace) := by
    funext u
    ext k
    by_cases hk : k = 0 <;> simp [screenAxis, hk, PiLp.smul_apply, smul_eq_mul]
  rw [he]
  exact continuous_id.smul continuous_const

def screenIndex (i : Fin 2) : Index := ⟨i.val + 2, by omega⟩

theorem screenMetric_screenEntry (M : Screen) (i j : Fin 2) :
    screenMetric M (screenIndex i) (screenIndex j) = M i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem screenJet_u_screenEntry (M : Screen) (i j : Fin 2) :
    screenJet M 0 (screenIndex i) (screenIndex j) = M i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem screen_sub_norm_le (A B : Screen) :
    ‖A - B‖ ≤ ‖screenMetric A - screenMetric B‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg _)).2
  intro i j
  have h := (norm_le_pi_norm (fun k => (screenMetric A - screenMetric B) (screenIndex i) k)
    (screenIndex j)).trans (norm_le_pi_norm (screenMetric A - screenMetric B) (screenIndex i))
  have he : (screenMetric A - screenMetric B) (screenIndex i) (screenIndex j) = A i j - B i j := by
    change screenMetric A (screenIndex i) (screenIndex j) -
      screenMetric B (screenIndex i) (screenIndex j) = _
    rw [screenMetric_screenEntry, screenMetric_screenEntry]
  rw [he] at h
  exact h


theorem screenBilinear_components_contDiffOn (I : Set ℝ) (γ : ℝ → Screen)
    (hγ : ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun u => γ u i j) I) (a b : Index) :
    ContDiffOn ℝ ∞ (fun x => metricComponents (screenBilinear γ) x a b) (screenSlab I) := by
  let π : CoordinateSpace →L[ℝ] ℝ := EuclideanSpace.proj 0
  have h (i j : Fin 2) : ContDiffOn ℝ ∞
      (fun x : CoordinateSpace => γ (x 0) i j) (screenSlab I) :=
    (hγ i j).comp π.contDiff.contDiffOn (fun _ hx => hx)
  rw [screenBilinear_components]
  fin_cases a <;> fin_cases b <;> simp [screenMetric]
  all_goals first | exact contDiffOn_const | apply h

theorem screenDerivative_continuousOn (I : Set ℝ) (hI : IsOpen I) (γ : ℝ → Screen)
    (hγ : ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun u => γ u i j) I) :
    ContinuousOn (screenDerivative γ) I := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j u hu
  have hs : ContDiffAt ℝ ((1 : WithTop ℕ∞) + 1) (fun t => γ t i j) u :=
    ((hγ i j).contDiffAt (hI.mem_nhds hu)).of_le (by
      change ((1 : ℕ∞) : WithTop ℕ∞) + 1 ≤ ↑(⊤ : ℕ∞)
      norm_num
      exact WithTop.coe_le_coe.mpr le_top)
  have hd : ContDiffAt ℝ 1 (deriv fun t => γ t i j) u := by
    simpa only [deriv] using hs.fderiv_right_succ.clm_apply
      (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℝ => (1 : ℝ)) u)
  exact hd.continuousAt.continuousWithinAt

theorem screenDerivative_entry_abs_le (γ : ℝ → Screen) (u : ℝ) (i j : Fin 2) :
    |deriv (fun t => γ t i j) u| ≤ ‖screenDerivative γ u‖ := by
  simpa only [screenDerivative, Real.norm_eq_abs] using
    (Matrix.norm_entry_le_entrywise_sup_norm (screenDerivative γ u) (i := i) (j := j))

theorem screenBilinear_rawJet_sub_screenEntry (I : Set ℝ) (hI : IsOpen I)
    (γ₁ γ₀ : ℝ → Screen)
    (hγ₁ : ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun u => γ₁ u i j) I)
    (hγ₀ : ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun u => γ₀ u i j) I)
    (x : CoordinateSpace) (hx : x ∈ screenSlab I) (i j : Fin 2) :
    coordinateJet (fun y => metricComponents (screenBilinear γ₁) y -
      metricComponents (screenBilinear γ₀) y) x 0 (screenIndex i) (screenIndex j) =
      screenDerivative γ₁ (x 0) i j - screenDerivative γ₀ (x 0) i j := by
  have hc₁ := fun a b => ((screenBilinear_components_contDiffOn I γ₁ hγ₁ a b).contDiffAt
    ((screenSlab_isOpen hI).mem_nhds hx)).differentiableAt (by simp)
  have hc₀ := fun a b => ((screenBilinear_components_contDiffOn I γ₀ hγ₀ a b).contDiffAt
    ((screenSlab_isOpen hI).mem_nhds hx)).differentiableAt (by simp)
  rw [coordinateJet_sub _ _ x hc₁ hc₀]
  rw [screenBilinear_coordinateJet γ₁ x (fun a b =>
      ((hγ₁ a b).contDiffAt (hI.mem_nhds hx)).differentiableAt (by simp)),
    screenBilinear_coordinateJet γ₀ x (fun a b =>
      ((hγ₀ a b).contDiffAt (hI.mem_nhds hx)).differentiableAt (by simp))]
  simp only [Pi.sub_apply, screenJet_u_screenEntry]

end Burnett.RosenPlaneWave.AdmissibleLocal


noncomputable section

namespace Burnett.RosenPlaneWave.AdmissibleLocal

open Set Filter MeasureTheory Burnett.RicciSymbol
open Burnett.RosenPlaneWave
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.AuxiliaryConnection Burnett.Geometry.AuxiliaryPhysicalBound
open Burnett.Geometry.CovariantTensorNorm
open scoped Topology ContDiff ENNReal BigOperators Matrix.Norms.Elementwise

private theorem screenDerivative_bound_all {I K : Set ℝ} (hI : IsOpen I)
    (hK : IsCompact K) (hKI : K ⊆ I) (γn : ℕ → ℝ → Screen)
    (hγn : ∀ n (i j : Fin 2), ContDiffOn ℝ ∞ (fun u => γn n u i j) I)
    {C : ℝ} (hC : 0 ≤ C)
    (htail : ∀ᶠ n in atTop, ∀ u ∈ K, ‖screenDerivative (γn n) u‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n u, u ∈ K → ‖screenDerivative (γn n) u‖ ≤ B := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  have hfinite : ∀ k : Fin N, ∃ A : ℝ, 0 ≤ A ∧
      ∀ u ∈ K, ‖screenDerivative (γn k) u‖ ≤ A := by
    intro k
    obtain ⟨A, hA⟩ := hK.bddAbove_image
      (((screenDerivative_continuousOn I hI (γn k) (hγn k)).mono hKI).norm)
    exact ⟨max A 0, le_max_right _ _, fun u hu =>
      (hA (mem_image_of_mem _ hu)).trans (le_max_left _ _)⟩
  choose A hA hs using hfinite
  have hsum : (0 : ℝ) ≤ ∑ k : Fin N, A k := Finset.sum_nonneg fun k _ => hA k
  refine ⟨C + ∑ k : Fin N, A k, add_nonneg hC hsum, ?_⟩
  intro n u hu
  by_cases hn : N ≤ n
  · exact (hN n hn u hu).trans (le_add_of_nonneg_right hsum)
  · let k : Fin N := ⟨n, Nat.lt_of_not_ge hn⟩
    exact (hs k u hu).trans ((Finset.single_le_sum (fun j _ => hA j)
      (Finset.mem_univ k)).trans (le_add_of_nonneg_left hC))

theorem screen_local_controls_of_chart_auxiliary_admissible
    (I : Set ℝ) (hI : IsOpen I) (γ : ℝ → Screen) (γn : ℕ → ℝ → Screen)
    (hγ : ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun u => γ u i j) I)
    (hγn : ∀ n (i j : Fin 2), ContDiffOn ℝ ∞ (fun u => γn n u i j) I)
    (r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hrc : ∀ a b, ContDiffOn ℝ 1 (fun x => metricComponents r x a b) (screenSlab I))
    (hrp : ∀ x ∈ screenSlab I, Matrix.PosDef (metricComponents r x))
    (μ : Measure CoordinateSpace)
    (hpos : ∀ V : Set CoordinateSpace, IsOpen V → V ⊆ screenSlab I → V.Nonempty → μ V ≠ 0)
    (hconv : ∀ L : Set CoordinateSpace, IsCompact L → L ⊆ screenSlab I →
      TendstoUniformlyOn (fun n => metricComponents (screenBilinear (γn n)))
        (metricComponents (screenBilinear γ)) atTop L)
    (hb : ∀ L : Set CoordinateSpace, IsCompact L → L ⊆ screenSlab I →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
        eLpNorm (fun x => norm3 (metricComponents r x)
          (auxiliaryPerturbationJet r (screenBilinear γ) (screenBilinear (γn n)) x))
          ∞ (μ.restrict L) ≤ ENNReal.ofReal D)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ I) :
    TendstoUniformlyOn γn γ atTop K ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n u, u ∈ K → ‖screenDerivative (γn n) u‖ ≤ C := by
  let U := screenSlab I
  let L := screenAxis '' K
  have hU : IsOpen U := screenSlab_isOpen hI
  have hL : IsCompact L := hK.image screenAxis_continuous
  have hLU : L ⊆ U := by
    rintro _ ⟨u, hu, rfl⟩
    change screenAxis u 0 ∈ I
    rw [screenAxis_zero]
    exact hKI hu
  obtain ⟨S, hS, hLS, hSU⟩ := exists_compact_between hL hU hLU
  obtain ⟨D, hD, hbS⟩ := hb S hS hSU
  have hc0 (a b : Index) : ContDiffOn ℝ 1
      (fun x => metricComponents (screenBilinear γ) x a b) U :=
    (screenBilinear_components_contDiffOn I γ hγ a b).of_le (by
      change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hc (n : ℕ) (a b : Index) : ContDiffOn ℝ 1
      (fun x => metricComponents (screenBilinear (γn n)) x a b) U :=
    (screenBilinear_components_contDiffOn I (γn n) (hγn n) a b).of_le (by
      change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨D₀, hD₀, hcov⟩ := exists_auxiliary_coordinate_bound_of_physical_LInfinity
    μ U L S hU hS hLS hSU hpos r (screenBilinear γ) (fun n => screenBilinear (γn n))
    hrc (fun x hx => hrp x (hSU hx)) hc0 hc hD hbS
  have hu := hconv L hL hLU
  obtain ⟨D₁, hD₁, hraw⟩ := exists_eventual_rawJet_bound_of_auxiliary_bound
    U L hU hLU hL r (screenBilinear γ) (fun n => screenBilinear (γn n)) hrc
    (fun x hx => nondegenerate_of_posDef_components r x (hrp x (hLU hx)))
    (fun x hx => symmetric_of_posDef_components r x (hrp x (hLU hx)))
    hD₀ (Eventually.of_forall hcov) hu
  constructor
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with n hn
    intro u hku
    have hd := hn (screenAxis u) (mem_image_of_mem screenAxis hku)
    rw [dist_comm, dist_eq_norm] at hd ⊢
    apply (screen_sub_norm_le (γn n u) (γ u)).trans_lt
    simpa only [screenBilinear_components, screenAxis_zero] using hd
  · obtain ⟨M, hM⟩ := hK.bddAbove_image
      (((screenDerivative_continuousOn I hI γ hγ).mono hKI).norm)
    let M₀ := max M 0
    have hM₀ : 0 ≤ M₀ := le_max_right _ _
    have hi : ∀ᶠ n in atTop, ∀ u ∈ K, ‖screenDerivative (γn n) u‖ ≤ D₁ + M₀ := by
      filter_upwards [hraw] with n hn
      intro u hku
      let x := screenAxis u
      have hxl : x ∈ L := mem_image_of_mem screenAxis hku
      let J := coordinateJet (fun y =>
        metricComponents (screenBilinear (γn n)) y - metricComponents (screenBilinear γ) y) x
      have hJ : ‖J‖ ≤ D₁ := hn x hxl
      have hdiff : ‖screenDerivative (γn n) u - screenDerivative γ u‖ ≤ D₁ := by
        apply (Matrix.norm_le_iff hD₁).2
        intro i j
        have he : J 0 (screenIndex i) (screenIndex j) =
            (screenDerivative (γn n) u - screenDerivative γ u) i j := by
          simpa only [J, x, screenAxis_zero, Matrix.sub_apply] using
            screenBilinear_rawJet_sub_screenEntry I hI (γn n) γ (hγn n) hγ x (hLU hxl) i j
        have hnorm := (norm_le_pi_norm (J 0 (screenIndex i)) (screenIndex j)).trans
          ((norm_le_pi_norm (J 0) (screenIndex i)).trans (norm_le_pi_norm J 0))
        change ‖(screenDerivative (γn n) u - screenDerivative γ u) i j‖ ≤ D₁
        rw [← he]
        exact hnorm.trans hJ
      calc
        ‖screenDerivative (γn n) u‖ =
            ‖(screenDerivative (γn n) u - screenDerivative γ u) + screenDerivative γ u‖ := by
              rw [sub_add_cancel]
        _ ≤ ‖screenDerivative (γn n) u - screenDerivative γ u‖ + ‖screenDerivative γ u‖ :=
          norm_add_le _ _
        _ ≤ D₁ + M₀ := add_le_add hdiff
          ((hM (mem_image_of_mem _ hku)).trans (le_max_left _ _))
    exact screenDerivative_bound_all hI hK hKI γn hγn (add_nonneg hD₁ hM₀) hi

end Burnett.RosenPlaneWave.AdmissibleLocal


noncomputable section

namespace Burnett.RosenPlaneWave.AdmissibleLocal

open Set Filter MeasureTheory Burnett.RicciSymbol
open Burnett.RosenPlaneWave
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.AuxiliaryConnection Burnett.Geometry.AuxiliaryPhysicalBound
open Burnett.Geometry.CovariantTensorNorm
open scoped Topology ContDiff ENNReal BigOperators Matrix.Norms.Elementwise

def screenLimitDensity (γ : ℝ → Screen) (x : CoordinateSpace) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt |Matrix.det (metricComponents (screenBilinear γ) x)|)

def screenLimitMeasure (γ : ℝ → Screen) : Measure CoordinateSpace :=
  volume.withDensity (screenLimitDensity γ)

theorem screenLimitDensity_eq (γ : ℝ → Screen) (x : CoordinateSpace) (hp : Matrix.PosDef (γ (x 0))) :
    screenLimitDensity γ x = ENNReal.ofReal (Real.sqrt (γ (x 0)).det) := by
  rw [screenLimitDensity, screenBilinear_components, screenMetric_volumeDensity _ hp.det_pos]

theorem screenLimitDensity_continuousOn (I : Set ℝ) (γ : ℝ → Screen)
    (hγ : ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun u => γ u i j) I) :
    ContinuousOn (screenLimitDensity γ) (screenSlab I) := by
  have hm : ContinuousOn (metricComponents (screenBilinear γ)) (screenSlab I) :=
    continuousOn_components_of_contDiffOn _ _
      (fun a b => (screenBilinear_components_contDiffOn I γ hγ a b).of_le (by
        change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top))
  have hd : ContinuousOn (fun x => Matrix.det (metricComponents (screenBilinear γ) x)) (screenSlab I) :=
    continuous_id.matrix_det.comp_continuousOn hm
  exact ENNReal.continuous_ofReal.comp_continuousOn hd.abs.sqrt

theorem screenLimitMeasure_open_pos (I : Set ℝ) (hI : IsOpen I) (γ : ℝ → Screen)
    (hγ : ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun u => γ u i j) I)
    (hγp : ∀ u ∈ I, Matrix.PosDef (γ u)) :
    ∀ V : Set CoordinateSpace, IsOpen V → V ⊆ screenSlab I → V.Nonempty →
      screenLimitMeasure γ V ≠ 0 := by
  classical
  let U := screenSlab I
  have hU : MeasurableSet U := (screenSlab_isOpen hI).measurableSet
  let w : CoordinateSpace → ℝ≥0∞ := U.piecewise (screenLimitDensity γ) (fun _ => 0)
  have hm : Measurable w :=
    (screenLimitDensity_continuousOn I γ hγ).measurable_piecewise continuous_const.continuousOn hU
  have hae : AEMeasurable (screenLimitDensity γ) (volume.restrict U) := by
    apply hm.aemeasurable.congr
    filter_upwards [ae_restrict_mem hU] with x hx
    exact Set.piecewise_eq_of_mem U _ _ hx
  have hp : ∀ x ∈ U, 0 < screenLimitDensity γ x := by
    intro x hx
    rw [screenLimitDensity_eq γ x (hγp (x 0) hx)]
    exact ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (hγp (x 0) hx).det_pos)
  intro V hV hVU hn
  exact (Burnett.Analysis.PositiveDensity.withDensity_open_pos_of_forall hU hae hp hV hn hVU).ne'

theorem screen_coordinate_uniform_of_physical_C0loc
    (I : Set ℝ) (γ : ℝ → Screen) (γn : ℕ → ℝ → Screen)
    (r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hrc : ∀ a b, ContDiffOn ℝ 1 (fun x => metricComponents r x a b) (screenSlab I))
    (hrp : ∀ x ∈ screenSlab I, Matrix.PosDef (metricComponents r x))
    (hconv : ∀ L : Set CoordinateSpace, IsCompact L → L ⊆ screenSlab I →
      TendstoUniformlyOn (fun n x => norm2 (metricComponents r x)
        (metricComponents (screenBilinear (γn n)) x - metricComponents (screenBilinear γ) x))
        (fun _ => 0) atTop L)
    (L : Set CoordinateSpace) (hL : IsCompact L) (hLI : L ⊆ screenSlab I) :
    TendstoUniformlyOn (fun n => metricComponents (screenBilinear (γn n)))
      (metricComponents (screenBilinear γ)) atTop L := by
  obtain ⟨C, hC, hcontrol⟩ := exists_uniform_norm2_control (metricComponents r) L hL
    (fun i => (hrc i i).continuousOn.mono hLI) (fun x hx => hrp x (hLI hx))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv L hL hLI) (ε / C) (div_pos hε hC)]
    with n hn
  intro x hx
  let T := metricComponents (screenBilinear (γn n)) x - metricComponents (screenBilinear γ) x
  have hnpos : 0 ≤ norm2 (metricComponents r x) T := Real.sqrt_nonneg _
  have hsmall : norm2 (metricComponents r x) T < ε / C := by
    simpa only [T, dist_zero_left, Real.norm_eq_abs,
      abs_of_nonneg hnpos] using hn x hx
  rw [dist_comm, dist_eq_norm]
  change ‖T‖ < ε
  exact (hcontrol x hx T).trans_lt ((mul_lt_mul_of_pos_left hsmall hC).trans_le
    (le_of_eq (by field_simp [hC.ne'])))

theorem screen_local_controls_of_physical_admissible
    (I : Set ℝ) (hI : IsOpen I) (γ : ℝ → Screen) (γn : ℕ → ℝ → Screen)
    (hγ : ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun u => γ u i j) I)
    (hγn : ∀ n (i j : Fin 2), ContDiffOn ℝ ∞ (fun u => γn n u i j) I)
    (hγp : ∀ u ∈ I, Matrix.PosDef (γ u))
    (r : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hrc : ∀ a b, ContDiffOn ℝ 1 (fun x => metricComponents r x a b) (screenSlab I))
    (hrp : ∀ x ∈ screenSlab I, Matrix.PosDef (metricComponents r x))
    (hconv : ∀ L : Set CoordinateSpace, IsCompact L → L ⊆ screenSlab I →
      TendstoUniformlyOn (fun n x => norm2 (metricComponents r x)
        (metricComponents (screenBilinear (γn n)) x - metricComponents (screenBilinear γ) x))
        (fun _ => 0) atTop L)
    (hb : ∀ L : Set CoordinateSpace, IsCompact L → L ⊆ screenSlab I →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
        eLpNorm (fun x => norm3 (metricComponents r x)
          (auxiliaryPerturbationJet r (screenBilinear γ) (screenBilinear (γn n)) x))
          ∞ ((screenLimitMeasure γ).restrict L) ≤ ENNReal.ofReal D)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ I) :
    TendstoUniformlyOn γn γ atTop K ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n u, u ∈ K → ‖screenDerivative (γn n) u‖ ≤ C :=
  screen_local_controls_of_chart_auxiliary_admissible I hI γ γn hγ hγn r hrc hrp
    (screenLimitMeasure γ) (screenLimitMeasure_open_pos I hI γ hγ hγp)
    (screen_coordinate_uniform_of_physical_C0loc I γ γn r hrc hrp hconv) hb K hK hKI

end Burnett.RosenPlaneWave.AdmissibleLocal
