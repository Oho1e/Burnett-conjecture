import Burnett.Rosen.Geometry
import Burnett.Rosen.Screen

/-!
# General Rosen plane waves

The nondegenerate Lorentz metric and its smooth timelike direction.
-/

set_option autoImplicit false

noncomputable section

noncomputable section

namespace Burnett.RosenPlaneWave

open Matrix Set
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.RosenMultiscale
open Burnett.RosenScreen
open scoped Matrix BigOperators ContDiff Topology

theorem screenInverseSqrt_congr_identity (γ : Screen) (hγ : γ.PosDef) :
    (screenInverseSqrt γ).transpose * γ * screenInverseSqrt γ = 1 := by
  let R := screenInverseSqrt γ
  have hRR : R * R = γ⁻¹ := screenInverseSqrt_mul_self γ hγ
  have hsym : R.transpose = R := (screenInverseSqrt_isSymm γ hγ).eq
  have hγR : γ * R * R = 1 := by
    rw [mul_assoc, hRR, Matrix.mul_nonsing_inv γ (isUnit_iff_ne_zero.mpr hγ.det_pos.ne')]
  have hAR : γ * R = R⁻¹ := (Matrix.inv_eq_left_inv hγR).symm
  change R.transpose * γ * R = 1
  rw [hsym, mul_assoc, hAR, Matrix.mul_nonsing_inv R
    (isUnit_iff_ne_zero.mpr (screenInverseSqrt_posDef γ hγ).det_pos.ne')]

def screenLorentzFrame (γ : Screen) : Matrix Index Index ℝ :=
  let R := screenInverseSqrt γ
  let k := (Real.sqrt 2)⁻¹
  !![k, k, 0, 0;
     k, -k, 0, 0;
     0, 0, R 0 0, R 0 1;
     0, 0, R 1 0, R 1 1]

theorem screenLorentzFrame_congr (γ : Screen) (hγ : γ.PosDef) :
    let G : Matrix Index Index ℝ := screenMetric γ
    (screenLorentzFrame γ).transpose * G * screenLorentzFrame γ =
      rosenStandardLorentz := by
  dsimp only
  let R := screenInverseSqrt γ
  have hR (i j : Fin 2) : (R.transpose * γ * R) i j = if i = j then 1 else 0 := by
    change ((screenInverseSqrt γ).transpose * γ * screenInverseSqrt γ) i j = _
    rw [screenInverseSqrt_congr_identity γ hγ, Matrix.one_apply]
  have hk : ((Real.sqrt 2)⁻¹)^2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [screenLorentzFrame, screenMetric, rosenStandardLorentz, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.transpose_apply]
  all_goals
    first
    | nlinarith only [hk]
    | simpa [R, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply] using hR 0 0
    | simpa [R, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply] using hR 0 1
    | simpa [R, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply] using hR 1 0
    | simpa [R, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply] using hR 1 1

theorem screenBilinear_lorentz_frame (γ : ℝ → Screen) (x : CoordinateSpace)
    (hγ : (γ (x 0)).PosDef) :
    let G : Matrix Index Index ℝ := metricComponents (screenBilinear γ) x
    ∃ E : Matrix Index Index ℝ, E.det ≠ 0 ∧
      E.transpose * G * E = rosenStandardLorentz := by
  dsimp only
  let E := screenLorentzFrame (γ (x 0))
  let G : Matrix Index Index ℝ := screenMetric (γ (x 0))
  have hE : E.transpose * G * E = rosenStandardLorentz := screenLorentzFrame_congr _ hγ
  refine ⟨E, determinant_ne_zero_of_rosenLorentz_congr _ _ hE, ?_⟩
  rw [screenBilinear_components]
  exact hE

theorem screenMetric_isSymm (γ : Screen) (hγ : γ.IsSymm) :
    Matrix.IsSymm (screenMetric γ) := by
  change Matrix.transpose (screenMetric γ) = screenMetric γ
  have h01 : γ 1 0 = γ 0 1 := hγ.apply 0 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [screenMetric, Matrix.transpose_apply, h01]

theorem screenBilinear_isSymm (γ : ℝ → Screen) (x : CoordinateSpace)
    (hγ : (γ (x 0)).PosDef) : (screenBilinear γ x).IsSymm := by
  have hS : (γ (x 0)).IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hγ.1
  apply (LinearMap.BilinForm.isSymm_iff_basis coordinateBasis).mpr
  intro i j
  have hcomp (a b : Index) :
      screenBilinear γ x (coordinateBasis a) (coordinateBasis b) = screenMetric (γ (x 0)) a b := by
    change metricComponents (screenBilinear γ) x a b = _
    rw [screenBilinear_components]
  rw [hcomp, hcomp]
  exact (screenMetric_isSymm _ hS).apply j i

theorem screenBilinear_nondegenerate (γ : ℝ → Screen) (x : CoordinateSpace)
    (hγ : (γ (x 0)).PosDef) : (screenBilinear γ x).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero (screenBilinear γ x) coordinateBasis
  rw [screenBilinear, BilinForm.toMatrix_toBilin, screenMetric_det]
  exact neg_ne_zero.mpr hγ.det_pos.ne'

theorem screenField_eq_metricComponents (γ : ℝ → Screen) (p : Transport.Coordinate) :
    screenField γ p = metricComponents (screenBilinear γ) (WithLp.toLp 2 p) := by
  rw [screenBilinear_components]
  rfl

theorem screenBilinear_smooth_components (U : Set ℝ) (γ : ℝ → Screen)
    (hs : ∀ i j, ContDiffOn ℝ ∞ (fun u => γ u i j) U) (i j : Index) :
    ContDiffOn ℝ ∞ (fun x : CoordinateSpace => metricComponents (screenBilinear γ) x i j)
      {x | x 0 ∈ U} := by
  let π : CoordinateSpace →L[ℝ] ℝ := EuclideanSpace.proj 0
  have h (a b : Fin 2) : ContDiffOn ℝ ∞
      (fun x : CoordinateSpace => γ (x 0) a b) {x | x 0 ∈ U} :=
    (hs a b).comp π.contDiff.contDiffOn (fun _ hx => hx)
  rw [screenBilinear_components]
  fin_cases i <;> fin_cases j <;> simp [screenMetric]
  all_goals first | exact contDiffOn_const | apply h

def screenTimeDirection : CoordinateSpace :=
  EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1

theorem screenTimeDirection_coord (i : Index) :
    screenTimeDirection i = originalRosenTimeDirection i := by
  fin_cases i <;> simp [screenTimeDirection, originalRosenTimeDirection, PiLp.add_apply]

theorem screenBilinear_timeDirection_square (γ : ℝ → Screen) (x : CoordinateSpace) :
    screenBilinear γ x screenTimeDirection screenTimeDirection = -2 := by
  rw [screenBilinear, Matrix.toBilin_apply]
  have h (i : Index) : coordinateBasis.repr screenTimeDirection i = originalRosenTimeDirection i :=
    screenTimeDirection_coord i
  norm_num [h, originalRosenTimeDirection, screenMetric, Fin.sum_univ_succ]

theorem screenTimeDirection_ne_zero : screenTimeDirection ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : CoordinateSpace => v 0) h
  simp [screenTimeDirection, PiLp.add_apply] at h0

theorem screenBilinear_has_smooth_timelike_direction (γ : ℝ → Screen) :
    ∃ T : CoordinateSpace → CoordinateSpace, ContDiff ℝ ∞ T ∧
      ∀ x, T x ≠ 0 ∧ screenBilinear γ x (T x) (T x) = -2 :=
  ⟨fun _ => screenTimeDirection, contDiff_const,
    fun x => ⟨screenTimeDirection_ne_zero, screenBilinear_timeDirection_square γ x⟩⟩


theorem screenBilinear_lorentz_on (U : Set ℝ) (γ : ℝ → Screen)
    (hs : ∀ i j, ContDiffOn ℝ ∞ (fun u => γ u i j) U)
    (hp : ∀ u ∈ U, (γ u).PosDef) :
    (∀ i j, ContDiffOn ℝ ∞ (fun x : CoordinateSpace =>
      metricComponents (screenBilinear γ) x i j) {x | x 0 ∈ U}) ∧
    (∀ x : CoordinateSpace, x 0 ∈ U →
      (screenBilinear γ x).IsSymm ∧ (screenBilinear γ x).Nondegenerate ∧
      (let G : Matrix Index Index ℝ := metricComponents (screenBilinear γ) x
       ∃ E : Matrix Index Index ℝ, E.det ≠ 0 ∧ E.transpose * G * E = rosenStandardLorentz)) ∧
    ∃ T : CoordinateSpace → CoordinateSpace, ContDiff ℝ ∞ T ∧
      ∀ x, T x ≠ 0 ∧ screenBilinear γ x (T x) (T x) = -2 := by
  refine ⟨screenBilinear_smooth_components U γ hs, ?_, screenBilinear_has_smooth_timelike_direction γ⟩
  intro x hx
  have h := hp (x 0) hx
  exact ⟨screenBilinear_isSymm γ x h, screenBilinear_nondegenerate γ x h, screenBilinear_lorentz_frame γ x h⟩

end Burnett.RosenPlaneWave
