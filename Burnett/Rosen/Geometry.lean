import Burnett.Counterexamples.Rosen.Kinetic
import Burnett.Geometry.BackgroundConnection
import Burnett.Geometry.CurvatureDifference
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# General Rosen plane waves

The full metric, computed connection and curvature, and canonical Hamiltonian.
-/

set_option autoImplicit false

noncomputable section

/-!
# The two-polarization Rosen metric in product coordinates

The screen is the full two-by-two block, including the mixed polarization.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenPlaneWave

open Matrix Set Filter Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField Burnett.Geometry.InversePerturbation
open scoped Matrix BigOperators Topology ContDiff

abbrev Screen := Matrix (Fin 2) (Fin 2) ℝ

def screenMetric (γ : Screen) : Tensor2 :=
  !![0, -1, 0, 0;
     -1, 0, 0, 0;
     0, 0, γ 0 0, γ 0 1;
     0, 0, γ 1 0, γ 1 1]

theorem screenMetric_inverse (γ : Screen) (hγ : IsUnit γ.det) :
    matrixInverse (screenMetric γ) = screenMetric γ⁻¹ := by
  have hscreen := Matrix.mul_nonsing_inv γ hγ
  have he (i j : Fin 2) : γ i 0 * γ⁻¹ 0 j + γ i 1 * γ⁻¹ 1 j = if i = j then 1 else 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] using
      congrArg (fun M : Screen => M i j) hscreen
  apply matrixInverse_eq_of_right_inverse
  funext i j
  fin_cases i <;> fin_cases j <;> simp [screenMetric, compose, identity, Fin.sum_univ_succ]
  all_goals first | simpa using he 0 0 | simpa using he 0 1 | simpa using he 1 0 | simpa using he 1 1

def screenJet (D : Screen) : FirstJet := fun d =>
  if d = 0 then !![0, 0, 0, 0;
                  0, 0, 0, 0;
                  0, 0, D 0 0, D 0 1;
                  0, 0, D 1 0, D 1 1]
  else 0

def optical (γInv D : Screen) : Screen := (γInv * D).map (fun z => z / 2)

/-- `D` is the first derivative of the screen and `L` is its mixed optical matrix. -/
def screenConnection (D L : Screen) : Connection :=
  ![0,
    !![0, 0, 0, 0;
       0, 0, 0, 0;
       0, 0, D 0 0 / 2, D 0 1 / 2;
       0, 0, D 1 0 / 2, D 1 1 / 2],
    !![0, 0, L 0 0, L 0 1;
       0, 0, 0, 0;
       L 0 0, 0, 0, 0;
       L 0 1, 0, 0, 0],
    !![0, 0, L 1 0, L 1 1;
       0, 0, 0, 0;
       L 1 0, 0, 0, 0;
       L 1 1, 0, 0, 0]]

theorem screenMetric_christoffel (γInv D : Screen) (hsym : D 1 0 = D 0 1) :
    christoffel (screenMetric γInv) (screenJet D) = screenConnection D (optical γInv D) := by
  funext a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [screenMetric, screenJet, screenConnection, optical, christoffel, koszul,
      Matrix.mul_apply, Fin.sum_univ_succ, hsym]
  all_goals ring

theorem screenConnection_ricci (D L D' L' : Screen) (b c : Index) :
    ricci (screenConnection D L) (fun d => if d = 0 then screenConnection D' L' else 0) b c =
      if b = 0 ∧ c = 0 then -(Matrix.trace L' + Matrix.trace (L * L)) else 0 := by
  fin_cases b <;> fin_cases c <;>
    simp [ricci, screenConnection, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- The bilinear metric in the fixed product coordinates, with an arbitrary screen. -/
def screenBilinear (γ : ℝ → Screen) (x : CoordinateSpace) :
    LinearMap.BilinForm ℝ CoordinateSpace :=
  Matrix.toBilin coordinateBasis (screenMetric (γ (x 0)))

theorem screenBilinear_components (γ : ℝ → Screen) :
    metricComponents (screenBilinear γ) = fun x => screenMetric (γ (x 0)) := by
  funext x
  calc
    metricComponents (screenBilinear γ) x =
      BilinForm.toMatrix coordinateBasis (screenBilinear γ x) := by
        ext a b
        simp only [metricComponents, Burnett.Geometry.FiberMetric.covariant, BilinForm.toMatrix_apply]
    _ = _ := BilinForm.toMatrix_toBilin coordinateBasis _

/-- The derivative of the full screen, taken for each coefficient in the fixed basis. -/
def screenDerivative (γ : ℝ → Screen) (u : ℝ) : Screen :=
  fun i j => deriv (fun t => γ t i j) u

def opticalMatrix (γ : ℝ → Screen) (u : ℝ) : Screen :=
  optical (γ u)⁻¹ (screenDerivative γ u)

private theorem fderiv_univariate_at_basis (f : ℝ → ℝ) (x : CoordinateSpace)
    (hf : DifferentiableAt ℝ f (x 0)) (d : Index) :
    fderiv ℝ (fun y : CoordinateSpace => f (y 0)) x (EuclideanSpace.single d 1) =
      if d = 0 then deriv f (x 0) else 0 := by
  let π : CoordinateSpace →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hd := hf.hasDerivAt.hasFDerivAt.comp x π.hasFDerivAt
  change fderiv ℝ (f ∘ π) x _ = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  change (EuclideanSpace.single d (1 : ℝ)) 0 * deriv f (x 0) = _
  by_cases h : d = 0
  · subst d
    simp [EuclideanSpace.single_apply]
  · simp [EuclideanSpace.single_apply, h, Ne.symm h]

theorem screenBilinear_coordinateJet (γ : ℝ → Screen) (x : CoordinateSpace)
    (hγ : ∀ i j, DifferentiableAt ℝ (fun u => γ u i j) (x 0)) :
    coordinateJet (metricComponents (screenBilinear γ)) x = screenJet (screenDerivative γ (x 0)) := by
  rw [screenBilinear_components]
  funext d a b
  have hderiv (i j : Fin 2) := fderiv_univariate_at_basis (fun u => γ u i j) x (hγ i j) d
  fin_cases a <;> fin_cases b <;>
    simp [coordinateJet, screenMetric, screenJet, screenDerivative, ite_apply, hderiv]

def opticalConnection (γ : ℝ → Screen) (x : CoordinateSpace) : Connection :=
  screenConnection (screenDerivative γ (x 0)) (opticalMatrix γ (x 0))

theorem screenBilinear_computedConnection (γ : ℝ → Screen) (x : CoordinateSpace)
    (hγ : ∀ i j, DifferentiableAt ℝ (fun u => γ u i j) (x 0))
    (hinv : IsUnit (γ (x 0)).det)
    (hsym : (fun u => γ u 1 0) =ᶠ[𝓝 (x 0)] (fun u => γ u 0 1)) :
    computedConnection (screenBilinear γ) x = opticalConnection γ x := by
  unfold computedConnection opticalConnection opticalMatrix
  rw [screenBilinear_coordinateJet γ x hγ, screenBilinear_components, screenMetric_inverse _ hinv]
  exact screenMetric_christoffel _ _ hsym.deriv_eq

private theorem differentiableAt_deriv_screen {f : ℝ → ℝ} {u : ℝ} (hf : ContDiffAt ℝ 2 f u) :
    DifferentiableAt ℝ (deriv f) u := by
  have hf' : ContDiffAt ℝ ((1 : WithTop ℕ∞) + 1) f u := by
    simpa only [show (1 : WithTop ℕ∞) + 1 = 2 by norm_num] using hf
  have h : ContDiffAt ℝ 1 (deriv f) u := by
    simpa only [deriv] using hf'.fderiv_right_succ.clm_apply
      (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℝ => (1 : ℝ)) u)
  exact h.differentiableAt_one

private theorem differentiableAt_screen_inverse (γ : ℝ → Screen) (u : ℝ)
    (hγ : ∀ i j, DifferentiableAt ℝ (fun t => γ t i j) u) (hinv : (γ u).det ≠ 0)
    (i j : Fin 2) : DifferentiableAt ℝ (fun t => (γ t)⁻¹ i j) u := by
  have hdet : DifferentiableAt ℝ (fun t => (γ t).det) u := by
    simp only [Matrix.det_fin_two]
    exact ((hγ 0 0).mul (hγ 1 1)).sub ((hγ 0 1).mul (hγ 1 0))
  have hinvdet : DifferentiableAt ℝ (fun t => (γ t).det⁻¹) u := hdet.inv hinv
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp
  · exact hinvdet.mul (hγ 1 1)
  · exact hinvdet.mul (hγ 0 1)
  · exact hinvdet.mul (hγ 1 0)
  · exact hinvdet.mul (hγ 0 0)

private theorem differentiableAt_opticalMatrix (γ : ℝ → Screen) (u : ℝ)
    (hγ : ∀ i j, ContDiffAt ℝ 2 (fun t => γ t i j) u) (hinv : (γ u).det ≠ 0)
    (i j : Fin 2) : DifferentiableAt ℝ (fun t => opticalMatrix γ t i j) u := by
  have hd (a b : Fin 2) := differentiableAt_deriv_screen (hγ a b)
  have hi := differentiableAt_screen_inverse γ u (fun a b => (hγ a b).differentiableAt (by norm_num)) hinv
  simp only [opticalMatrix, optical, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, screenDerivative]
  exact (((hi i 0).mul (hd 0 j)).add ((hi i 1).mul (hd 1 j))).div_const 2

set_option maxHeartbeats 650000 in
private theorem opticalConnection_coordinateJet (γ : ℝ → Screen) (x : CoordinateSpace)
    (hγ : ∀ i j, ContDiffAt ℝ 2 (fun t => γ t i j) (x 0)) (hinv : (γ (x 0)).det ≠ 0) :
    coordinateConnectionJet (opticalConnection γ) x = fun d => if d = 0 then
      screenConnection (screenDerivative (screenDerivative γ) (x 0))
        (screenDerivative (opticalMatrix γ) (x 0)) else 0 := by
  have hd (i j : Fin 2) : DifferentiableAt ℝ (fun u => screenDerivative γ u i j / 2) (x 0) :=
    (differentiableAt_deriv_screen (hγ i j)).div_const 2
  funext d a b c
  have hD (i j : Fin 2) := fderiv_univariate_at_basis
    (fun u => deriv (fun t => γ t i j) u / 2) x (hd i j) d
  have hL (i j : Fin 2) := fderiv_univariate_at_basis (fun t => opticalMatrix γ t i j) x
    (differentiableAt_opticalMatrix γ (x 0) hγ hinv i j) d
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [coordinateConnectionJet, opticalConnection, screenConnection, screenDerivative,
      ite_apply, hD, hL, deriv_div_const]

/-- The computed Ricci tensor of a Rosen metric with a general two-dimensional screen. -/
theorem screenBilinear_coordinateRicci (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ 2 (fun t => γ t i j) U)
    (hinv : ∀ u ∈ U, (γ u).det ≠ 0) (hsym : ∀ u ∈ U, Matrix.IsSymm (γ u))
    (x : CoordinateSpace) (hx : x 0 ∈ U) (b c : Index) :
    coordinateRicci (computedConnection (screenBilinear γ)) x b c =
      if b = 0 ∧ c = 0 then
        -(deriv (fun u => Matrix.trace (opticalMatrix γ u)) (x 0) +
          Matrix.trace (opticalMatrix γ (x 0) * opticalMatrix γ (x 0))) else 0 := by
  let π : CoordinateSpace →L[ℝ] ℝ := EuclideanSpace.proj 0
  let F := computedConnection (screenBilinear γ)
  let G := opticalConnection γ
  have atPoint (p : CoordinateSpace) (hp : p 0 ∈ U) (i j : Fin 2) := (hγ i j).contDiffAt (hU.mem_nhds hp)
  have heqPt (p : CoordinateSpace) (hp : p 0 ∈ U) : F p = G p := by
    apply screenBilinear_computedConnection γ p (fun i j => (atPoint p hp i j).differentiableAt (by norm_num))
      (isUnit_iff_ne_zero.mpr (hinv _ hp))
    filter_upwards [hU.mem_nhds hp] with u hu
    exact (hsym u hu).apply 0 1
  have heq : F =ᶠ[𝓝 x] G := by
    have hNear : ∀ᶠ p in 𝓝 x, p 0 ∈ U := π.continuous.continuousAt (hU.mem_nhds hx)
    filter_upwards [hNear] with p hp
    exact heqPt p hp
  have hjet : coordinateConnectionJet F x = coordinateConnectionJet G x := by
    funext d a i j
    have hcomp : (fun p => F p a i j) =ᶠ[𝓝 x] (fun p => G p a i j) :=
      heq.mono fun _ hp => congrFun (congrFun (congrFun hp a) i) j
    unfold coordinateConnectionJet
    rw [hcomp.fderiv_eq]
  have hLdiff := differentiableAt_opticalMatrix γ (x 0) (atPoint x hx) (hinv _ hx)
  have htrace : Matrix.trace (screenDerivative (opticalMatrix γ) (x 0)) =
      deriv (fun u => Matrix.trace (opticalMatrix γ u)) (x 0) := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, screenDerivative]
    exact (deriv_add (hLdiff 0 0) (hLdiff 1 1)).symm
  change coordinateRicci F x b c = _
  unfold coordinateRicci
  rw [heqPt x hx, hjet, opticalConnection_coordinateJet γ x (atPoint x hx) (hinv _ hx)]
  change ricci (screenConnection _ _) _ _ _ = _
  rw [screenConnection_ricci, htrace]

/-- Actual vacuum Ricci in the product chart gives the one-dimensional optical trace law. -/
theorem vacuum_trace_derivative_of_coordinateRicci (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ 2 (fun t => γ t i j) U)
    (hinv : ∀ u ∈ U, (γ u).det ≠ 0) (hsym : ∀ u ∈ U, Matrix.IsSymm (γ u))
    (hVac : ∀ x : CoordinateSpace, x 0 ∈ U →
      ∀ b c : Index, coordinateRicci (computedConnection (screenBilinear γ)) x b c = 0)
    (u : ℝ) (hu : u ∈ U) :
    -deriv (fun t => Matrix.trace (opticalMatrix γ t)) u =
      Matrix.trace (opticalMatrix γ u * opticalMatrix γ u) := by
  let x : CoordinateSpace := EuclideanSpace.single 0 u
  have hx : x 0 = u := by simp [x, EuclideanSpace.single_apply]
  have hxU : x 0 ∈ U := hx.symm ▸ hu
  have hv := hVac x hxU 0 0
  rw [screenBilinear_coordinateRicci γ U hU hγ hinv hsym x hxU, hx] at hv
  simp only [and_self, if_true] at hv
  linarith

end Burnett.RosenPlaneWave

namespace Burnett.RosenPlaneWave

open Matrix Set Filter
open scoped Matrix BigOperators Topology
open Burnett.RosenMultiscale.Transport

/-- The determinant includes one negative direction from the null block. -/
theorem screenMetric_det (γ : Screen) : Matrix.det (screenMetric γ) = -γ.det := by
  rw [Matrix.det_succ_row_zero]
  simp [screenMetric, Matrix.det_fin_three, Matrix.det_fin_two, Matrix.submatrix_apply, Fin.sum_univ_succ]
  have h : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  simp [h]
  ring

theorem screenMetric_volumeDensity (γ : Screen) (hγ : 0 < γ.det) :
    Real.sqrt |Matrix.det (screenMetric γ)| = Real.sqrt γ.det := by
  rw [screenMetric_det, abs_neg, abs_of_pos hγ]

/-- The metric field, in the ordinary product coordinate model of the Hamiltonian. -/
def screenField (γ : ℝ → Screen) (x : Coordinate) : Matrix (Fin 4) (Fin 4) ℝ :=
  screenMetric (γ (x 0))

theorem screenHamilton_du (γ : ℝ → Screen) (x : Coordinate) (hγ : IsUnit (γ (x 0)).det) :
    P (screenField γ) x du = 0 := by
  have hinv : inverseMetric (screenField γ x) = screenMetric (γ (x 0))⁻¹ := screenMetric_inverse _ hγ
  rw [P_du_entry, hinv]
  simp [screenMetric]

private theorem screenHamilton_eq (γ : ℝ → Screen) (x : Coordinate) (hγ : IsUnit (γ (x 0)).det)
    (ξ : Coordinate) :
    let A := (γ (x 0))⁻¹
    P (screenField γ) x ξ = -(ξ 0 * ξ 1) +
      (A 0 0 * (ξ 2)^2 + (A 0 1 + A 1 0) * (ξ 2 * ξ 3) + A 1 1 * (ξ 3)^2) / 2 := by
  have hinv : inverseMetric (screenField γ x) = screenMetric (γ (x 0))⁻¹ := screenMetric_inverse _ hγ
  simp [P, hinv, screenMetric, Fin.sum_univ_succ]
  ring

theorem screenHamilton_momentum_fderiv_du (γ : ℝ → Screen) (x : Coordinate)
    (hγ : IsUnit (γ (x 0)).det) :
    HasFDerivAt (P (screenField γ) x) (-(ContinuousLinearMap.proj 1 : Coordinate →L[ℝ] ℝ)) du := by
  let A : Screen := (γ (x 0))⁻¹
  have hc (i : Fin 4) : HasFDerivAt (fun ξ : Coordinate => ξ i)
      (ContinuousLinearMap.proj i : Coordinate →L[ℝ] ℝ) du :=
    (ContinuousLinearMap.proj i : Coordinate →L[ℝ] ℝ).hasFDerivAt
  have h01 : HasFDerivAt (fun ξ : Coordinate => ξ 0 * ξ 1)
      (ContinuousLinearMap.proj 1 : Coordinate →L[ℝ] ℝ) du := by
    simpa [du, coordinateBasis] using (hc 0).mul (hc 1)
  have h2 : HasFDerivAt (fun ξ : Coordinate => (ξ 2)^2) (0 : Coordinate →L[ℝ] ℝ) du := by
    simpa [du, coordinateBasis] using (hc 2).pow 2
  have h23 : HasFDerivAt (fun ξ : Coordinate => ξ 2 * ξ 3) (0 : Coordinate →L[ℝ] ℝ) du := by
    simpa [du, coordinateBasis] using (hc 2).mul (hc 3)
  have h3 : HasFDerivAt (fun ξ : Coordinate => (ξ 3)^2) (0 : Coordinate →L[ℝ] ℝ) du := by
    simpa [du, coordinateBasis] using (hc 3).pow 2
  have hs := ((h2.const_mul (A 0 0)).add (h23.const_mul (A 0 1 + A 1 0))).add (h3.const_mul (A 1 1))
  have h := h01.neg.add (hs.const_mul ((2 : ℝ)⁻¹))
  rw [show P (screenField γ) x = (fun ξ : Coordinate => -(ξ 0 * ξ 1) +
      (A 0 0 * (ξ 2)^2 + (A 0 1 + A 1 0) * (ξ 2 * ξ 3) + A 1 1 * (ξ 3)^2) / 2) from
    funext (screenHamilton_eq γ x hγ)]
  simpa only [Pi.add_def, Pi.neg_apply, smul_zero, add_zero, div_eq_mul_inv, mul_comm] using h

theorem screenHamilton_basePartial_du (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ u ∈ U, IsUnit (γ u).det) (x : Coordinate) (hx : x 0 ∈ U) (i : Fin 4) :
    basePartial i (P (screenField γ)) x du = 0 := by
  have hnear : ∀ᶠ y : Coordinate in 𝓝 x, y 0 ∈ U :=
    ((continuous_apply 0 : Continuous (fun y : Coordinate => y 0)).continuousAt) (hU.mem_nhds hx)
  have heq : (fun y => P (screenField γ) y du) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
    hnear.mono fun y hy => screenHamilton_du γ y (hγ _ hy)
  unfold basePartial
  rw [heq.fderiv_eq]
  simp

theorem screenHamilton_momentumPartial_du (γ : ℝ → Screen) (x : Coordinate)
    (hγ : IsUnit (γ (x 0)).det) (i : Fin 4) :
    momentumPartial i (P (screenField γ)) x du = if i = 1 then -1 else 0 := by
  unfold momentumPartial
  rw [(screenHamilton_momentum_fderiv_du γ x hγ).fderiv]
  fin_cases i <;> simp [coordinateBasis]

/-- At the null graph, the Hamilton vector field is horizontal and equals `-∂v`. -/
theorem screenHamilton_canonical_du (γ : ℝ → Screen) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ u ∈ U, IsUnit (γ u).det) (a : Coordinate → Coordinate → ℝ)
    (x : Coordinate) (hx : x 0 ∈ U) :
    canonicalHamilton (screenField γ) a x du = -basePartial 1 a x du := by
  unfold canonicalHamilton
  simp_rw [screenHamilton_momentumPartial_du γ x (hγ _ hx), screenHamilton_basePartial_du γ U hU hγ x hx]
  simp

end Burnett.RosenPlaneWave
