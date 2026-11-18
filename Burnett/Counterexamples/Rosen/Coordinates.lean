import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Rosen multiscale example

The original and pulled metric, its signature and the coordinate change.
-/

set_option autoImplicit false

noncomputable section

set_option autoImplicit false

noncomputable section

namespace Burnett.RosenMultiscale

open Matrix Filter Set
open scoped BigOperators Topology

abbrev CoordinateMetric := Matrix (Fin 4) (Fin 4) ℝ

def pulledMetricAt (b d v s t : ℝ) : CoordinateMetric :=
  !![-2 * d * v, -b, 0, 0;
     -b,          0, 0, 0;
     0,           0, s, 0;
     0,           0, 0, t]

def inversePulledMetricAt (b d v s t : ℝ) : CoordinateMetric :=
  !![0,    -b⁻¹,          0,   0;
     -b⁻¹, 2 * d * v / b^2, 0,   0;
     0,    0,            s⁻¹, 0;
     0,    0,            0,   t⁻¹]

theorem pulledMetricAt_det (b d v s t : ℝ) :
    (pulledMetricAt b d v s t).det = -(b^2 * s * t) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.sum_univ_succ, pulledMetricAt, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove, Fin.succ, Fin.castSucc]
  ring

theorem pulledMetricAt_inv (b d v s t : ℝ) (hb : b ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) :
    (pulledMetricAt b d v s t)⁻¹ = inversePulledMetricAt b d v s t := by
  let A := pulledMetricAt b d v s t
  let N := inversePulledMetricAt b d v s t
  have hn : A * N = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [A, N, pulledMetricAt, inversePulledMetricAt, Matrix.mul_apply, Fin.sum_univ_succ,
        hb, hs, ht]
    field_simp [hb]
    ring
  have hdet : A.det ≠ 0 := by
    change (pulledMetricAt b d v s t).det ≠ 0
    rw [pulledMetricAt_det]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hb) hs) ht)
  have hleft := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet)
  exact calc
    A⁻¹ = A⁻¹ * (A * N) := by rw [hn, mul_one]
    _ = N := by rw [← mul_assoc, hleft, one_mul]

def screenX (b ψ : ℝ) : ℝ := b^2 * Real.exp (2 * ψ)

def screenZ (b ψ : ℝ) : ℝ := b^2 * Real.exp (-2 * ψ)

theorem screen_product (b ψ : ℝ) : screenX b ψ * screenZ b ψ = b^4 := by
  calc
    screenX b ψ * screenZ b ψ = b^4 * (Real.exp (2 * ψ) * Real.exp (-2 * ψ)) := by
      simp only [screenX, screenZ]
      ring
    _ = b^4 := by rw [← Real.exp_add]; simp

theorem pulledRosen_volume (b d v ψ : ℝ) (hb : 0 < b) :
    Real.sqrt |(pulledMetricAt b d v (screenX b ψ) (screenZ b ψ)).det| = b^3 := by
  rw [pulledMetricAt_det, abs_neg, mul_assoc, screen_product]
  have hpow : b^2 * b^4 = (b^3)^2 := by ring
  rw [hpow, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos (pow_pos hb 3)]

def pulledRosenField (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ) : CoordinateMetric :=
  let u := point 0
  pulledMetricAt (B u) (deriv B u) (point 1) (screenX (B u) (ψ u)) (screenZ (B u) (ψ u))

def densitizedInverse (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ) : CoordinateMetric :=
  let G := pulledRosenField B ψ point
  Real.sqrt |G.det| • G⁻¹

-- Differentiate the actual densitized inverse in each coordinate direction.
def contractedSource (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∑ j, deriv (fun t => densitizedInverse B ψ (Function.update point j t) i j) (point j)

def explicitFlux (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ) : CoordinateMetric :=
  let u := point 0
  let b := B u
  !![0,    -(b^2),                     0,                    0;
     -(b^2), 2 * b * deriv B u * point 1, 0,                0;
     0,       0,                        b^3 / screenX b (ψ u), 0;
     0,       0,                        0,                    b^3 / screenZ b (ψ u)]

theorem densitizedInverse_eq_explicitFlux (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ)
    (h : 0 < B (point 0)) : densitizedInverse B ψ point = explicitFlux B ψ point := by
  have hx : screenX (B (point 0)) (ψ (point 0)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ h.ne') (Real.exp_pos _).ne'
  have hz : screenZ (B (point 0)) (ψ (point 0)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ h.ne') (Real.exp_pos _).ne'
  simp only [densitizedInverse, pulledRosenField]
  rw [pulledRosen_volume _ _ _ _ h, pulledMetricAt_inv _ _ _ _ _ h.ne' hx hz]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [inversePulledMetricAt, explicitFlux, Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv]
  all_goals field_simp [h.ne']

theorem deriv_densitizedInverse_update (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ)
    (hB : ContinuousAt B (point 0)) (h : 0 < B (point 0)) (i j : Fin 4) :
    deriv (fun t => densitizedInverse B ψ (Function.update point j t) i j) (point j) =
      deriv (fun t => explicitFlux B ψ (Function.update point j t) i j) (point j) := by
  apply Filter.EventuallyEq.deriv_eq
  by_cases hj : j = 0
  · subst j
    have hN : ∀ᶠ t in 𝓝 (point 0), 0 < B t := hB (Ioi_mem_nhds h)
    filter_upwards [hN] with t ht
    rw [densitizedInverse_eq_explicitFlux B ψ _ (by simpa using ht)]
  · filter_upwards with t
    rw [densitizedInverse_eq_explicitFlux B ψ _ (by simpa [Function.update_of_ne (Ne.symm hj)] using h)]

theorem pulledRosen_contractedSource_zero (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ)
    (hBd : DifferentiableAt ℝ B (point 0)) (h : 0 < B (point 0)) (i : Fin 4) :
    contractedSource B ψ point i = 0 := by
  simp_rw [contractedSource, deriv_densitizedInverse_update B ψ point hBd.continuousAt h]
  have hU : deriv (fun t => -(B t)^2) (point 0) = -(2 * B (point 0) * deriv B (point 0)) := by
    have d := (hBd.hasDerivAt.pow 2).neg.deriv
    convert d using 1
    ring
  have hV : deriv (fun t => 2 * B (point 0) * deriv B (point 0) * t) (point 1) =
      2 * B (point 0) * deriv B (point 0) := by
    simpa using ((hasDerivAt_id (point 1)).const_mul (2 * B (point 0) * deriv B (point 0))).deriv
  fin_cases i <;> simp [explicitFlux, Fin.sum_univ_succ, Function.update_of_ne, hU, hV]

def rosenCoordinates (B : ℝ → ℝ) (point : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![point 0, B (point 0) * point 1, point 2, point 3]

def coordinateJacobian (F : (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (point : Fin 4 → ℝ) : CoordinateMetric := fun i j =>
  deriv (fun t => F (Function.update point j t) i) (point j)

def originalRosenField (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ) : CoordinateMetric :=
  !![0, -1, 0, 0;
     -1, 0, 0, 0;
     0, 0, screenX (B (point 0)) (ψ (point 0)), 0;
     0, 0, 0, screenZ (B (point 0)) (ψ (point 0))]

theorem rosenCoordinates_jacobian (B : ℝ → ℝ) (point : Fin 4 → ℝ)
    (hB : DifferentiableAt ℝ B (point 0)) :
    coordinateJacobian (rosenCoordinates B) point =
      !![1,                          0,           0, 0;
         deriv B (point 0) * point 1, B (point 0), 0, 0;
         0,                          0,           1, 0;
         0,                          0,           0, 1] := by
  have hu := (hB.hasDerivAt.mul_const (point 1)).deriv
  have hv : deriv (fun t => B (point 0) * t) (point 1) = B (point 0) := by
    simpa using ((hasDerivAt_id (point 1)).const_mul (B (point 0))).deriv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateJacobian, rosenCoordinates, Function.update_of_ne, hu, hv]

theorem pulledRosenField_eq_jacobian_pullback (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ)
    (hB : DifferentiableAt ℝ B (point 0)) :
    let A := coordinateJacobian (rosenCoordinates B) point
    A.transpose * originalRosenField B ψ (rosenCoordinates B point) * A =
      pulledRosenField B ψ point := by
  dsimp only
  rw [rosenCoordinates_jacobian B point hB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, originalRosenField,
      rosenCoordinates, pulledRosenField, pulledMetricAt]
  ring

theorem rosen_coordinate_pullback_source_zero (B ψ : ℝ → ℝ) (point : Fin 4 → ℝ)
    (hB : DifferentiableAt ℝ B (point 0)) (hpos : 0 < B (point 0)) :
    (let A := coordinateJacobian (rosenCoordinates B) point
     A.transpose * originalRosenField B ψ (rosenCoordinates B point) * A =
        pulledRosenField B ψ point) ∧ ∀ i, contractedSource B ψ point i = 0 :=
  ⟨pulledRosenField_eq_jacobian_pullback B ψ point hB,
    pulledRosen_contractedSource_zero B ψ point hB hpos⟩

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Set
open scoped ContDiff

def inverseRosenCoordinates (B : ℝ → ℝ) (point : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![point 0, point 1 / B (point 0), point 2, point 3]

theorem rosenCoordinates_inverses_on_slab (B : ℝ → ℝ) (U : Set ℝ)
    (hb : ∀ u ∈ U, B u ≠ 0) :
    let slab : Set (Fin 4 → ℝ) := {point | point 0 ∈ U}
    MapsTo (rosenCoordinates B) slab slab ∧ MapsTo (inverseRosenCoordinates B) slab slab ∧
    InvOn (inverseRosenCoordinates B) (rosenCoordinates B) slab slab := by
  let slab : Set (Fin 4 → ℝ) := {point | point 0 ∈ U}
  have hd : MapsTo (rosenCoordinates B) slab slab := fun _ hx => hx
  have hi : MapsTo (inverseRosenCoordinates B) slab slab := fun _ hx => hx
  refine ⟨hd, hi, ⟨?_, ?_⟩⟩
  · intro point hp
    have hB := hb (point 0) hp
    ext i
    fin_cases i <;> simp [rosenCoordinates, inverseRosenCoordinates, hB]
  · intro point hp
    have hB := hb (point 0) hp
    ext i
    fin_cases i <;> simp [rosenCoordinates, inverseRosenCoordinates]
    rw [mul_comm, div_mul_cancel₀ _ hB]

theorem rosenCoordinates_smooth_on_slab (B : ℝ → ℝ) (U : Set ℝ)
    (hB : ContDiffOn ℝ ∞ B U) (hb : ∀ u ∈ U, B u ≠ 0) :
    let slab : Set (Fin 4 → ℝ) := {point | point 0 ∈ U}
    ContDiffOn ℝ ∞ (rosenCoordinates B) slab ∧ ContDiffOn ℝ ∞ (inverseRosenCoordinates B) slab := by
  let slab : Set (Fin 4 → ℝ) := {point | point 0 ∈ U}
  have hp (i : Fin 4) : ContDiffOn ℝ ∞ (fun point : Fin 4 → ℝ => point i) slab :=
    (contDiff_apply ℝ ℝ i).contDiffOn
  have hBS : ContDiffOn ℝ ∞ (fun point : Fin 4 → ℝ => B (point 0)) slab :=
    hB.comp (hp 0) (fun _ h => h)
  have hMul := hBS.mul (hp 1)
  have hDiv := (hp 1).div hBS (fun point hx => hb (point 0) hx)
  constructor
  · apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact hp 0
    · exact hMul
    · exact hp 2
    · exact hp 3
  · apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact hp 0
    · exact hDiv
    · exact hp 2
    · exact hp 3

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Matrix

def rosenStandardLorentz : CoordinateMetric :=
  Matrix.diagonal ![(-1 : ℝ), 1, 1, 1]

def rosenScreenOrthonormalFrame (s t : ℝ) : CoordinateMetric :=
  let k := (Real.sqrt 2)⁻¹
  !![k, k, 0, 0;
     k, -k, 0, 0;
     0, 0, (Real.sqrt s)⁻¹, 0;
     0, 0, 0, (Real.sqrt t)⁻¹]

theorem rosenStandardLorentz_det : rosenStandardLorentz.det = -1 := by
  simp [rosenStandardLorentz, Matrix.det_diagonal, Fin.prod_univ_succ]

theorem rosenScreenOrthonormalFrame_congr (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    let E := rosenScreenOrthonormalFrame s t
    E.transpose * pulledMetricAt 1 0 0 s t * E = rosenStandardLorentz := by
  have hk : ((Real.sqrt 2)⁻¹)^2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hks : (Real.sqrt s)⁻¹ * (s * (Real.sqrt s)⁻¹) = 1 := by
    calc
      _ = s * ((Real.sqrt s)⁻¹)^2 := by ring
      _ = 1 := by rw [inv_pow, Real.sq_sqrt hs.le, mul_inv_cancel₀ hs.ne']
  have hkt : (Real.sqrt t)⁻¹ * (t * (Real.sqrt t)⁻¹) = 1 := by
    calc
      _ = t * ((Real.sqrt t)⁻¹)^2 := by ring
      _ = 1 := by rw [inv_pow, Real.sq_sqrt ht.le, mul_inv_cancel₀ ht.ne']
  dsimp only
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rosenScreenOrthonormalFrame, pulledMetricAt, rosenStandardLorentz, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.transpose_apply]
  all_goals nlinarith only [hk, hks, hkt]

theorem determinant_ne_zero_of_rosenLorentz_congr (E g : CoordinateMetric)
    (h : E.transpose * g * E = rosenStandardLorentz) : E.det ≠ 0 := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, rosenStandardLorentz_det] at hd
  intro hzero
  simp [hzero] at hd

theorem originalRosenField_lorentz (B ψ : ℝ → ℝ) (p : Fin 4 → ℝ) (hb : B (p 0) ≠ 0) :
    ∃ E : CoordinateMetric, E.det ≠ 0 ∧
      E.transpose * originalRosenField B ψ p * E = rosenStandardLorentz := by
  let s := screenX (B (p 0)) (ψ (p 0))
  let t := screenZ (B (p 0)) (ψ (p 0))
  have hs : 0 < s := mul_pos (sq_pos_of_ne_zero hb) (Real.exp_pos _)
  have ht : 0 < t := mul_pos (sq_pos_of_ne_zero hb) (Real.exp_pos _)
  have hm : originalRosenField B ψ p = pulledMetricAt 1 0 0 s t := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [originalRosenField, pulledMetricAt, s, t]
  have h := rosenScreenOrthonormalFrame_congr s t hs ht
  change (rosenScreenOrthonormalFrame s t).transpose * pulledMetricAt 1 0 0 s t *
    rosenScreenOrthonormalFrame s t = rosenStandardLorentz at h
  rw [← hm] at h
  exact ⟨_, determinant_ne_zero_of_rosenLorentz_congr _ _ h, h⟩

theorem rosenCoordinates_jacobian_det (B : ℝ → ℝ) (p : Fin 4 → ℝ) (hB : DifferentiableAt ℝ B (p 0)) :
    (coordinateJacobian (rosenCoordinates B) p).det = B (p 0) := by
  rw [rosenCoordinates_jacobian B p hB, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, Fin.succ, Fin.castSucc]

theorem pulledRosenField_lorentz (B ψ : ℝ → ℝ) (p : Fin 4 → ℝ)
    (hB : DifferentiableAt ℝ B (p 0)) (hb : B (p 0) ≠ 0) :
    ∃ E : CoordinateMetric, E.det ≠ 0 ∧
      E.transpose * pulledRosenField B ψ p * E = rosenStandardLorentz := by
  let J := coordinateJacobian (rosenCoordinates B) p
  let q := rosenCoordinates B p
  let g := originalRosenField B ψ q
  obtain ⟨E, _, hE⟩ := originalRosenField_lorentz B ψ q hb
  have hg : J.transpose * g * J = pulledRosenField B ψ p :=
    pulledRosenField_eq_jacobian_pullback B ψ p hB
  have hJ : IsUnit J.det := by
    apply isUnit_iff_ne_zero.mpr
    unfold J
    rwa [rosenCoordinates_jacobian_det B p hB]
  have hJinv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ
  let L := J⁻¹ * E
  have hlim : J * L = E := by rw [show L = J⁻¹ * E from rfl, ← Matrix.mul_assoc, hJinv, one_mul]
  have htransport (A C G : CoordinateMetric) :
      C.transpose * (A.transpose * G * A) * C = (A * C).transpose * G * (A * C) := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hL : L.transpose * pulledRosenField B ψ p * L = rosenStandardLorentz := by
    rw [← hg]
    calc
      L.transpose * (J.transpose * g * J) * L = (J * L).transpose * g * (J * L) := htransport J L g
      _ = _ := by rw [hlim, hE]
  exact ⟨L, determinant_ne_zero_of_rosenLorentz_congr _ _ hL, hL⟩

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Matrix Set
open scoped ContDiff BigOperators

def originalRosenTimeDirection : Fin 4 → ℝ := ![1, 1, 0, 0]

def pulledRosenTimeDirection (B : ℝ → ℝ) (p : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![1, (1 - deriv B (p 0) * p 1) / B (p 0), 0, 0]

theorem originalRosenTimeDirection_norm (B ψ : ℝ → ℝ) (p : Fin 4 → ℝ) :
    dotProduct originalRosenTimeDirection ((originalRosenField B ψ p).mulVec originalRosenTimeDirection) = -2 := by
  norm_num [originalRosenTimeDirection, originalRosenField, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem pulledRosenTimeDirection_norm (B ψ : ℝ → ℝ) (p : Fin 4 → ℝ) (hb : B (p 0) ≠ 0) :
    dotProduct (pulledRosenTimeDirection B p) ((pulledRosenField B ψ p).mulVec (pulledRosenTimeDirection B p)) = -2 := by
  simp [pulledRosenTimeDirection, pulledRosenField, pulledMetricAt, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  field_simp [hb]
  ring

theorem pulledRosenTimeDirection_smooth (B : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hb : ∀ u ∈ U, B u ≠ 0) :
    ContDiffOn ℝ ∞ (pulledRosenTimeDirection B) {p | p 0 ∈ U} := by
  let slab : Set (Fin 4 → ℝ) := {p | p 0 ∈ U}
  have hp (i : Fin 4) : ContDiffOn ℝ ∞ (fun p : Fin 4 → ℝ => p i) slab :=
    (contDiff_apply ℝ ℝ i).contDiffOn
  have hBs : ContDiffOn ℝ ∞ (fun p : Fin 4 → ℝ => B (p 0)) slab := hB.comp (hp 0) (fun _ h => h)
  have hBd : ContDiffOn ℝ ∞ (deriv B) U := hB.deriv_of_isOpen hU (by simp)
  have hBds : ContDiffOn ℝ ∞ (fun p : Fin 4 → ℝ => deriv B (p 0)) slab := hBd.comp (hp 0) (fun _ h => h)
  have hV : ContDiffOn ℝ ∞ (fun p : Fin 4 → ℝ => 1 - deriv B (p 0) * p 1) slab :=
    contDiffOn_const.sub (hBds.mul (hp 1))
  have hquot := hV.div hBs (fun p hx => hb (p 0) hx)
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_const
  · exact hquot
  · exact contDiffOn_const
  · exact contDiffOn_const

theorem rosenMetricFields_smooth (B ψ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hψ : ContDiffOn ℝ ∞ ψ U) :
    let slab : Set (Fin 4 → ℝ) := {p | p 0 ∈ U}
    (∀ i j, ContDiffOn ℝ ∞ (fun p => originalRosenField B ψ p i j) slab) ∧
    ∀ i j, ContDiffOn ℝ ∞ (fun p => pulledRosenField B ψ p i j) slab := by
  let slab : Set (Fin 4 → ℝ) := {p | p 0 ∈ U}
  have hp (i : Fin 4) : ContDiffOn ℝ ∞ (fun p : Fin 4 → ℝ => p i) slab :=
    (contDiff_apply ℝ ℝ i).contDiffOn
  have hBs : ContDiffOn ℝ ∞ (fun p : Fin 4 → ℝ => B (p 0)) slab := hB.comp (hp 0) (fun _ h => h)
  have hs : ContDiffOn ℝ ∞ (fun p : Fin 4 → ℝ => ψ (p 0)) slab := hψ.comp (hp 0) (fun _ h => h)
  have hBd : ContDiffOn ℝ ∞ (deriv B) U := hB.deriv_of_isOpen hU (by simp)
  have hBds : ContDiffOn ℝ ∞ (fun p : Fin 4 → ℝ => deriv B (p 0)) slab := hBd.comp (hp 0) (fun _ h => h)
  have hxx : ContDiffOn ℝ ∞ (fun p : Fin 4 → ℝ => screenX (B (p 0)) (ψ (p 0))) slab :=
    (hBs.pow 2).mul ((contDiffOn_const.mul hs).exp)
  have hzz : ContDiffOn ℝ ∞ (fun p : Fin 4 → ℝ => screenZ (B (p 0)) (ψ (p 0))) slab :=
    (hBs.pow 2).mul ((contDiffOn_const.mul hs).exp)
  have huu : ContDiffOn ℝ ∞ (fun p : Fin 4 → ℝ => -2 * deriv B (p 0) * p 1) slab :=
    (contDiffOn_const.mul hBds).mul (hp 1)
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> first | exact contDiffOn_const | exact hxx | exact hzz
  · intro i j
    fin_cases i <;> fin_cases j <;>
      first | exact contDiffOn_const | exact hBs.neg | exact huu | exact hxx | exact hzz

end Burnett.RosenMultiscale
