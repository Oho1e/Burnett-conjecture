import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

noncomputable section

namespace Burnett.CubicExplicit

open scoped ContDiff BigOperators

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev Index := Fin 4

def coord (i : Index) : Space →L[ℝ] ℝ := EuclideanSpace.proj i
def u : Space →L[ℝ] ℝ := coord 0 - coord 1
def v : Space →L[ℝ] ℝ := coord 0 + coord 1
def basis (i : Index) : Space := EuclideanSpace.single i 1

@[simp] theorem basis_apply (i j : Index) : basis i j = if j = i then 1 else 0 :=
  EuclideanSpace.single_apply i 1 j

@[simp] theorem coord_apply (i : Index) (x : Space) : coord i x = x i := rfl
@[simp] theorem u_apply (x : Space) : u x = x 0 - x 1 := rfl
@[simp] theorem v_apply (x : Space) : v x = x 0 + x 1 := rfl

@[simp] theorem u_basis (i : Index) :
    u (basis i) = (if i = 0 then 1 else 0) - (if i = 1 then 1 else 0) := by
  simp [basis, EuclideanSpace.single_apply, eq_comm]

@[simp] theorem v_basis (i : Index) :
    v (basis i) = (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) := by
  simp [basis, EuclideanSpace.single_apply, eq_comm]

/-- The actual coordinate derivative of a scalar function. -/
def D (i : Index) (f : Space → ℝ) (x : Space) : ℝ := fderiv ℝ f x (basis i)

def waveF (lam μ : ℝ) (x : Space) : ℝ :=
  lam⁻¹ * (Real.cos (μ * v x) * Real.sin (lam * u x))

def waveW (μ : ℝ) (x : Space) : ℝ :=
  (2 * μ)⁻¹ * Real.sin (2 * μ * v x)

/-- A continuous-linear-map expression obtained by the actual chain/product rule. -/
def waveFGradient (lam μ : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  lam⁻¹ • (Real.cos (μ * v x) • (Real.cos (lam * u x) • (lam • u)) +
    Real.sin (lam * u x) • (-Real.sin (μ * v x) • (μ • v)))

def waveWGradient (μ : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (2 * μ)⁻¹ • (Real.cos (2 * μ * v x) • ((2 * μ) • v))

theorem waveF_hasFDerivAt (lam μ : ℝ) (x : Space) :
    HasFDerivAt (waveF lam μ) (waveFGradient lam μ x) x := by
  have hc := ((μ • v).hasFDerivAt (x := x)).cos
  have hs := ((lam • u).hasFDerivAt (x := x)).sin
  simpa only [waveF, waveFGradient, ContinuousLinearMap.smul_apply, smul_eq_mul] using
    (hc.mul hs).const_mul lam⁻¹

theorem waveW_hasFDerivAt (μ : ℝ) (x : Space) :
    HasFDerivAt (waveW μ) (waveWGradient μ x) x := by
  have hs := (((2 * μ) • v).hasFDerivAt (x := x)).sin
  simpa only [waveW, waveWGradient, ContinuousLinearMap.smul_apply, smul_eq_mul] using
    hs.const_mul (2 * μ)⁻¹

/-- This uses the C∞ order ∞ in WithTop ℕ∞, not the analytic order ω. -/
theorem waveF_smooth (lam μ : ℝ) : ContDiff ℝ ∞ (waveF lam μ) := by
  have hc : ContDiff ℝ ∞ (fun x : Space => Real.cos (μ * v x)) := (μ • v).contDiff.cos
  have hs : ContDiff ℝ ∞ (fun x : Space => Real.sin (lam * u x)) := (lam • u).contDiff.sin
  exact contDiff_const.mul (hc.mul hs)

theorem waveW_smooth (μ : ℝ) : ContDiff ℝ ∞ (waveW μ) := by
  have hs : ContDiff ℝ ∞ (fun x : Space => Real.sin (2 * μ * v x)) := ((2 * μ) • v).contDiff.sin
  exact contDiff_const.mul hs

theorem D_waveF (lam μ : ℝ) (hlam : lam ≠ 0) (i : Index) (x : Space) :
    D i (waveF lam μ) x =
      Real.cos (μ * v x) * Real.cos (lam * u x) * u (basis i) -
      (μ / lam) * Real.sin (μ * v x) * Real.sin (lam * u x) * v (basis i) := by
  unfold D
  rw [(waveF_hasFDerivAt lam μ x).fderiv]
  simp only [waveFGradient, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
  field_simp [hlam]
  ring

theorem D_waveW (μ : ℝ) (hμ : μ ≠ 0) (i : Index) (x : Space) :
    D i (waveW μ) x = Real.cos (2 * μ * v x) * v (basis i) := by
  unfold D
  rw [(waveW_hasFDerivAt μ x).fderiv]
  simp only [waveWGradient, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [hμ]

theorem D_time_waveF (lam μ : ℝ) (hlam : lam ≠ 0) (x : Space) :
    D 0 (waveF lam μ) x = Real.cos (μ * v x) * Real.cos (lam * u x) -
      (μ / lam) * Real.sin (μ * v x) * Real.sin (lam * u x) := by
  simpa using D_waveF lam μ hlam 0 x

theorem D_space_waveF (lam μ : ℝ) (hlam : lam ≠ 0) (x : Space) :
    D 1 (waveF lam μ) x = -Real.cos (μ * v x) * Real.cos (lam * u x) -
      (μ / lam) * Real.sin (μ * v x) * Real.sin (lam * u x) := by
  simpa using D_waveF lam μ hlam 1 x

theorem D_y_waveF (lam μ : ℝ) (hlam : lam ≠ 0) (x : Space) : D 2 (waveF lam μ) x = 0 := by
  simpa using D_waveF lam μ hlam 2 x

theorem D_z_waveF (lam μ : ℝ) (hlam : lam ≠ 0) (x : Space) : D 3 (waveF lam μ) x = 0 := by
  simpa using D_waveF lam μ hlam 3 x

theorem D_time_waveW (μ : ℝ) (hμ : μ ≠ 0) (x : Space) :
    D 0 (waveW μ) x = Real.cos (2 * μ * v x) := by simpa using D_waveW μ hμ 0 x

theorem D_space_waveW (μ : ℝ) (hμ : μ ≠ 0) (x : Space) :
    D 1 (waveW μ) x = Real.cos (2 * μ * v x) := by simpa using D_waveW μ hμ 1 x

theorem D_y_waveW (μ : ℝ) (hμ : μ ≠ 0) (x : Space) : D 2 (waveW μ) x = 0 := by
  simpa using D_waveW μ hμ 2 x

theorem D_z_waveW (μ : ℝ) (hμ : μ ≠ 0) (x : Space) : D 3 (waveW μ) x = 0 := by
  simpa using D_waveW μ hμ 3 x

/-- The actual Minkowski contraction of the two derivative covectors. -/
def nullForm (f w : Space → ℝ) (x : Space) : ℝ :=
  -D 0 f x * D 0 w x + D 1 f x * D 1 w x + D 2 f x * D 2 w x + D 3 f x * D 3 w x

theorem nullForm_waveF_waveW (lam μ : ℝ) (hlam : lam ≠ 0) (hμ : μ ≠ 0) (x : Space) :
    nullForm (waveF lam μ) (waveW μ) x =
      -2 * Real.cos (μ * v x) * Real.cos (lam * u x) * Real.cos (2 * μ * v x) := by
  simp only [nullForm, D_time_waveF lam μ hlam, D_space_waveF lam μ hlam,
    D_y_waveF lam μ hlam, D_z_waveF lam μ hlam, D_time_waveW μ hμ, D_space_waveW μ hμ,
    D_y_waveW μ hμ, D_z_waveW μ hμ]
  ring

def cubicMain (lam μ : ℝ) (x : Space) : ℝ :=
  -2 * Real.cos (μ * v x)^2 * Real.cos (2 * μ * v x) * Real.cos (lam * u x)^2

def cubicRemainder (lam μ : ℝ) (x : Space) : ℝ :=
  (2 * μ / lam) * (Real.cos (μ * v x) * Real.sin (μ * v x) * Real.cos (2 * μ * v x) *
    Real.cos (lam * u x) * Real.sin (lam * u x))

theorem cubic_product_decomposition (lam μ : ℝ) (hlam : lam ≠ 0) (hμ : μ ≠ 0) (x : Space) :
    nullForm (waveF lam μ) (waveW μ) x * D 0 (waveF lam μ) x =
      cubicMain lam μ x + cubicRemainder lam μ x := by
  rw [nullForm_waveF_waveW lam μ hlam hμ, D_time_waveF lam μ hlam]
  unfold cubicMain cubicRemainder
  ring

theorem seven_modes (a b : ℝ) :
    -2 * Real.cos a ^ 2 * Real.cos (2 * a) * Real.cos b ^ 2 =
      -1/4 - (1/2)*Real.cos (2*a) - (1/4)*Real.cos (4*a) - (1/4)*Real.cos (2*b) -
      (1/4)*Real.cos (2*a+2*b) - (1/4)*Real.cos (2*a-2*b) -
      (1/8)*Real.cos (4*a+2*b) - (1/8)*Real.cos (4*a-2*b) := by
  have h4 : Real.cos (4 * a) = 2 * Real.cos (2 * a)^2 - 1 := by
    calc
      Real.cos (4 * a) = Real.cos (2 * (2 * a)) := congrArg Real.cos (by ring)
      _ = _ := Real.cos_two_mul (2 * a)
  simp only [Real.cos_add, Real.cos_sub, h4, Real.cos_two_mul]
  ring

def cosCos (lam μ : ℝ) (x : Space) : ℝ := Real.cos (μ * v x) * Real.cos (lam * u x)
def sinSin (lam μ : ℝ) (x : Space) : ℝ := Real.sin (μ * v x) * Real.sin (lam * u x)

def cosCosGradient (lam μ : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  Real.cos (μ * v x) • (-Real.sin (lam * u x) • (lam • u)) +
    Real.cos (lam * u x) • (-Real.sin (μ * v x) • (μ • v))

def sinSinGradient (lam μ : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  Real.sin (μ * v x) • (Real.cos (lam * u x) • (lam • u)) +
    Real.sin (lam * u x) • (Real.cos (μ * v x) • (μ • v))

theorem cosCos_hasFDerivAt (lam μ : ℝ) (x : Space) :
    HasFDerivAt (cosCos lam μ) (cosCosGradient lam μ x) x := by
  have hc := ((μ • v).hasFDerivAt (x := x)).cos
  have hd := ((lam • u).hasFDerivAt (x := x)).cos
  simpa only [cosCos, cosCosGradient, ContinuousLinearMap.smul_apply, smul_eq_mul] using hc.mul hd

theorem sinSin_hasFDerivAt (lam μ : ℝ) (x : Space) :
    HasFDerivAt (sinSin lam μ) (sinSinGradient lam μ x) x := by
  have hc := ((μ • v).hasFDerivAt (x := x)).sin
  have hd := ((lam • u).hasFDerivAt (x := x)).sin
  simpa only [sinSin, sinSinGradient, ContinuousLinearMap.smul_apply, smul_eq_mul] using hc.mul hd

theorem D_time_time_waveF (lam μ : ℝ) (hlam : lam ≠ 0) (x : Space) :
    D 0 (D 0 (waveF lam μ)) x =
      -2*μ*Real.sin (μ*v x)*Real.cos (lam*u x) -
      (lam+μ^2/lam)*Real.cos (μ*v x)*Real.sin (lam*u x) := by
  have hf : D 0 (waveF lam μ) = fun y => cosCos lam μ y - (μ/lam)*sinSin lam μ y := by
    funext y
    simpa only [cosCos, sinSin, mul_assoc] using D_time_waveF lam μ hlam y
  rw [hf]
  unfold D
  have hd := ((cosCos_hasFDerivAt lam μ x).sub ((sinSin_hasFDerivAt lam μ x).const_mul (μ/lam))).fderiv
  change fderiv ℝ (fun y => cosCos lam μ y - (μ/lam)*sinSin lam μ y) x = _ at hd
  rw [hd]
  simp only [cosCosGradient, sinSinGradient, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [u_basis, v_basis]
  norm_num
  field_simp [hlam]
  ring

theorem D_space_space_waveF (lam μ : ℝ) (hlam : lam ≠ 0) (x : Space) :
    D 1 (D 1 (waveF lam μ)) x =
      2*μ*Real.sin (μ*v x)*Real.cos (lam*u x) -
      (lam+μ^2/lam)*Real.cos (μ*v x)*Real.sin (lam*u x) := by
  have hf : D 1 (waveF lam μ) = fun y => -cosCos lam μ y - (μ/lam)*sinSin lam μ y := by
    funext y
    simpa only [cosCos, sinSin, mul_assoc, neg_mul] using D_space_waveF lam μ hlam y
  rw [hf]
  unfold D
  have hd := ((cosCos_hasFDerivAt lam μ x).neg.sub ((sinSin_hasFDerivAt lam μ x).const_mul (μ/lam))).fderiv
  change fderiv ℝ (fun y => -cosCos lam μ y - (μ/lam)*sinSin lam μ y) x = _ at hd
  rw [hd]
  simp only [cosCosGradient, sinSinGradient, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [u_basis, v_basis]
  norm_num
  field_simp [hlam]
  ring

/-- The actual coordinate Minkowski wave operator. -/
def waveOperator (f : Space → ℝ) (x : Space) : ℝ :=
  -D 0 (D 0 f) x + D 1 (D 1 f) x + D 2 (D 2 f) x + D 3 (D 3 f) x

theorem waveOperator_waveF (lam μ : ℝ) (hlam : lam ≠ 0) (x : Space) :
    waveOperator (waveF lam μ) x = 4*μ*Real.sin (μ*v x)*Real.cos (lam*u x) := by
  have hy : D 2 (waveF lam μ) = fun _ => 0 := funext (D_y_waveF lam μ hlam)
  have hz : D 3 (waveF lam μ) = fun _ => 0 := funext (D_z_waveF lam μ hlam)
  rw [waveOperator, D_time_time_waveF lam μ hlam, D_space_space_waveF lam μ hlam, hy, hz]
  simp [D]
  ring

theorem waveOperator_waveW (μ : ℝ) (hμ : μ ≠ 0) (x : Space) :
    waveOperator (waveW μ) x = 0 := by
  have ht : D 0 (waveW μ) = fun y => Real.cos (2*μ*v y) := funext (D_time_waveW μ hμ)
  have hx : D 1 (waveW μ) = fun y => Real.cos (2*μ*v y) := funext (D_space_waveW μ hμ)
  have hy : D 2 (waveW μ) = fun _ => 0 := funext (D_y_waveW μ hμ)
  have hz : D 3 (waveW μ) = fun _ => 0 := funext (D_z_waveW μ hμ)
  rw [waveOperator, ht, hx, hy, hz]
  unfold D
  have hd : fderiv ℝ (fun y : Space => Real.cos (2*μ*v y)) x =
      -Real.sin (2*μ*v x) • ((2*μ) • v) := by
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using
      ((((2*μ) • v).hasFDerivAt (x := x)).cos).fderiv
  rw [hd]
  simp [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- An explicit small scalar potential whose u derivative is the wave source. -/
def sourcePotential (lam μ : ℝ) (x : Space) : ℝ := (4*μ/lam) * sinSin lam μ x

def fluxCoefficient (i : Index) : ℝ := if i = 0 then 1/2 else if i = 1 then -1/2 else 0
def fluxComponent (lam μ : ℝ) (i : Index) (x : Space) : ℝ :=
  fluxCoefficient i * sourcePotential lam μ x
def fluxDivergence (lam μ : ℝ) (x : Space) : ℝ := ∑ i, D i (fluxComponent lam μ i) x

theorem D_fluxComponent (lam μ : ℝ) (i j : Index) (x : Space) :
    D j (fluxComponent lam μ i) x =
      fluxCoefficient i * (4*μ/lam) * sinSinGradient lam μ x (basis j) := by
  have h := ((sinSin_hasFDerivAt lam μ x).const_mul (4*μ/lam)).const_mul (fluxCoefficient i)
  unfold D
  rw [show fderiv ℝ (fluxComponent lam μ i) x =
    fluxCoefficient i • ((4*μ/lam) • sinSinGradient lam μ x) from h.fderiv]
  simp [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc]

theorem fluxDivergence_eq_wave_source (lam μ : ℝ) (hlam : lam ≠ 0) (x : Space) :
    fluxDivergence lam μ x = 4*μ*Real.sin (μ*v x)*Real.cos (lam*u x) := by
  simp only [fluxDivergence, D_fluxComponent]
  simp [Fin.sum_univ_succ, fluxCoefficient, sinSinGradient,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [hlam]
  ring

/-- Exact coefficients: the flux is (A/2,-A/2,0,0), not (A,-A,0,0). -/
theorem waveOperator_waveF_eq_divergence (lam μ : ℝ) (hlam : lam ≠ 0) (x : Space) :
    waveOperator (waveF lam μ) x = fluxDivergence lam μ x := by
  rw [waveOperator_waveF lam μ hlam, fluxDivergence_eq_wave_source lam μ hlam]

private theorem abs_product_le_one {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a*b| ≤ 1 := by
  calc
    |a*b| = |a| * |b| := abs_mul a b
    _ ≤ 1*1 := mul_le_mul ha hb (abs_nonneg b) (by norm_num)
    _ = 1 := by ring

theorem waveF_abs_le (lam μ : ℝ) (hlam : 0 < lam) (x : Space) :
    |waveF lam μ x| ≤ lam⁻¹ := by
  have hp := abs_product_le_one (Real.abs_cos_le_one (μ*v x)) (Real.abs_sin_le_one (lam*u x))
  rw [waveF, abs_mul, abs_inv, abs_of_pos hlam]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hlam.le)

theorem waveW_abs_le (μ : ℝ) (hμ : 0 < μ) (x : Space) :
    |waveW μ x| ≤ (2*μ)⁻¹ := by
  have hpos : 0 < 2*μ := mul_pos (by norm_num) hμ
  rw [waveW, abs_mul, abs_inv, abs_of_pos hpos]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.abs_sin_le_one (2*μ*v x)) (inv_nonneg.mpr hpos.le)

theorem D_waveF_abs_le_two (lam μ : ℝ) (hlam : lam ≠ 0) (hratio : |μ/lam| ≤ 1)
    (i : Index) (x : Space) : |D i (waveF lam μ) x| ≤ 2 := by
  have hu : |u (basis i)| ≤ 1 := by fin_cases i <;> norm_num [basis, EuclideanSpace.single_apply]
  have hv : |v (basis i)| ≤ 1 := by fin_cases i <;> norm_num [basis, EuclideanSpace.single_apply]
  have ha := abs_product_le_one
    (abs_product_le_one (Real.abs_cos_le_one (μ*v x)) (Real.abs_cos_le_one (lam*u x))) hu
  have hb := abs_product_le_one
    (abs_product_le_one (abs_product_le_one hratio (Real.abs_sin_le_one (μ*v x)))
      (Real.abs_sin_le_one (lam*u x))) hv
  rw [D_waveF lam μ hlam]
  calc
    _ ≤ |Real.cos (μ*v x)*Real.cos (lam*u x)*u (basis i)| +
        |(μ/lam)*Real.sin (μ*v x)*Real.sin (lam*u x)*v (basis i)| := abs_sub _ _
    _ ≤ 1+1 := add_le_add ha hb
    _ = 2 := by ring

theorem D_waveW_abs_le_one (μ : ℝ) (hμ : μ ≠ 0) (i : Index) (x : Space) :
    |D i (waveW μ) x| ≤ 1 := by
  have hv : |v (basis i)| ≤ 1 := by fin_cases i <;> norm_num [basis, EuclideanSpace.single_apply]
  rw [D_waveW μ hμ]
  exact abs_product_le_one (Real.abs_cos_le_one (2*μ*v x)) hv

theorem cubicRemainder_abs_le (lam μ : ℝ) (x : Space) :
    |cubicRemainder lam μ x| ≤ 2* |μ/lam| := by
  have hp := abs_product_le_one
    (abs_product_le_one
      (abs_product_le_one
        (abs_product_le_one (Real.abs_cos_le_one (μ*v x)) (Real.abs_sin_le_one (μ*v x)))
        (Real.abs_cos_le_one (2*μ*v x)))
      (Real.abs_cos_le_one (lam*u x)))
    (Real.abs_sin_le_one (lam*u x))
  have hc : 2*μ/lam = 2*(μ/lam) := by ring
  rw [cubicRemainder, hc, abs_mul, abs_mul]
  norm_num
  simpa only [mul_one, abs_mul, u_apply, v_apply] using mul_le_mul_of_nonneg_left hp
    (show (0 : ℝ) ≤ 2*|μ/lam| from mul_nonneg (by norm_num) (abs_nonneg (μ/lam)))

theorem sourcePotential_abs_le (lam μ : ℝ) (x : Space) :
    |sourcePotential lam μ x| ≤ 4* |μ/lam| := by
  have hp := abs_product_le_one (Real.abs_sin_le_one (μ*v x)) (Real.abs_sin_le_one (lam*u x))
  have hc : 4*μ/lam = 4*(μ/lam) := by ring
  rw [sourcePotential, sinSin, hc, abs_mul, abs_mul]
  norm_num
  simpa only [mul_one, abs_mul, u_apply, v_apply] using mul_le_mul_of_nonneg_left hp
    (show (0 : ℝ) ≤ 4*|μ/lam| from mul_nonneg (by norm_num) (abs_nonneg (μ/lam)))

theorem fluxCoefficient_abs_le (i : Index) : |fluxCoefficient i| ≤ 1/2 := by
  unfold fluxCoefficient
  split_ifs <;> norm_num

theorem fluxComponent_abs_le (lam μ : ℝ) (i : Index) (x : Space) :
    |fluxComponent lam μ i x| ≤ 2* |μ/lam| := by
  rw [fluxComponent, abs_mul]
  calc
    _ ≤ (1/2)*(4* |μ/lam|) := mul_le_mul (fluxCoefficient_abs_le i)
      (sourcePotential_abs_le lam μ x) (abs_nonneg _) (by norm_num)
    _ = _ := by ring

/-- Positive integer reindexing of the manuscript's n, avoiding division by zero. -/
def N (n : ℕ) : ℝ := n + 1
def fSequence (n : ℕ) : Space → ℝ := waveF ((N n)^2) (N n)
def wSequence (n : ℕ) : Space → ℝ := waveW (N n)

theorem N_ge_one (n : ℕ) : 1 ≤ N n := by
  unfold N
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

theorem N_pos (n : ℕ) : 0 < N n := lt_of_lt_of_le (by norm_num) (N_ge_one n)
theorem N_ne_zero (n : ℕ) : N n ≠ 0 := ne_of_gt (N_pos n)

theorem N_ratio (n : ℕ) : N n / (N n)^2 = (N n)⁻¹ := by
  field_simp [N_ne_zero n, pow_two]

theorem N_ratio_abs_le_one (n : ℕ) : |N n / (N n)^2| ≤ 1 := by
  rw [N_ratio, abs_of_pos (inv_pos.mpr (N_pos n))]
  exact inv_le_one_of_one_le₀ (N_ge_one n)

theorem fSequence_smooth (n : ℕ) : ContDiff ℝ ∞ (fSequence n) := waveF_smooth _ _
theorem wSequence_smooth (n : ℕ) : ContDiff ℝ ∞ (wSequence n) := waveW_smooth _

theorem fSequence_abs_le (n : ℕ) (x : Space) : |fSequence n x| ≤ ((N n)^2)⁻¹ :=
  waveF_abs_le _ _ (pow_pos (N_pos n) 2) x

theorem wSequence_abs_le (n : ℕ) (x : Space) : |wSequence n x| ≤ (2*N n)⁻¹ :=
  waveW_abs_le _ (N_pos n) x

theorem D_fSequence_abs_le_two (n : ℕ) (i : Index) (x : Space) : |D i (fSequence n) x| ≤ 2 :=
  D_waveF_abs_le_two _ _ (pow_ne_zero 2 (N_ne_zero n)) (N_ratio_abs_le_one n) i x

theorem D_wSequence_abs_le_one (n : ℕ) (i : Index) (x : Space) : |D i (wSequence n) x| ≤ 1 :=
  D_waveW_abs_le_one _ (N_ne_zero n) i x

theorem cubicRemainder_sequence_abs_le (n : ℕ) (x : Space) :
    |cubicRemainder ((N n)^2) (N n) x| ≤ 2/N n := by
  calc
    _ ≤ 2* |N n / (N n)^2| := cubicRemainder_abs_le _ _ x
    _ = _ := by rw [N_ratio, abs_of_pos (inv_pos.mpr (N_pos n))]; rfl

theorem sourcePotential_sequence_abs_le (n : ℕ) (x : Space) :
    |sourcePotential ((N n)^2) (N n) x| ≤ 4/N n := by
  calc
    _ ≤ 4* |N n / (N n)^2| := sourcePotential_abs_le _ _ x
    _ = _ := by rw [N_ratio, abs_of_pos (inv_pos.mpr (N_pos n))]; rfl

theorem cubicSequence_decomposition (n : ℕ) (x : Space) :
    nullForm (fSequence n) (wSequence n) x * D 0 (fSequence n) x =
      cubicMain ((N n)^2) (N n) x + cubicRemainder ((N n)^2) (N n) x :=
  cubic_product_decomposition _ _ (pow_ne_zero 2 (N_ne_zero n)) (N_ne_zero n) x

/-- The actual Euclidean flux vector for the divergence representation. -/
def fluxVector (lam μ : ℝ) (x : Space) : Space :=
  (sourcePotential lam μ x / 2) • (basis 0 - basis 1)

theorem fluxVector_component (lam μ : ℝ) (x : Space) (i : Index) :
    fluxVector lam μ x i = fluxComponent lam μ i x := by
  fin_cases i <;>
    simp [fluxVector, fluxComponent, fluxCoefficient, basis, EuclideanSpace.single_apply,
      PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] <;> ring

theorem fluxVector_norm_le (lam μ : ℝ) (x : Space) :
    ‖fluxVector lam μ x‖ ≤ |sourcePotential lam μ x| := by
  have hb0 : ‖basis 0‖ = 1 := by simp [basis]
  have hb1 : ‖basis 1‖ = 1 := by simp [basis]
  have hd : ‖basis 0 - basis 1‖ ≤ 2 := by
    have h := norm_sub_le (basis 0) (basis 1)
    rw [hb0, hb1] at h
    norm_num at h
    exact h
  rw [fluxVector, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ (|sourcePotential lam μ x|/2)*2 := mul_le_mul_of_nonneg_left hd (div_nonneg (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem fluxVector_sequence_norm_le (n : ℕ) (x : Space) :
    ‖fluxVector ((N n)^2) (N n) x‖ ≤ 4/N n :=
  (fluxVector_norm_le _ _ x).trans (sourcePotential_sequence_abs_le n x)

theorem actual_flux_divergence (lam μ : ℝ) (x : Space) :
    (∑ i, D i (fun y => fluxVector lam μ y i) x) = fluxDivergence lam μ x := by
  unfold fluxDivergence
  apply Finset.sum_congr rfl
  intro i hi
  have hf : (fun y => fluxVector lam μ y i) = fluxComponent lam μ i :=
    funext (fun y => fluxVector_component lam μ y i)
  rw [hf]

theorem waveOperator_waveF_eq_actual_flux_divergence (lam μ : ℝ) (hlam : lam ≠ 0) (x : Space) :
    waveOperator (waveF lam μ) x = ∑ i, D i (fun y => fluxVector lam μ y i) x := by
  rw [actual_flux_divergence, waveOperator_waveF_eq_divergence lam μ hlam]

end Burnett.CubicExplicit
