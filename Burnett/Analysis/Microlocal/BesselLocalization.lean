import Burnett.Analysis.Microlocal.AngularCommutator.Infrared
import Burnett.Analysis.HminusWeightedDual
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Burnett.Analysis.Fourier.L2Extension
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Burnett.Analysis.Fourier.Projection
import Burnett.Analysis.LocalHminusFourier

/-!
# Bessel regularization of a first-order coordinate system

The order-zero principal action follows from the negative Fourier energy
of the actual row and the compactly supported distributional limits.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.BesselLocalization

open MeasureTheory Filter Set Burnett.Fourier Burnett.Analysis.HminusWeightedDual
open Burnett.X02.SobolevTestJet
open scoped FourierTransform ContDiff Topology

private theorem twoPi_pos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos

private theorem frequencyWeight_root_pos (ξ : Space) : 0 < Real.sqrt (frequencyWeight ξ) :=
  Real.sqrt_pos.mpr (frequencyWeight_pos ξ)

private theorem one_le_frequencyWeight_root (ξ : Space) : 1 ≤ Real.sqrt (frequencyWeight ξ) := by
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (frequencyWeight_one_le ξ)

private theorem radial_le_frequencyWeight_root (ξ : Space) :
    2 * Real.pi * ‖ξ‖ ≤ Real.sqrt (frequencyWeight ξ) := by
  have ha : 0 ≤ 2 * Real.pi * ‖ξ‖ := mul_nonneg twoPi_pos.le (norm_nonneg ξ)
  apply (sq_le_sq₀ ha (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (frequencyWeight_pos ξ).le, frequencyWeight]
  ring_nf
  linarith

/-- The genuine inverse Bessel weight for the pinned $H^1$ test norm. -/
def bessel (ξ : Space) : ℂ := ((Real.sqrt (frequencyWeight ξ))⁻¹ : ℝ)

theorem continuous_bessel : Continuous bessel :=
  Complex.continuous_ofReal.comp
    (frequencyWeight_continuous.sqrt.inv₀ fun ξ => (frequencyWeight_root_pos ξ).ne')

theorem norm_bessel_le_one (ξ : Space) : ‖bessel ξ‖ ≤ 1 := by
  rw [bessel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_le_one_of_one_le₀ (one_le_frequencyWeight_root ξ)

def besselSymbol : BoundedSymbol Space where
  toFun := bessel
  measurable := continuous_bessel.aestronglyMeasurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := norm_bessel_le_one

/-- The bounded Fourier symbol of the directional derivative followed by
the fixed inverse Bessel operator, with the actual Fourier sign and $2π$. -/
def regularizedDirection (v ξ : Space) : ℂ :=
  Complex.I * ((2 * Real.pi * inner ℝ ξ v) / Real.sqrt (frequencyWeight ξ) : ℝ)

def angularDirection (v ξ : Space) : ℂ :=
  Complex.I * ((inner ℝ ξ v) / ‖ξ‖ : ℝ)

theorem continuous_regularizedDirection (v : Space) : Continuous (regularizedDirection v) := by
  unfold regularizedDirection
  apply continuous_const.mul
  apply Complex.continuous_ofReal.comp
  exact (continuous_const.mul (continuous_id.inner continuous_const)).div
    frequencyWeight_continuous.sqrt (fun ξ => (frequencyWeight_root_pos ξ).ne')

theorem measurable_angularDirection (v : Space) : Measurable (angularDirection v) := by
  unfold angularDirection
  exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp
    ((continuous_id.inner continuous_const).measurable.div continuous_norm.measurable))

theorem norm_regularizedDirection_le (v ξ : Space) : ‖regularizedDirection v ξ‖ ≤ ‖v‖ := by
  simp only [regularizedDirection, norm_mul, Complex.norm_I, Complex.norm_real, one_mul,
    Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg twoPi_pos.le,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (frequencyWeight_root_pos ξ)).mpr
  calc
    2 * Real.pi * |inner ℝ ξ v| ≤ 2 * Real.pi * (‖ξ‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) _ _) twoPi_pos.le
    _ = 2 * Real.pi * ‖ξ‖ * ‖v‖ := by ring
    _ ≤ Real.sqrt (frequencyWeight ξ) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (radial_le_frequencyWeight_root ξ) (norm_nonneg _)
    _ = ‖v‖ * Real.sqrt (frequencyWeight ξ) := mul_comm _ _

theorem norm_angularDirection_le (v ξ : Space) : ‖angularDirection v ξ‖ ≤ ‖v‖ := by
  by_cases hξ : ξ = 0
  · simp [hξ, angularDirection]
  · simp only [angularDirection, norm_mul, Complex.norm_I, Complex.norm_real, one_mul,
      Real.norm_eq_abs, abs_div, abs_norm]
    apply (div_le_iff₀ (norm_pos_iff.mpr hξ)).mpr
    simpa only [mul_comm ‖v‖ ‖ξ‖] using (norm_inner_le_norm (𝕜 := ℝ) ξ v)

def regularizedDirectionSymbol (v : Space) : BoundedSymbol Space where
  toFun := regularizedDirection v
  measurable := (continuous_regularizedDirection v).aestronglyMeasurable
  bound := ‖v‖
  bound_nonneg := norm_nonneg _
  norm_le := norm_regularizedDirection_le v

def angularDirectionSymbol (v : Space) : BoundedSymbol Space where
  toFun := angularDirection v
  measurable := (measurable_angularDirection v).aestronglyMeasurable
  bound := ‖v‖
  bound_nonneg := norm_nonneg _
  norm_le := norm_angularDirection_le v

/-- The inverse Bessel operator sees exactly the pinned negative energy. -/
theorem besselLp_norm_sq_eq_negativeEnergy (f : SchwartzMap Space ℂ) :
    ‖fourierMultiplier besselSymbol (f.toLp 2 volume)‖ ^ 2 = negativeEnergy f := by
  rw [fourierMultiplier_apply, LinearIsometryEquiv.norm_map, l2_norm_sq_integral, negativeEnergy]
  apply integral_congr_ae
  filter_upwards [symbolL2_ae besselSymbol (fourierL2Equiv (f.toLp 2 volume)),
    fourierL2Equiv_schwartz_ae f] with ξ hsymbol hfourier
  rw [hsymbol, hfourier]
  change ‖bessel ξ * 𝓕 (f : Space → ℂ) ξ‖ ^ 2 =
    ‖𝓕 (f : Space → ℂ) ξ‖ ^ 2 / frequencyWeight ξ
  simp only [bessel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg
    (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt (frequencyWeight_pos ξ).le, div_eq_mul_inv]
  rw [mul_comm]

/-- On actual Schwartz source data, the Bessel regularization of the
directional derivative is the fixed order-zero Fourier multiplier. -/
theorem besselLp_pderiv (f : SchwartzMap Space ℂ) (v : Space) :
    fourierMultiplier besselSymbol ((SchwartzMap.pderivCLM ℂ v f).toLp 2 volume) =
      fourierMultiplier (regularizedDirectionSymbol v) (f.toLp 2 volume) := by
  apply (fourierL2Equiv (V := Space)).injective
  rw [fourier_fourierMultiplier, fourier_fourierMultiplier]
  apply Lp.ext
  filter_upwards [symbolL2_ae besselSymbol (fourierL2Equiv ((SchwartzMap.pderivCLM ℂ v f).toLp 2 volume)),
    symbolL2_ae (regularizedDirectionSymbol v) (fourierL2Equiv (f.toLp 2 volume)),
    fourierL2Equiv_schwartz_ae (SchwartzMap.pderivCLM ℂ v f), fourierL2Equiv_schwartz_ae f]
    with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, fourier_pderiv]
  change bessel ξ * ((2 * Real.pi * Complex.I) * (inner ℝ ξ v : ℂ) * 𝓕 (f : Space → ℂ) ξ) =
    regularizedDirection v ξ * 𝓕 (f : Space → ℂ) ξ
  simp only [bessel, regularizedDirection, Complex.ofReal_inv, Complex.ofReal_mul,
    div_eq_mul_inv, Complex.ofReal_ofNat]
  ring

end Burnett.Microlocal.BesselLocalization

namespace Burnett.Microlocal.BesselLocalization

open MeasureTheory Filter Set Burnett.Fourier Burnett.Analysis.HminusWeightedDual
open Burnett.Microlocal.AngularCommutator
open Burnett.X02.SobolevTestJet Burnett.Analysis.LocalHminusFourier
open scoped FourierTransform ContDiff Topology

theorem angularDirection_contDiffOn (v : Space) :
    ContDiffOn ℝ ∞ (angularDirection v) ({0}ᶜ : Set Space) := by
  intro ξ hξ
  have h0 : ξ ≠ 0 := hξ
  have hc : ContDiff ℝ ∞ (fun y : Space => inner ℝ y v) := by
    simpa only [innerSL_apply, real_inner_comm v] using (innerSL ℝ v).contDiff
  have hd := hc.contDiffWithinAt.div
    ((contDiffAt_norm ℝ h0).contDiffWithinAt (s := ({0}ᶜ : Set Space))) (norm_ne_zero_iff.mpr h0)
  exact contDiffWithinAt_const.mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp_contDiffWithinAt ξ hd)

theorem angularDirection_degreeZero (v : Space) : DegreeZero (angularDirection v) := by
  intro r hr ξ
  rw [angularDirection, angularDirection, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, mul_div_mul_left _ _ hr.ne']

private theorem frequencyWeight_root_le_radial_add_one (ξ : Space) :
    Real.sqrt (frequencyWeight ξ) ≤ 2 * Real.pi * ‖ξ‖ + 1 := by
  have hb : 0 ≤ 2 * Real.pi * ‖ξ‖ := mul_nonneg twoPi_pos.le (norm_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg hb zero_le_one)).mp
  rw [Real.sq_sqrt (frequencyWeight_pos ξ).le, frequencyWeight]
  nlinarith [Real.pi_pos, norm_nonneg ξ]

/-- The actual normalized order-zero principal multiplier differs from the
Bessel-regularized directional multiplier by a symbol decaying at infinity. -/
theorem norm_regularizedDirection_sub_angularDirection_le (v ξ : Space) :
    ‖regularizedDirection v ξ - angularDirection v ξ‖ ≤
      ‖v‖ / Real.sqrt (frequencyWeight ξ) := by
  by_cases hξ : ξ = 0
  · simp [hξ, regularizedDirection, angularDirection, frequencyWeight]
  · let a := 2 * Real.pi * ‖ξ‖
    let b := Real.sqrt (frequencyWeight ξ)
    have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hb : 0 < b := frequencyWeight_root_pos ξ
    have ha : a ≤ b := radial_le_frequencyWeight_root ξ
    have hab : b - a ≤ 1 := by
      have h := frequencyWeight_root_le_radial_add_one ξ
      change b ≤ a + 1 at h
      linarith
    have heq : regularizedDirection v ξ - angularDirection v ξ =
        (((a - b) / b : ℝ) : ℂ) * angularDirection v ξ := by
      rw [regularizedDirection, angularDirection]
      simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub]
      unfold a b
      have hv : (‖ξ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm.ne'
      have hb' : (Real.sqrt (frequencyWeight ξ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
      field_simp
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_nonneg hb.le, abs_of_nonpos (sub_nonpos.mpr ha), neg_sub]
    calc
      (b - a) / b * ‖angularDirection v ξ‖ ≤
          1 / b * ‖angularDirection v ξ‖ :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hab hb.le) (norm_nonneg _)
      _ ≤ 1 / b * ‖v‖ :=
        mul_le_mul_of_nonneg_left (norm_angularDirection_le v ξ) (by positivity)
      _ = ‖v‖ / b := by ring

theorem directionRemainder_small_outside_ball (v : Space) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ ξ : Space, ξ ∉ Metric.closedBall 0 R →
      ‖regularizedDirection v ξ - angularDirection v ξ‖ ≤ ε := by
  let R := (‖v‖ + 1) / (2 * Real.pi * ε)
  refine ⟨R, fun ξ hξ => (norm_regularizedDirection_sub_angularDirection_le v ξ).trans ?_⟩
  have hR : R < ‖ξ‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hξ
  have hbound : ‖v‖ + 1 < ‖ξ‖ * (2 * Real.pi * ε) :=
    (div_lt_iff₀ (mul_pos twoPi_pos hε)).mp hR
  apply (div_le_iff₀ (frequencyWeight_root_pos ξ)).mpr
  have hh := mul_le_mul_of_nonneg_left (radial_le_frequencyWeight_root ξ) hε.le
  linarith [show ‖ξ‖ * (2 * Real.pi * ε) = ε * (2 * Real.pi * ‖ξ‖) by ring]

/-- Replacing the actual Bessel-regularized directional multiplier by its
homogeneous principal part has strongly zero error on the original sequence. -/
theorem bessel_pderiv_minus_angular_tendsto_zero
    (v : Space) (f : ℕ → Space → ℝ) (hs : ∀ k, ContDiff ℝ ∞ (f k))
    (hf : ∀ k, MemLp (f k) 2 (volume : Measure Space))
    (χ0 : D) (hχ0 : ∀ k x, f k x ≠ 0 → (χ0 : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ k, ‖(hf k).toLp (f k)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun k => ∫ x, f k x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun k =>
      fourierMultiplier besselSymbol
        ((SchwartzMap.pderivCLM ℂ v (sourceSchwartz (hs k) χ0 (hχ0 k))).toLp 2 volume) -
      fourierMultiplier (angularDirectionSymbol v) ((sourceSchwartz (hs k) χ0 (hχ0 k)).toLp 2 volume))
      atTop (𝓝 0) := by
  simp_rw [besselLp_pderiv, ← fourierMultiplier_symbolDifference]
  exact vanishingFrequency_tendsto_zero_of_localized_weak_zero
    (symbolDifference (regularizedDirectionSymbol v) (angularDirectionSymbol v))
    (fun ε hε => directionRemainder_small_outside_ball v ε hε) f hs hf χ0 hχ0 B hB ht

end Burnett.Microlocal.BesselLocalization

namespace Burnett.Microlocal.BesselLocalization

open MeasureTheory Filter Set Burnett.Fourier Burnett.Analysis.HminusWeightedDual
open Burnett.Microlocal.AngularCommutator
open Burnett.X02.SobolevTestJet Burnett.Analysis.LocalHminusFourier
open scoped FourierTransform ContDiff Topology

private theorem physicalCoefficient_bound (a : D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Space, ‖((a : Space → ℝ) x : ℂ)‖ ≤ B := by
  obtain ⟨B, hB, h⟩ := ((test_compactSupport a).image (test_smooth a).continuous).isBounded.exists_pos_norm_le
  refine ⟨B, hB.le, fun x => ?_⟩
  rw [Complex.norm_real]
  by_cases hx : x ∈ tsupport (a : Space → ℝ)
  · exact h _ ⟨x, hx, rfl⟩
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact hB.le

def physicalCoefficient (a : D) : BoundedSymbol Space where
  toFun x := ((a : Space → ℝ) x : ℂ)
  measurable := (Complex.continuous_ofReal.comp (test_smooth a).continuous).aestronglyMeasurable
  bound := (physicalCoefficient_bound a).choose
  bound_nonneg := (physicalCoefficient_bound a).choose_spec.1
  norm_le := (physicalCoefficient_bound a).choose_spec.2

def coefficientPDeriv (a : D) (v : Space) : D :=
  ⟨fun x => fderiv ℝ (a : Space → ℝ) x v,
    ⟨((test_smooth a).contDiff_fderiv_apply (by simp : ∞ + 1 ≤ (∞ : WithTop ℕ∞))).comp
      (contDiff_id.prodMk contDiff_const),
      HasCompactSupport.fderiv_apply ℝ (test_compactSupport a) v⟩⟩

def coeffMul (a : D) (u : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  ((test_compactSupport a).comp_left Complex.ofReal_zero).mul_right.toSchwartzMap
    ((Complex.ofRealCLM.contDiff.comp (test_smooth a)).mul (u.smooth ⊤))

theorem coeffMul_toLp (a : D) (u : SchwartzMap Space ℂ) :
    (coeffMul a u).toLp 2 volume = symbolCLM (physicalCoefficient a) (u.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(coeffMul a u).coeFn_toLp 2 volume, u.coeFn_toLp 2 volume,
    symbolL2_ae (physicalCoefficient a) (u.toLp 2 volume)] with x h₁ h₂ h₃
  change (coeffMul a u).toLp 2 volume x = symbolL2 (physicalCoefficient a) (u.toLp 2 volume) x
  rw [h₁, h₃, h₂]
  rfl

theorem pderiv_coeffMul (a : D) (u : SchwartzMap Space ℂ) (v : Space) :
    SchwartzMap.pderivCLM ℂ v (coeffMul a u) =
      coeffMul a (SchwartzMap.pderivCLM ℂ v u) + coeffMul (coefficientPDeriv a v) u := by
  apply SchwartzMap.ext
  intro x
  have ha := (Complex.ofRealCLM.hasFDerivAt).comp x (test_differentiable a x).hasFDerivAt
  change HasFDerivAt (fun y => ((a : Space → ℝ) y : ℂ))
    (Complex.ofRealCLM.comp (fderiv ℝ (a : Space → ℝ) x)) x at ha
  change fderiv ℝ (fun y => ((a : Space → ℝ) y : ℂ) * u y) x v =
    ((a : Space → ℝ) x : ℂ) * fderiv ℝ (u : Space → ℂ) x v +
      (fderiv ℝ (a : Space → ℝ) x v : ℂ) * u x
  rw [fderiv_fun_mul ha.differentiableAt u.differentiableAt, ha.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  ring

/-- Exact normal-operator identity for a variable coefficient derivative.
The lower-order term is the actual derivative of the same coefficient. -/
theorem besselLp_coeffMul_pderiv (a : D) (u : SchwartzMap Space ℂ) (v : Space) :
    fourierMultiplier besselSymbol ((coeffMul a (SchwartzMap.pderivCLM ℂ v u)).toLp 2 volume) =
      fourierMultiplier (regularizedDirectionSymbol v)
        (symbolCLM (physicalCoefficient a) (u.toLp 2 volume)) -
      fourierMultiplier besselSymbol ((coeffMul (coefficientPDeriv a v) u).toLp 2 volume) := by
  let L := (fourierMultiplier besselSymbol).comp (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space))
  have h := congrArg L (pderiv_coeffMul a u v)
  rw [map_add] at h
  simp only [L, ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply] at h
  rw [besselLp_pderiv, coeffMul_toLp] at h
  exact eq_sub_of_add_eq h.symm

theorem bessel_small_outside_ball (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ ξ : Space, ξ ∉ Metric.closedBall 0 R → ‖bessel ξ‖ ≤ ε := by
  let R := (2 * Real.pi * ε)⁻¹
  refine ⟨R, fun ξ hξ => ?_⟩
  have hR : R < ‖ξ‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hξ
  have h2 : 1 < ‖ξ‖ * (2 * Real.pi * ε) := by
    apply (div_lt_iff₀ (mul_pos twoPi_pos hε)).mp
    simpa only [one_div] using hR
  rw [bessel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    ← one_div]
  apply (div_le_iff₀ (frequencyWeight_root_pos ξ)).mpr
  have h := mul_le_mul_of_nonneg_left (radial_le_frequencyWeight_root ξ) hε.le
  linarith [show ‖ξ‖ * (2 * Real.pi * ε) = ε * (2 * Real.pi * ‖ξ‖) by ring]

/-- The vanishing-frequency multiplier still tends strongly to zero after a
fixed real compact coefficient on the original localized sequence. -/
theorem vanishingFrequency_after_coefficient_tendsto_zero
    (q : BoundedSymbol Space)
    (hq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ ξ, ξ ∉ Metric.closedBall (0 : Space) R → ‖q ξ‖ ≤ ε)
    (a : D) (f : ℕ → Space → ℝ) (hs : ∀ k, ContDiff ℝ ∞ (f k))
    (hf : ∀ k, MemLp (f k) 2 (volume : Measure Space))
    (χ0 : D) (hχ0 : ∀ k x, f k x ≠ 0 → (χ0 : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ k, ‖(hf k).toLp (f k)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun k => ∫ x, f k x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun k => fourierMultiplier q
      (symbolCLM (physicalCoefficient a) ((sourceSchwartz (hs k) χ0 (hχ0 k)).toLp 2 volume)))
      atTop (𝓝 0) := by
  let g (k : ℕ) (x : Space) := (a : Space → ℝ) x * f k x
  let C := (physicalCoefficient a).bound
  have hC : 0 ≤ C := (physicalCoefficient a).bound_nonneg
  have hgs (k : ℕ) : ContDiff ℝ ∞ (g k) := (test_smooth a).mul (hs k)
  have hpoint (k : ℕ) (x : Space) : ‖g k x‖ ≤ C * ‖f k x‖ := by
    rw [show g k x = (a : Space → ℝ) x * f k x from rfl, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have ha := (physicalCoefficient a).norm_le x
    change ‖((a : Space → ℝ) x : ℂ)‖ ≤ C at ha
    simpa only [Complex.norm_real] using ha
  have hg (k : ℕ) : MemLp (g k) 2 volume :=
    (hf k).of_le_mul (hgs k).continuous.aestronglyMeasurable (Eventually.of_forall (hpoint k))
  have hBg (k : ℕ) : ‖(hg k).toLp (g k)‖ ≤ C * B := by
    have hscaled := (hf k).const_smul C
    have hle : ‖(hg k).toLp (g k)‖ ≤ ‖hscaled.toLp (C • f k)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(hg k).coeFn_toLp, hscaled.coeFn_toLp] with x hx hy
      rw [hx, hy]
      simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using hpoint k x
    change ‖(hg k).toLp (g k)‖ ≤ ‖C • (hf k).toLp (f k)‖ at hle
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] at hle
    exact hle.trans (mul_le_mul_of_nonneg_left (hB k) hC)
  have hcut (k : ℕ) (x : Space) (hx : g k x ≠ 0) : (χ0 : Space → ℝ) x = 1 :=
    hχ0 k x (mul_ne_zero_iff.mp hx).2
  have hgt : ∀ φ : D, Tendsto (fun k => ∫ x, g k x * (φ : Space → ℝ) x) atTop (𝓝 0) :=
    fixedRealWeight_preserves_test_limits (a : Space → ℝ) (test_smooth a) (test_compactSupport a) f ht
  have heq (k : ℕ) : sourceSchwartz (hgs k) χ0 (hcut k) =
      coeffMul a (sourceSchwartz (hs k) χ0 (hχ0 k)) := by
    apply SchwartzMap.ext
    intro x
    exact Complex.ofReal_mul _ _
  have hout := vanishingFrequency_tendsto_zero_of_localized_weak_zero q hq
    g hgs hg χ0 hcut (C * B) hBg hgt
  simpa only [heq, coeffMul_toLp] using hout

set_option maxHeartbeats 1000000 in
/-- The localized first-order operator and its actual principal symbol give
the same strong limit after applying the pinned inverse Bessel operator. -/
theorem bessel_coeffMul_pderiv_minus_principal_tendsto_zero
    (a : D) (v : Space) (f : ℕ → Space → ℝ) (hs : ∀ k, ContDiff ℝ ∞ (f k))
    (hf : ∀ k, MemLp (f k) 2 (volume : Measure Space))
    (χ0 : D) (hχ0 : ∀ k x, f k x ≠ 0 → (χ0 : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ k, ‖(hf k).toLp (f k)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun k => ∫ x, f k x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun k => fourierMultiplier besselSymbol
      ((coeffMul a (SchwartzMap.pderivCLM ℂ v (sourceSchwartz (hs k) χ0 (hχ0 k)))).toLp 2 volume) -
      symbolCLM (physicalCoefficient a) (fourierMultiplier (angularDirectionSymbol v)
        ((sourceSchwartz (hs k) χ0 (hχ0 k)).toLp 2 volume))) atTop (𝓝 0) := by
  let S (k : ℕ) := sourceSchwartz (hs k) χ0 (hχ0 k)
  let L (k : ℕ) := (S k).toLp 2 volume
  let m := angularDirectionSymbol v
  let c := physicalCoefficient a
  let db := physicalCoefficient (coefficientPDeriv a v)
  let r := regularizedDirectionSymbol v
  have hrest := vanishingFrequency_after_coefficient_tendsto_zero (symbolDifference r m)
    (fun ε hε => directionRemainder_small_outside_ball v ε hε) a f hs hf χ0 hχ0 B hB ht
  have hlow := vanishingFrequency_after_coefficient_tendsto_zero besselSymbol bessel_small_outside_ball
    (coefficientPDeriv a v) f hs hf χ0 hχ0 B hB ht
  have hcomm := cutoffCommutator_tendsto_zero_of_localized_weak_zero m c
    (angularDirection_contDiffOn v) (angularDirection_degreeZero v)
    (Complex.ofRealCLM.contDiff.comp (test_smooth a))
    ((test_compactSupport a).comp_left Complex.ofReal_zero) f hs hf χ0 hχ0 B hB ht
  have hsplit (k : ℕ) :
      fourierMultiplier besselSymbol ((coeffMul a (SchwartzMap.pderivCLM ℂ v (S k))).toLp 2 volume) -
        symbolCLM c (fourierMultiplier m (L k)) =
      fourierMultiplier (symbolDifference r m) (symbolCLM c (L k)) +
        cutoffCommutator m c (L k) - fourierMultiplier besselSymbol (symbolCLM db (L k)) := by
    have hv := besselLp_coeffMul_pderiv a (S k) v
    rw [coeffMul_toLp (coefficientPDeriv a v) (S k)] at hv
    change fourierMultiplier besselSymbol ((coeffMul a (SchwartzMap.pderivCLM ℂ v (S k))).toLp 2 volume) =
      fourierMultiplier r (symbolCLM c (L k)) - fourierMultiplier besselSymbol (symbolCLM db (L k)) at hv
    rw [hv, fourierMultiplier_symbolDifference r m (symbolCLM c (L k))]
    simp only [cutoffCommutator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    change fourierMultiplier r (symbolCLM c (L k)) - fourierMultiplier besselSymbol (symbolCLM db (L k)) -
      symbolCLM c (fourierMultiplier m (L k)) = _
    abel
  change Tendsto (fun k => fourierMultiplier besselSymbol
    ((coeffMul a (SchwartzMap.pderivCLM ℂ v (S k))).toLp 2 volume) -
    symbolCLM c (fourierMultiplier m (L k))) atTop (𝓝 0)
  simp_rw [hsplit]
  simpa only [add_zero, sub_zero] using (hrest.add hcomm).sub hlow

end Burnett.Microlocal.BesselLocalization

namespace Burnett.Microlocal.BesselLocalization

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.HminusWeightedDual
open Burnett.X02.SobolevTestJet Burnett.Analysis.LocalHminusFourier
open scoped ContDiff Topology BigOperators

variable {ι κ η : Type*} [Fintype ι] [Fintype η]

/-- A row of an actual first-order system on the component fields. -/
def firstOrderRow (a : ι → D) (v : ι → Space) (i : ι → κ) (b : η → D) (j : η → κ)
    (u : κ → SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  (∑ h, coeffMul (a h) (SchwartzMap.pderivCLM ℂ (v h) (u (i h)))) +
    ∑ h, coeffMul (b h) (u (j h))

omit [Fintype η] in
def rowPrincipal (a : ι → D) (v : ι → Space) (i : ι → κ) (u : κ → SchwartzMap Space ℂ) :
    ComplexL2 Space :=
  ∑ h, symbolCLM (physicalCoefficient (a h))
    (fourierMultiplier (angularDirectionSymbol (v h)) ((u (i h)).toLp 2 volume))

/-- The first-order row after inverse Bessel regularization and its
homogeneous principal action differ by a strongly null error. -/
theorem bessel_firstOrderRow_minus_principal_tendsto_zero
    (a : ι → D) (v : ι → Space) (i : ι → κ) (b : η → D) (j : η → κ)
    (f : ℕ → κ → Space → ℝ) (hs : ∀ k c, ContDiff ℝ ∞ (f k c))
    (hf : ∀ k c, MemLp (f k c) 2 (volume : Measure Space))
    (χ0 : D) (hχ0 : ∀ k c x, f k c x ≠ 0 → (χ0 : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ k c, ‖(hf k c).toLp (f k c)‖ ≤ B)
    (ht : ∀ (c : κ) (φ : D), Tendsto (fun k => ∫ x, f k c x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    let u := fun k c => sourceSchwartz (hs k c) χ0 (hχ0 k c)
    Tendsto (fun k => fourierMultiplier besselSymbol ((firstOrderRow a v i b j (u k)).toLp 2 volume) -
      rowPrincipal a v i (u k)) atTop (𝓝 0) := by
  let u (k : ℕ) (c : κ) := sourceSchwartz (hs k c) χ0 (hχ0 k c)
  let T := (fourierMultiplier besselSymbol).comp (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space))
  let err (k : ℕ) (h : ι) :=
    T (coeffMul (a h) (SchwartzMap.pderivCLM ℂ (v h) (u k (i h)))) -
    symbolCLM (physicalCoefficient (a h)) (fourierMultiplier (angularDirectionSymbol (v h))
      ((u k (i h)).toLp 2 volume))
  let lower (k : ℕ) (h : η) := T (coeffMul (b h) (u k (j h)))
  have hErr (h : ι) : Tendsto (fun k => err k h) atTop (𝓝 0) :=
    bessel_coeffMul_pderiv_minus_principal_tendsto_zero (a h) (v h) (fun k => f k (i h))
      (fun k => hs k (i h)) (fun k => hf k (i h)) χ0 (fun k => hχ0 k (i h))
      B (fun k => hB k (i h)) (ht (i h))
  have hLower (h : η) : Tendsto (fun k => lower k h) atTop (𝓝 0) := by
    simp only [lower, T, ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply, coeffMul_toLp]
    exact vanishingFrequency_after_coefficient_tendsto_zero besselSymbol bessel_small_outside_ball
      (b h) (fun k => f k (j h)) (fun k => hs k (j h)) (fun k => hf k (j h))
      χ0 (fun k => hχ0 k (j h)) B (fun k => hB k (j h)) (ht (j h))
  have hsplit (k : ℕ) : T (firstOrderRow a v i b j (u k)) - rowPrincipal a v i (u k) =
      (∑ h, err k h) + ∑ h, lower k h := by
    simp only [firstOrderRow, rowPrincipal, err, lower, map_add, map_sum, Finset.sum_sub_distrib]
    abel
  change Tendsto (fun k => T (firstOrderRow a v i b j (u k)) - rowPrincipal a v i (u k))
    atTop (𝓝 0)
  simp_rw [hsplit]
  simpa only [Finset.sum_const_zero, add_zero] using
    (tendsto_finset_sum Finset.univ (fun h _ => hErr h)).add
      (tendsto_finset_sum Finset.univ (fun h _ => hLower h))

/-- Strong vanishing in the pinned Fourier negative energy for the actual
first-order row gives strong vanishing of its principal action. -/
theorem rowPrincipal_tendsto_zero_of_negativeEnergy_tendsto_zero
    (a : ι → D) (v : ι → Space) (i : ι → κ) (b : η → D) (j : η → κ)
    (f : ℕ → κ → Space → ℝ) (hs : ∀ k c, ContDiff ℝ ∞ (f k c))
    (hf : ∀ k c, MemLp (f k c) 2 (volume : Measure Space))
    (χ0 : D) (hχ0 : ∀ k c x, f k c x ≠ 0 → (χ0 : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ k c, ‖(hf k c).toLp (f k c)‖ ≤ B)
    (ht : ∀ (c : κ) (φ : D), Tendsto (fun k => ∫ x, f k c x * (φ : Space → ℝ) x) atTop (𝓝 0))
    (hA : Tendsto (fun k => negativeEnergy
      (firstOrderRow a v i b j (fun c => sourceSchwartz (hs k c) χ0 (hχ0 k c)))) atTop (𝓝 0)) :
    Tendsto (fun k => rowPrincipal a v i (fun c => sourceSchwartz (hs k c) χ0 (hχ0 k c))) atTop (𝓝 0) := by
  let U (k : ℕ) (c : κ) := sourceSchwartz (hs k c) χ0 (hχ0 k c)
  let V (k : ℕ) := firstOrderRow a v i b j (U k)
  have hnorm (k : ℕ) :
      ‖fourierMultiplier besselSymbol ((V k).toLp 2 volume)‖ = Real.sqrt (negativeEnergy (V k)) := by
    rw [← besselLp_norm_sq_eq_negativeEnergy, Real.sqrt_sq (norm_nonneg _)]
  have hb : Tendsto (fun k => fourierMultiplier besselSymbol ((V k).toLp 2 volume)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [hnorm]
    simpa only [Function.comp_apply, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hA
  have he := bessel_firstOrderRow_minus_principal_tendsto_zero a v i b j f hs hf χ0 hχ0 B hB ht
  simpa only [V, U, sub_sub_cancel, sub_zero] using hb.sub he

end Burnett.Microlocal.BesselLocalization
