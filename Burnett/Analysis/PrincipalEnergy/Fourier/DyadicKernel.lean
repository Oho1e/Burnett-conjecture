import Burnett.Analysis.Microlocal.AngularCommutator.Infrared
import Burnett.Analysis.PrincipalEnergy.Fourier.SymbolProduct
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularDyadicKernel

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open scoped ContDiff FourierTransform InnerProduct Topology BigOperators

abbrev E := EuclideanSpace ℝ (Fin 4)

/-- A fixed radial cutoff, equal to one on the unit ball and zero outside the
ball of radius two. -/
def radialCore (x : E) : ℝ :=
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 4, by norm_num, by norm_num⟩
  bump (‖x‖ ^ 2)

theorem radialCore_contDiff : ContDiff ℝ ∞ radialCore := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 4, by norm_num, by norm_num⟩
  change ContDiff ℝ ∞ ((bump : ℝ → ℝ) ∘ fun x : E => ‖x‖ ^ 2)
  apply bump.contDiff.comp
  simp only [← real_inner_self_eq_norm_sq]
  exact ContDiff.inner ℝ contDiff_id contDiff_id

theorem radialCore_nonneg (x : E) : 0 ≤ radialCore x :=
  ContDiffBump.nonneg' _ _

theorem radialCore_le_one (x : E) : radialCore x ≤ 1 :=
  ContDiffBump.le_one _

theorem radialCore_eq_one (x : E) (hx : ‖x‖ ≤ 1) : radialCore x = 1 := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 4, by norm_num, by norm_num⟩
  change bump (‖x‖ ^ 2) = 1
  apply bump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_of_nonneg (sq_nonneg _)]
  change ‖x‖ ^ 2 ≤ (1 : ℝ)
  exact (pow_le_pow_left₀ (norm_nonneg _) hx 2).trans_eq (one_pow 2)

theorem radialCore_eq_zero (x : E) (hx : 2 ≤ ‖x‖) : radialCore x = 0 := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 4, by norm_num, by norm_num⟩
  change bump (‖x‖ ^ 2) = 0
  apply bump.zero_of_le_dist
  rw [dist_zero_right, Real.norm_of_nonneg (sq_nonneg _)]
  change (4 : ℝ) ≤ ‖x‖ ^ 2
  exact (by norm_num : (4 : ℝ) = 2 ^ 2).trans_le (pow_le_pow_left₀ (by norm_num) hx 2)

/-- The actual radial annular cutoff for the dyadic decomposition. -/
def annulus (x : E) : ℝ := radialCore ((1 / 2 : ℝ) • x) - radialCore x

theorem annulus_contDiff : ContDiff ℝ ∞ annulus :=
  (radialCore_contDiff.comp (contDiff_const.smul contDiff_id)).sub radialCore_contDiff

theorem annulus_radial {x y : E} (h : ‖x‖ = ‖y‖) : annulus x = annulus y := by
  unfold annulus radialCore
  rw [norm_smul, norm_smul, h]

theorem annulus_eq_zero_near (x : E) (hx : ‖x‖ ≤ 1) : annulus x = 0 := by
  have hhalf : ‖(1 / 2 : ℝ) • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
    linarith
  rw [annulus, radialCore_eq_one x hx, radialCore_eq_one _ hhalf, sub_self]

theorem annulus_eq_zero_far (x : E) (hx : 4 ≤ ‖x‖) : annulus x = 0 := by
  have hhalf : 2 ≤ ‖(1 / 2 : ℝ) • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
    linarith
  rw [annulus, radialCore_eq_zero x (by linarith), radialCore_eq_zero _ hhalf, sub_self]

/-- The genuine annular multiplier symbol, using the same bounded angular
symbol consumed by the F05 Fourier multiplier. -/
def annularSymbol (m : BoundedSymbol E) (ξ : E) : ℂ := (annulus ξ : ℂ) * m ξ

theorem annularSymbol_hasCompactSupport (m : BoundedSymbol E) : HasCompactSupport (annularSymbol m) := by
  have h : tsupport (annularSymbol m) ⊆ Metric.closedBall (0 : E) 4 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra hxB
    have hx' : 4 < ‖x‖ := lt_of_not_ge (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hxB)
    exact hx (by simp [annularSymbol, annulus_eq_zero_far _ hx'.le])
  exact (isCompact_closedBall (0 : E) 4).of_isClosed_subset isClosed_closure h

theorem annularSymbol_contDiff (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    ContDiff ℝ ∞ (annularSymbol m) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : E) zero_lt_one] with y hy
    have hy' : ‖y‖ ≤ 1 := (by
      simpa only [Metric.mem_ball, dist_zero_right] using hy : ‖y‖ < 1).le
    simp [annularSymbol, annulus_eq_zero_near y hy']
  · exact ((Complex.ofRealCLM.contDiff.comp annulus_contDiff).contDiffAt).mul
      (hm.contDiffAt (isOpen_compl_singleton.mem_nhds hx))

def annularSchwartz (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) : SchwartzMap E ℂ :=
  (annularSymbol_hasCompactSupport m).toSchwartzMap (annularSymbol_contDiff m hm)

/-- The one fixed inverse-Fourier Schwartz profile for all scaled shells. -/
def inverseAnnularSchwartz (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) : SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm (annularSchwartz m hm)

theorem inverseAnnularSchwartz_apply (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (z : E) :
    inverseAnnularSchwartz m hm z = 𝓕⁻ (annularSymbol m) z := by
  rw [inverseAnnularSchwartz, SchwartzMap.fourierTransformCLE_symm_apply]
  rfl

/-- The finite dyadic sum is the difference of the original core cutoff and
the same core cutoff at the outermost scale, multiplied by the original
homogeneous angular symbol. -/
theorem sum_range_annularSymbol (m : BoundedSymbol E) (hd : DegreeZero (m : E → ℂ))
    (N : ℕ) (ξ : E) :
    (∑ j ∈ Finset.range N, annularSymbol m (((2 : ℝ) ^ j)⁻¹ • ξ)) =
      ((radialCore (((2 : ℝ) ^ N)⁻¹ • ξ) - radialCore ξ : ℝ) : ℂ) * m ξ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, annularSymbol, annulus]
    have hscale : (1 / 2 : ℝ) • (((2 : ℝ) ^ N)⁻¹ • ξ) = ((2 : ℝ) ^ (N+1))⁻¹ • ξ := by
      rw [smul_smul, pow_succ]
      congr 1
      field_simp
    rw [hscale, hd _ (by positivity : 0 < ((2 : ℝ) ^ N)⁻¹)]
    push_cast
    ring

end Burnett.Microlocal.AngularDyadicKernel

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularDyadicKernel

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.AngularCommutator (DegreeZero symbolDifference)
open Burnett.Microlocal.SeparablePositive (productSymbol)
open scoped ContDiff FourierTransform InnerProduct Topology BigOperators ENNReal

def dyadicScale (j : ℕ) : ℝ := (2 : ℝ) ^ j

private theorem dyadicScale_pos (j : ℕ) : 0 < dyadicScale j := by
  unfold dyadicScale
  positivity

/-- With the actual Lebesgue normalization, dilating an inverse Fourier
argument on frequency introduces precisely the fourth power of the scale. -/
theorem inverseFourier_dilation (s : ℝ) (hs : 0 < s) (f : E → ℂ) (z : E) :
    𝓕⁻ (fun ξ => f (s⁻¹ • ξ)) z = s ^ 4 • 𝓕⁻ f (s • z) := by
  let g (y : E) := (Real.fourierChar (inner ℝ y (s • z))) • f y
  have hInner (ξ : E) : inner ℝ (s⁻¹ • ξ) (s • z) = inner ℝ ξ z := by
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
      inv_mul_cancel₀ hs.ne', one_mul]
  have hL : 𝓕⁻ (fun ξ => f (s⁻¹ • ξ)) z = ∫ x, g (s⁻¹ • x) := by
    rw [Real.fourierIntegralInv_eq]
    simp only [g, hInner]
  rw [hL, Real.fourierIntegralInv_eq]
  let e : E ≃ₜ E := Homeomorph.smulOfNeZero _ (inv_ne_zero hs.ne')
  change (∫ x, g (e.toMeasurableEquiv x)) = s ^ 4 • ∫ x, g x
  rw [← integral_map_equiv e.toMeasurableEquiv]
  change (∫ x, g x ∂Measure.map (fun x : E => s⁻¹ • x) volume) = _
  rw [Measure.map_addHaar_smul (volume : Measure E) (inv_ne_zero hs.ne'),
    finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hs.le _),
    integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg hs.le _)]

/-- Every annular inverse transform uses the same Schwartz profile. -/
def shellKernel (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) (z : E) : ℂ :=
  dyadicScale j ^ 4 • inverseAnnularSchwartz m hm (dyadicScale j • z)

theorem shellKernel_eq_inverseFourier (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) (z : E) :
    shellKernel m hm j z = 𝓕⁻ (fun ξ => annularSymbol m ((dyadicScale j)⁻¹ • ξ)) z := by
  rw [inverseFourier_dilation _ (dyadicScale_pos j), shellKernel, inverseAnnularSchwartz_apply]

theorem shellKernel_hasFDerivAt (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) (z : E) :
    HasFDerivAt (shellKernel m hm j)
      (dyadicScale j ^ 5 •
        fderiv ℝ (inverseAnnularSchwartz m hm : E → ℂ) (dyadicScale j • z)) z := by
  let g := inverseAnnularSchwartz m hm
  let s := dyadicScale j
  let A : E →L[ℝ] E := s • ContinuousLinearMap.id ℝ E
  have hA : HasFDerivAt (fun x : E => s • x) A z := A.hasFDerivAt
  have hg : Differentiable ℝ (g : E → ℂ) := g.smooth'.differentiable (by simp)
  have hDeriv := ((hg (s • z)).hasFDerivAt.comp z hA).const_smul (s ^ 4)
  change HasFDerivAt (fun x : E => s ^ 4 • g (s • x))
    (s ^ 4 • (fderiv ℝ (g : E → ℂ) (s • z)).comp A) z at hDeriv
  simpa only [A, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, smul_smul,
    ← pow_succ] using hDeriv

def boundedRadialCore (s : ℝ) : BoundedSymbol E where
  toFun x := (radialCore (s • x) : ℂ)
  measurable := (Complex.continuous_ofReal.comp
    (radialCore_contDiff.continuous.comp (continuous_const.smul continuous_id))).aestronglyMeasurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x := by
    rw [Complex.norm_real, Real.norm_of_nonneg (radialCore_nonneg _)]
    exact radialCore_le_one _

private def unitSymbol : BoundedSymbol E where
  toFun := fun _ => 1
  measurable := aestronglyMeasurable_const
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by simp

/-- The original angular multiplier with one fixed smooth infrared cutoff. -/
def normalizedAngularSymbol (m : BoundedSymbol E) : BoundedSymbol E :=
  productSymbol (symbolDifference unitSymbol (boundedRadialCore 1)) m

def partialAngularSymbol (m : BoundedSymbol E) (N : ℕ) : BoundedSymbol E :=
  productSymbol (symbolDifference (boundedRadialCore (dyadicScale N)⁻¹) (boundedRadialCore 1)) m

theorem partialAngularSymbol_apply_sum (m : BoundedSymbol E) (hd : DegreeZero (m : E → ℂ))
    (N : ℕ) (ξ : E) :
    partialAngularSymbol m N ξ =
      ∑ j ∈ Finset.range N, annularSymbol m ((dyadicScale j)⁻¹ • ξ) := by
  change partialAngularSymbol m N ξ = ∑ j ∈ Finset.range N, annularSymbol m (((2 : ℝ)^j)⁻¹ • ξ)
  rw [sum_range_annularSymbol m hd]
  change ((radialCore ((dyadicScale N)⁻¹ • ξ) : ℂ) - (radialCore ((1 : ℝ) • ξ) : ℂ)) * m ξ =
    ((radialCore (((2 : ℝ) ^ N)⁻¹ • ξ) - radialCore ξ : ℝ) : ℂ) * m ξ
  rw [one_smul, Complex.ofReal_sub]
  rfl

theorem partialAngularSymbol_eventually_eq (m : BoundedSymbol E) (ξ : E) :
    (fun N => partialAngularSymbol m N ξ) =ᶠ[atTop] (fun _ => normalizedAngularSymbol m ξ) := by
  have hLarge : ∀ᶠ N : ℕ in atTop, ‖ξ‖ ≤ (2 : ℝ) ^ N :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
      (eventually_ge_atTop ‖ξ‖)
  filter_upwards [hLarge] with N hN
  have hnorm : ‖(dyadicScale N)⁻¹ • ξ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (dyadicScale_pos N).le)]
    calc
      (dyadicScale N)⁻¹ * ‖ξ‖ ≤ (dyadicScale N)⁻¹ * dyadicScale N :=
        mul_le_mul_of_nonneg_left hN (inv_nonneg.mpr (dyadicScale_pos N).le)
      _ = 1 := inv_mul_cancel₀ (dyadicScale_pos N).ne'
  change ((radialCore ((dyadicScale N)⁻¹ • ξ) : ℂ) - (radialCore ((1 : ℝ) • ξ) : ℂ)) * m ξ =
    (1 - (radialCore ((1 : ℝ) • ξ) : ℂ)) * m ξ
  rw [radialCore_eq_one _ hnorm, Complex.ofReal_one]

end Burnett.Microlocal.AngularDyadicKernel

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularDyadicKernel

open Filter Finset
open scoped Topology BigOperators

private theorem scale_pos (j : ℕ) : 0 < dyadicScale j := by
  unfold dyadicScale
  positivity

private theorem first_large_scale_exists (r : ℝ) (hr : 0 < r) :
    ∃ J : ℕ, 1 ≤ dyadicScale J * r := by
  have h : ∀ᶠ J : ℕ in atTop, r⁻¹ ≤ (2 : ℝ) ^ J :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
      (eventually_ge_atTop r⁻¹)
  obtain ⟨J, hJ⟩ := eventually_atTop.1 h
  refine ⟨J, ?_⟩
  calc
    1 = r⁻¹ * r := (inv_mul_cancel₀ hr.ne').symm
    _ ≤ dyadicScale J * r := mul_le_mul_of_nonneg_right (hJ J le_rfl) hr.le

private theorem geometric_mass (C : ℝ) :
    (Summable fun j : ℕ => C * ((1 / 2 : ℝ) ^ j)) ∧
      (∑' j : ℕ, C * ((1 / 2 : ℝ) ^ j)) = C * 2 := by
  have h : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  refine ⟨(summable_geometric_of_norm_lt_one h).mul_left C, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one h]
  norm_num

/-- A four-dimensional kernel or its first derivative uses this estimate
with exponent four or five. The proof splits at the first scale with
positive scaled radius at least one. -/
theorem normalizedDyadicSeries_le (d : ℕ) (hd : 0 < d) (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hLow : ∀ j, a j ≤ C * (dyadicScale j * r) ^ d)
    (hHigh : ∀ j, a j ≤ C / (dyadicScale j * r)) :
    Summable a ∧ (∑' j, a j) ≤ C * ((2 : ℝ) ^ d + 2) := by
  have hTop (j : ℕ) : a j ≤ (C / r) * (1 / 2 : ℝ) ^ j := by
    refine (hHigh j).trans_eq ?_
    unfold dyadicScale
    rw [div_eq_mul_inv, div_eq_mul_inv, one_div, inv_pow]
    field_simp
  have hSum : Summable a := Summable.of_nonneg_of_le ha hTop (geometric_mass (C / r)).1
  refine ⟨hSum, ?_⟩
  let hExists := first_large_scale_exists r hr
  let J := Nat.find hExists
  have hJ : 1 ≤ dyadicScale J * r := Nat.find_spec hExists
  have hLowSum : (∑ j ∈ range J, a j) ≤ C * (2 : ℝ) ^ d := by
    by_cases hj : J = 0
    · simp only [hj, range_zero, sum_empty]
      positivity
    · have hPrev := Nat.find_min hExists (show J - 1 < J by omega)
      have hUpper : dyadicScale J * r ≤ 2 := by
        change (2 : ℝ) ^ J * r ≤ 2
        conv_lhs => rw [show J = (J - 1) + 1 by omega, pow_succ]
        have hlt : (2 : ℝ) ^ (J - 1) * r < 1 := lt_of_not_ge hPrev
        linarith
      let b := (2 : ℝ) ^ d
      have hb : 2 ≤ b := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ d by omega))
      have hGeom : (∑ j ∈ range J, b ^ j) ≤ b ^ J := by
        have h := geom_sum_mul b J
        have hn : 0 ≤ ∑ j ∈ range J, b ^ j :=
          Finset.sum_nonneg fun i _ => pow_nonneg (by linarith) i
        have hx := mul_nonneg hn (show 0 ≤ b - 2 by linarith)
        nlinarith
      have hEq (j : ℕ) : (dyadicScale j * r) ^ d = r ^ d * b ^ j := by
        simp only [dyadicScale, b, mul_pow, ← pow_mul]
        rw [Nat.mul_comm j d, mul_comm]
      calc
        _ ≤ ∑ j ∈ range J, C * (dyadicScale j * r) ^ d :=
          Finset.sum_le_sum fun j _ => hLow j
        _ = (C * r ^ d) * ∑ j ∈ range J, b ^ j := by
          simp only [hEq, Finset.mul_sum, mul_assoc]
        _ ≤ (C * r ^ d) * b ^ J := mul_le_mul_of_nonneg_left hGeom (by positivity)
        _ = C * (dyadicScale J * r) ^ d := by rw [hEq, mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by unfold dyadicScale; positivity) hUpper d) hC
  have hTailBound (j : ℕ) : a (j + J) ≤ C * (1 / 2 : ℝ) ^ j := by
    refine (hHigh (j+J)).trans ?_
    have hDen : dyadicScale j ≤ dyadicScale (j+J) * r := by
      change (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (j+J) * r
      rw [pow_add, mul_assoc]
      exact le_mul_of_one_le_right (by positivity) hJ
    calc
      C / (dyadicScale (j+J) * r) ≤ C / dyadicScale j :=
        div_le_div_of_nonneg_left hC (scale_pos j) hDen
      _ = _ := by rw [div_eq_mul_inv, one_div, inv_pow]; rfl
  have hTailSum : Summable (fun j => a (j + J)) :=
    Summable.of_nonneg_of_le (fun j => ha (j+J)) hTailBound (geometric_mass C).1
  have hHighSum := hTailSum.tsum_le_tsum hTailBound (geometric_mass C).1
  rw [(geometric_mass C).2] at hHighSum
  rw [← hSum.sum_add_tsum_nat_add J, mul_add]
  exact add_le_add hLowSum hHighSum

end Burnett.Microlocal.AngularDyadicKernel

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularDyadicKernel

open MeasureTheory Filter Set Burnett.Fourier
open scoped ContDiff FourierTransform InnerProduct Topology BigOperators

private theorem schwartz_scale_pos (j : ℕ) : 0 < dyadicScale j := by
  unfold dyadicScale
  positivity

section GenericProfile

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem scaledSchwartz_high_bound (p : SchwartzMap E F) (d j : ℕ) (z : E) (hz : z ≠ 0) :
    ‖dyadicScale j ^ d • p (dyadicScale j • z)‖ ≤
      SchwartzMap.seminorm ℝ (d+1) 0 p * (dyadicScale j)⁻¹ * (‖z‖ ^ (d+1))⁻¹ := by
  let s := dyadicScale j
  let r := ‖z‖
  let C := SchwartzMap.seminorm ℝ (d+1) 0 p
  have hs : 0 < s := schwartz_scale_pos j
  have hr : 0 < r := norm_pos_iff.mpr hz
  have hnorm : ‖s • z‖ = s * r := by
    rw [norm_smul, Real.norm_of_nonneg hs.le]
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ p (d+1) (s • z)
  rw [hnorm] at h
  have h₁ : ‖p (s • z)‖ ≤ C / (s*r)^(d+1) :=
    (le_div_iff₀ (pow_pos (mul_pos hs hr) _)).mpr (by rwa [mul_comm])
  change ‖s ^ d • p (s • z)‖ ≤ C * s⁻¹ * (r ^ (d+1))⁻¹
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hs.le _)]
  calc
    s ^ d * ‖p (s • z)‖ ≤ s ^ d * (C / (s*r)^(d+1)) :=
      mul_le_mul_of_nonneg_left h₁ (pow_nonneg hs.le _)
    _ = _ := by
      rw [mul_pow, pow_succ s]
      field_simp [hs.ne', hr.ne', pow_ne_zero d hs.ne',
        pow_ne_zero (d+1) hr.ne']

/-- A fixed Schwartz profile gives an absolutely summable dilated kernel
with the sharp inverse power in the nonzero spatial argument. -/
theorem scaledSchwartz_absoluteSum_le (p : SchwartzMap E F) (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ≠ 0,
      Summable (fun j => ‖dyadicScale j ^ d • p (dyadicScale j • z)‖) ∧
      (∑' j, ‖dyadicScale j ^ d • p (dyadicScale j • z)‖) ≤ C * (‖z‖ ^ d)⁻¹ := by
  let M := max (SchwartzMap.seminorm ℝ 0 0 p) (SchwartzMap.seminorm ℝ (d+1) 0 p)
  have hM : 0 ≤ M := (apply_nonneg _ _).trans (le_max_left _ _)
  refine ⟨M * ((2 : ℝ)^d + 2), by positivity, ?_⟩
  intro z hz
  let r := ‖z‖
  let b (j : ℕ) := ‖dyadicScale j ^ d • p (dyadicScale j • z)‖
  let a (j : ℕ) := r ^ d * b j
  have hr : 0 < r := norm_pos_iff.mpr hz
  have hrpow : r ^ d ≠ 0 := pow_ne_zero _ hr.ne'
  have hL (j : ℕ) : a j ≤ M * (dyadicScale j * r)^d := by
    unfold a b
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (schwartz_scale_pos j).le _), mul_pow]
    calc
      r^d * (dyadicScale j ^ d * ‖p (dyadicScale j • z)‖) ≤
        r^d * (dyadicScale j ^ d * M) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            ((SchwartzMap.norm_le_seminorm ℝ p _).trans (le_max_left _ _))
            (pow_nonneg (schwartz_scale_pos j).le _)) (pow_nonneg hr.le _)
      _ = _ := by ring
  have hH (j : ℕ) : a j ≤ M / (dyadicScale j*r) := by
    have hs := schwartz_scale_pos j
    calc
      a j ≤ r^d * (SchwartzMap.seminorm ℝ (d+1) 0 p * (dyadicScale j)⁻¹ * (r^(d+1))⁻¹) :=
        mul_le_mul_of_nonneg_left (scaledSchwartz_high_bound p d j z hz) (pow_nonneg hr.le _)
      _ ≤ r^d * (M * (dyadicScale j)⁻¹ * (r^(d+1))⁻¹) := by
        gcongr
        exact le_max_right _ _
      _ = _ := by rw [pow_succ r]; field_simp [hr.ne', hs.ne', hrpow]
  obtain ⟨hSum, hSize⟩ := normalizedDyadicSeries_le d hd r M hr hM a
    (fun j => mul_nonneg (pow_nonneg hr.le _) (norm_nonneg _)) hL hH
  have hu : (fun j => ‖dyadicScale j ^ d • p (dyadicScale j • z)‖) = fun j => (r^d)⁻¹ * a j := by
    funext j
    change b j = (r^d)⁻¹ * (r^d * b j)
    rw [← mul_assoc, inv_mul_cancel₀ hrpow, one_mul]
  rw [hu, tsum_mul_left]
  refine ⟨hSum.mul_left _, ?_⟩
  exact (mul_le_mul_of_nonneg_left hSize (inv_nonneg.mpr (pow_nonneg hr.le _))).trans_eq (mul_comm _ _)

end GenericProfile

/-- The convergent off-diagonal kernel assembled from the actual inverse
Fourier transforms of the annular frequency pieces. -/
def angularKernel (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (z : E) : ℂ :=
  ∑' j, shellKernel m hm j z

theorem angularKernel_size (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ≠ 0,
      Summable (fun j => ‖shellKernel m hm j z‖) ∧
      ‖angularKernel m hm z‖ ≤ C * (‖z‖ ^ 4)⁻¹ := by
  obtain ⟨C, hC, hMain⟩ := scaledSchwartz_absoluteSum_le (inverseAnnularSchwartz m hm) 4 (by decide)
  refine ⟨C, hC, ?_⟩
  intro z hz
  obtain ⟨hSum, hBound⟩ := hMain z hz
  exact ⟨hSum, (norm_tsum_le_tsum_norm hSum).trans hBound⟩

private theorem shellDerivative_geometric_bound (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (r : ℝ) (hr : 0 < r)
    (j : ℕ) (z : E) (hz : r ≤ ‖z‖) :
    ‖dyadicScale j ^ 5 • fderiv ℝ (inverseAnnularSchwartz m hm : E → ℂ) (dyadicScale j • z)‖ ≤
      (SchwartzMap.seminorm ℝ 6 0 (SchwartzMap.fderivCLM ℝ (inverseAnnularSchwartz m hm)) *
        (r ^ 6)⁻¹) * (1 / 2 : ℝ)^j := by
  let p := SchwartzMap.fderivCLM ℝ (inverseAnnularSchwartz m hm)
  have hn : 0 < ‖z‖ := hr.trans_le hz
  have h := scaledSchwartz_high_bound p 5 j z (norm_pos_iff.mp hn)
  rw [SchwartzMap.fderivCLM_apply] at h
  refine h.trans ?_
  change SchwartzMap.seminorm ℝ 6 0 p * (dyadicScale j)⁻¹ * (‖z‖ ^ 6)⁻¹ ≤ _
  rw [dyadicScale, ← inv_pow, ← one_div, mul_assoc]
  have hPowInv : (‖z‖ ^ 6)⁻¹ ≤ (r ^ 6)⁻¹ :=
    (inv_le_inv₀ (pow_pos hn _) (pow_pos hr _)).mpr (pow_le_pow_left₀ hr.le hz _)
  calc
    _ ≤ SchwartzMap.seminorm ℝ 6 0 p * ((1 / 2 : ℝ)^j * (r ^ 6)⁻¹) := by
      gcongr
    _ = _ := by ring

theorem angularKernel_hasFDerivAt_offzero (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (z : E) (hz : z ≠ 0) :
    HasFDerivAt (angularKernel m hm)
      (∑' j, dyadicScale j ^ 5 •
        fderiv ℝ (inverseAnnularSchwartz m hm : E → ℂ) (dyadicScale j • z)) z := by
  let r := ‖z‖ / 2
  let K := Metric.ball z r
  let B := SchwartzMap.seminorm ℝ 6 0
    (SchwartzMap.fderivCLM ℝ (inverseAnnularSchwartz m hm)) * (r ^ 6)⁻¹
  have hr : 0 < r := half_pos (norm_pos_iff.mpr hz)
  have hzK : z ∈ K := Metric.mem_ball_self hr
  have hLower (x : E) (hx : x ∈ K) : r ≤ ‖x‖ := by
    have hdist : ‖x - z‖ < r := by
      simpa only [K, Metric.mem_ball, dist_eq_norm] using hx
    have h := norm_sub_le x (x-z)
    rw [sub_sub_cancel] at h
    dsimp only [r] at *
    linarith
  have hGeo : Summable (fun j : ℕ => B * (1 / 2 : ℝ)^j) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left B
  obtain ⟨C, _, hSize⟩ := angularKernel_size m hm
  exact hasFDerivAt_tsum_of_isPreconnected hGeo Metric.isOpen_ball
    (convex_ball z r).isPreconnected (fun j x _ => shellKernel_hasFDerivAt m hm j x)
    (fun j x hx => shellDerivative_geometric_bound m hm r hr j x (hLower x hx))
    hzK ((hSize z hz).1.of_norm) hzK

theorem angularKernel_derivative_bound (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ≠ 0,
      DifferentiableAt ℝ (angularKernel m hm) z ∧
        ‖fderiv ℝ (angularKernel m hm) z‖ ≤ C * (‖z‖ ^ 5)⁻¹ := by
  let p := SchwartzMap.fderivCLM ℝ (inverseAnnularSchwartz m hm)
  obtain ⟨C, hC, hMain⟩ := scaledSchwartz_absoluteSum_le p 5 (by decide)
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hD := angularKernel_hasFDerivAt_offzero m hm z hz
  obtain ⟨hSum, hB⟩ := hMain z hz
  have hBound := (norm_tsum_le_tsum_norm hSum).trans hB
  refine ⟨hD.differentiableAt, ?_⟩
  rw [hD.fderiv]
  simpa only [p, SchwartzMap.fderivCLM_apply] using hBound

theorem angularKernel_measurable (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    Measurable (angularKernel m hm) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro z hz
  exact (angularKernel_hasFDerivAt_offzero m hm z
    (by simpa only [mem_compl_iff, mem_singleton_iff] using hz)).continuousAt.continuousWithinAt

/-- The same finite annular sum as the exact finite-frequency multiplier. -/
def partialAngularKernel (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (N : ℕ) (z : E) : ℂ :=
  ∑ j ∈ Finset.range N, shellKernel m hm j z

theorem partialAngularKernel_hasFDerivAt (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (N : ℕ) (z : E) :
    HasFDerivAt (partialAngularKernel m hm N)
      (∑ j ∈ Finset.range N, dyadicScale j ^ 5 •
        fderiv ℝ (inverseAnnularSchwartz m hm : E → ℂ) (dyadicScale j • z)) z :=
  HasFDerivAt.fun_sum fun j _ => shellKernel_hasFDerivAt m hm j z

theorem partialAngularKernel_tendsto (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (z : E) (hz : z ≠ 0) :
    Tendsto (fun N => partialAngularKernel m hm N z) atTop (𝓝 (angularKernel m hm z)) := by
  obtain ⟨C, _, h⟩ := angularKernel_size m hm
  exact ((h z hz).1.of_norm.hasSum).tendsto_sum_nat

/-- These off-diagonal bounds are uniform in the exact finite frequency
cutoff. In particular, subtraction can be done before any kernel limit. -/
theorem partialAngularKernel_uniform_bounds (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N z, z ≠ 0 →
      ‖partialAngularKernel m hm N z‖ ≤ C * (‖z‖ ^ 4)⁻¹ ∧
      ‖fderiv ℝ (partialAngularKernel m hm N) z‖ ≤ C * (‖z‖ ^ 5)⁻¹ := by
  let p := inverseAnnularSchwartz m hm
  let dp := SchwartzMap.fderivCLM ℝ p
  obtain ⟨C, hC, hSize⟩ := scaledSchwartz_absoluteSum_le p 4 (by decide)
  obtain ⟨D, hD, hDerivative⟩ := scaledSchwartz_absoluteSum_le dp 5 (by decide)
  refine ⟨max C D, hC.trans (le_max_left _ _), ?_⟩
  intro N z hz
  obtain ⟨hS, hB⟩ := hSize z hz
  obtain ⟨hS', hB'⟩ := hDerivative z hz
  constructor
  · exact (norm_sum_le _ _).trans ((hS.sum_le_tsum _ (fun _ _ => norm_nonneg _)).trans
      (hB.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))))
  · rw [(partialAngularKernel_hasFDerivAt m hm N z).fderiv]
    have hBound : ‖∑ j ∈ Finset.range N, dyadicScale j ^ 5 • dp (dyadicScale j • z)‖ ≤
        D * (‖z‖ ^ 5)⁻¹ :=
      (norm_sum_le _ _).trans ((hS'.sum_le_tsum _ (fun _ _ => norm_nonneg _)).trans hB')
    have hBound' := hBound.trans (mul_le_mul_of_nonneg_right (le_max_right C D) (by positivity))
    simpa only [dp, p, SchwartzMap.fderivCLM_apply] using hBound'

end Burnett.Microlocal.AngularDyadicKernel

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularDyadicKernel

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.AngularCommutator
  (DegreeZero fourier_mul_inverse_eq_integral fourierL2Equiv_symm_eq_inverse_ae_of_integrable)
open scoped FourierTransform InnerProduct ContDiff Topology BigOperators

private def dilationEquiv (s : ℝ) (hs : s ≠ 0) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { toFun := fun x => s • x
      invFun := fun x => s⁻¹ • x
      left_inv := fun _ => by simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]
      right_inv := fun _ => by simp only [smul_smul, mul_inv_cancel₀ hs, one_smul]
      map_add' := smul_add s
      map_smul' := fun r x => smul_comm s r x }
  continuous_toFun := continuous_const.smul continuous_id
  continuous_invFun := continuous_const.smul continuous_id

private def shellFrequencySchwartz (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (dilationEquiv (dyadicScale j)⁻¹ (by unfold dyadicScale; positivity)) (annularSchwartz m hm)

private theorem shellFrequencySchwartz_apply (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) (ξ : E) :
    shellFrequencySchwartz m hm j ξ = annularSymbol m ((dyadicScale j)⁻¹ • ξ) := rfl

/-- The actual finite frequency cutoffs are compact Schwartz symbols. -/
def partialAngularSchwartz (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (N : ℕ) : SchwartzMap E ℂ :=
  ∑ j ∈ Finset.range N, shellFrequencySchwartz m hm j

private theorem schwartz_finset_sum_apply (s : Finset ℕ) (f : ℕ → SchwartzMap E ℂ) (x : E) :
    (∑ j ∈ s, f j) x = ∑ j ∈ s, f j x := by
  let eval : SchwartzMap E ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun g => g x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact map_sum eval f s

theorem partialAngularSchwartz_apply (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (ξ : E) :
    partialAngularSchwartz m hm N ξ = partialAngularSymbol m N ξ := by
  rw [partialAngularSymbol_apply_sum m hd]
  simp only [partialAngularSchwartz, schwartz_finset_sum_apply, shellFrequencySchwartz_apply]

theorem inverseFourier_partialAngular_eq_sum (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (z : E) :
    (𝓕⁻ (partialAngularSymbol m N : E → ℂ)) z =
      ∑ j ∈ Finset.range N, shellKernel m hm j z := by
  have hF : (partialAngularSymbol m N : E → ℂ) = (partialAngularSchwartz m hm N : E → ℂ) :=
    funext fun ξ => (partialAngularSchwartz_apply m hm hd N ξ).symm
  let I : SchwartzMap E ℂ ≃L[ℂ] SchwartzMap E ℂ := SchwartzMap.fourierTransformCLE ℂ
  have hI (g : SchwartzMap E ℂ) : (I.symm g : E → ℂ) = 𝓕⁻ (g : E → ℂ) :=
    SchwartzMap.fourierTransformCLE_symm_apply ℂ g
  rw [hF, ← hI, partialAngularSchwartz, map_sum, schwartz_finset_sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [hI, shellKernel_eq_inverseFourier]
  rfl

/-- An inverse Fourier transform of a frequency product is the genuine
spatial convolution integral, in the exact Fourier convention. -/
theorem inverseFourier_mul_fourier_eq_convolution (p f : E → ℂ)
    (hp : Integrable p (volume : Measure E)) (hf : Integrable f (volume : Measure E)) (x : E) :
    (𝓕⁻ (fun ξ => p ξ * (𝓕 f) ξ)) x = ∫ y, (𝓕⁻ p) (x-y) * f y := by
  let N : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  let F := f ∘ N
  have hF : Integrable F (volume : Measure E) :=
    (N.measurePreserving.integrable_comp_emb N.toHomeomorph.measurableEmbedding).mpr hf
  have hInverse : 𝓕⁻ F = 𝓕 f := by
    funext ξ
    rw [Real.fourierIntegralInv_eq_fourierIntegral_neg]
    change 𝓕 (f ∘ N) (-ξ) = 𝓕 f ξ
    rw [Real.fourierIntegral_comp_linearIsometry]
    simp [N]
  have h := fourier_mul_inverse_eq_integral p F hp hF (-x)
  rw [hInverse] at h
  rw [Real.fourierIntegralInv_eq_fourierIntegral_neg, h]
  have hMap := N.measurePreserving.integral_comp N.toHomeomorph.measurableEmbedding
    (fun y : E => (𝓕 p) (-x-y) * F y)
  change (∫ y : E, (𝓕 p) (-x-N y) * F (N y)) = _ at hMap
  rw [← hMap]
  apply integral_congr_ae
  filter_upwards with y
  have hxy : -x - (-y) = -(x-y) := by abel
  change (𝓕 p) (-x - (-y)) * f (-(-y)) = (𝓕⁻ p) (x-y) * f y
  rw [hxy, neg_neg, Real.fourierIntegralInv_eq_fourierIntegral_neg]

/-- The actual bounded L² multiplier on a Schwartz function agrees with
the pointwise inverse Fourier integral almost everywhere. -/
theorem fourierMultiplier_schwartz_eq_inverse_mul_ae (p : BoundedSymbol E)
    (f : SchwartzMap E ℂ) :
    (fourierMultiplier p (f.toLp 2 volume) : E → ℂ) =ᵐ[volume]
      (𝓕⁻ (fun ξ => p ξ * (𝓕 (f : E → ℂ)) ξ)) := by
  let u := f.toLp 2 volume
  let v := symbolL2 p (fourierL2Equiv u)
  let G (ξ : E) := p ξ * (𝓕 (f : E → ℂ)) ξ
  have hEq : (v : E → ℂ) =ᵐ[volume] G := by
    filter_upwards [symbolL2_ae p (fourierL2Equiv u), fourierL2Equiv_schwartz_ae f] with ξ h₁ h₂
    exact h₁.trans (congrArg (fun z => p ξ * z) h₂)
  have h₂ : MemLp G 2 (volume : Measure E) := (Lp.memLp v).ae_eq hEq
  have hF : Integrable (𝓕 (f : E → ℂ)) (volume : Measure E) :=
    (SchwartzMap.fourierTransformCLE ℂ f).integrable
  have h₁ : Integrable G (volume : Measure E) := hF.bdd_mul p.measurable ⟨p.bound, p.norm_le⟩
  have hv : v = h₂.toLp G := Lp.ext (hEq.trans h₂.coeFn_toLp.symm)
  rw [fourierMultiplier_apply, show symbolL2 p (fourierL2Equiv u) = v from rfl, hv]
  exact fourierL2Equiv_symm_eq_inverse_ae_of_integrable G h₁ h₂

/-- The actual finite-cutoff \(L^2\) operator acts by the finite sum of
the genuine annular inverse-Fourier kernels on a Schwartz input. -/
theorem fourierMultiplier_partialAngular_eq_kernel_ae (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ))
    (N : ℕ) (f : SchwartzMap E ℂ) :
    (fourierMultiplier (partialAngularSymbol m N) (f.toLp 2 volume) : E → ℂ) =ᵐ[volume]
      (fun x => ∫ y, (∑ j ∈ Finset.range N, shellKernel m hm j (x-y)) * f y) := by
  have hP : Integrable (partialAngularSymbol m N : E → ℂ) (volume : Measure E) := by
    rw [show (partialAngularSymbol m N : E → ℂ) = (partialAngularSchwartz m hm N : E → ℂ) from
      funext fun ξ => (partialAngularSchwartz_apply m hm hd N ξ).symm]
    exact (partialAngularSchwartz m hm N).integrable
  filter_upwards [fourierMultiplier_schwartz_eq_inverse_mul_ae (partialAngularSymbol m N) f] with x hx
  rw [hx, inverseFourier_mul_fourier_eq_convolution _ _ hP f.integrable]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change (𝓕⁻ (partialAngularSymbol m N : E → ℂ)) (x-y) * f y = _
    rw [inverseFourier_partialAngular_eq_sum m hm hd N]

end Burnett.Microlocal.AngularDyadicKernel

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularDyadicKernel

open MeasureTheory Filter Set Burnett.Fourier
open scoped Topology ENNReal

private theorem angular_symbol_difference_bound (m : BoundedSymbol E) (N : ℕ) (x : E) :
    ‖partialAngularSymbol m N x - normalizedAngularSymbol m x‖ ≤ 4 * m.bound := by
  have h₁ := (partialAngularSymbol m N).norm_le x
  have h₂ := (normalizedAngularSymbol m).norm_le x
  change ‖partialAngularSymbol m N x‖ ≤ (1+1) * m.bound at h₁
  change ‖normalizedAngularSymbol m x‖ ≤ (1+1) * m.bound at h₂
  exact (norm_sub_le _ _).trans (by linarith)

/-- Removing the outer frequency cutoff converges strongly to the actual
normalized angular multiplier on the whole \(L^2\) space. -/
theorem tendsto_fourierMultiplier_partialAngular (m : BoundedSymbol E) (u : ComplexL2 E) :
    Tendsto (fun N => fourierMultiplier (partialAngularSymbol m N) u) atTop
      (𝓝 (fourierMultiplier (normalizedAngularSymbol m) u)) := by
  let v := fourierL2Equiv u
  let T (N : ℕ) := symbolL2 (partialAngularSymbol m N) v
  let Tlim := symbolL2 (normalizedAngularSymbol m) v
  let F (N : ℕ) (x : E) := ‖(partialAngularSymbol m N x - normalizedAngularSymbol m x) * v x‖^2
  let B (x : E) := (4 * m.bound)^2 * ‖v x‖^2
  have hF (N : ℕ) : AEStronglyMeasurable (F N) (volume : Measure E) :=
    (continuous_pow 2).comp_aestronglyMeasurable
      (((partialAngularSymbol m N).measurable.sub (normalizedAngularSymbol m).measurable).mul
        (Lp.aestronglyMeasurable v)).norm
  have hB : Integrable B (volume : Measure E) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)).const_mul _
  have hBound (N : ℕ) (x : E) : ‖F N x‖ ≤ B x := by
    unfold F B
    rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (angular_symbol_difference_bound m N x) 2) (sq_nonneg _)
  have hLim (x : E) : Tendsto (fun N => F N x) atTop (𝓝 (0 : ℝ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [partialAngularSymbol_eventually_eq m x] with N hN
    change partialAngularSymbol m N x = normalizedAngularSymbol m x at hN
    simp [F, hN]
  have hDCT := tendsto_integral_filter_of_dominated_convergence B
    (Eventually.of_forall hF) (Eventually.of_forall fun N => Eventually.of_forall (hBound N)) hB
    (Eventually.of_forall hLim)
  have hSq (N : ℕ) : ‖T N - Tlim‖^2 = ∫ x, F N x := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (T N) Tlim,
      symbolL2_ae (partialAngularSymbol m N) v, symbolL2_ae (normalizedAngularSymbol m) v]
      with x hsub hT hlim
    rw [hsub]
    change ‖(T N) x - Tlim x‖^2 = F N x
    rw [hT, hlim, ← sub_mul]
  have hT : Tendsto (fun N => ‖T N - Tlim‖^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [← hSq, integral_zero] using hDCT
  have hT' : Tendsto T atTop (𝓝 Tlim) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have h := (Real.continuous_sqrt.tendsto 0).comp hT
    change Tendsto (fun N => Real.sqrt (‖T N - Tlim‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at h
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h
  simpa only [T, Tlim, v, fourierMultiplier_apply, Function.comp_def] using
    (fourierL2Equiv.symm.continuous.tendsto Tlim).comp hT'

end Burnett.Microlocal.AngularDyadicKernel

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularDyadicKernel

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open scoped FourierTransform ContDiff InnerProduct Topology BigOperators

/-- When the output point lies outside the support of a Schwartz input,
passing to the infinite annular kernel in the actual convolution is justified
by the uniform finite kernel bounds. -/
theorem convolution_partialAngularKernel_tendsto_of_notMem_tsupport
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (f : SchwartzMap E ℂ) (x : E) (hx : x ∉ tsupport (f : E → ℂ)) :
    Tendsto (fun N => ∫ y, partialAngularKernel m hm N (x-y) * f y) atTop
      (𝓝 (∫ y, angularKernel m hm (x-y) * f y)) := by
  obtain ⟨r, hr, hBall⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hx
  have hDist (y : E) (hy : f y ≠ 0) : r ≤ ‖x-y‖ := by
    by_contra hle
    have hmem : y ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
      exact lt_of_not_ge hle
    exact hBall hmem (subset_tsupport (f : E → ℂ) hy)
  obtain ⟨C, hC, hUniform⟩ := partialAngularKernel_uniform_bounds m hm
  have hMeas (N : ℕ) : AEStronglyMeasurable (fun y => partialAngularKernel m hm N (x-y) * f y)
      (volume : Measure E) :=
    (((Differentiable.continuous (fun z => (partialAngularKernel_hasFDerivAt m hm N z).differentiableAt)).comp
      (continuous_const.sub continuous_id)).mul f.continuous).aestronglyMeasurable
  let B (y : E) := (C * (r^4)⁻¹) * ‖f y‖
  have hBound (N : ℕ) (y : E) : ‖partialAngularKernel m hm N (x-y) * f y‖ ≤ B y := by
    by_cases hy : f y = 0
    · simp [B, hy]
    · have hDist' := hDist y hy
      have hp : 0 < ‖x-y‖ := hr.trans_le hDist'
      have hInv : (‖x-y‖^4)⁻¹ ≤ (r^4)⁻¹ :=
        (inv_le_inv₀ (pow_pos hp _) (pow_pos hr _)).mpr (pow_le_pow_left₀ hr.le hDist' _)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        ((hUniform N (x-y) (norm_pos_iff.mp hp)).1.trans (mul_le_mul_of_nonneg_left hInv hC))
        (norm_nonneg _)
  have hLimit (y : E) : Tendsto (fun N => partialAngularKernel m hm N (x-y) * f y) atTop
      (𝓝 (angularKernel m hm (x-y) * f y)) := by
    by_cases hy : f y = 0
    · simp only [hy, mul_zero]
      exact tendsto_const_nhds
    · exact (partialAngularKernel_tendsto m hm (x-y)
        (norm_pos_iff.mp (hr.trans_le (hDist y hy)))).mul_const (f y)
  exact tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall hMeas)
    (Eventually.of_forall fun N => Eventually.of_forall (hBound N))
    (f.integrable.norm.const_mul _) (Eventually.of_forall hLimit)

/-- The actual normalized angular operator has this off-diagonal
kernel on Schwartz inputs, with exact almost-everywhere equality. -/
theorem fourierMultiplier_normalizedAngular_eq_kernel_ae_offSupport
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (f : SchwartzMap E ℂ) :
    ∀ᵐ x ∂(volume : Measure E), x ∉ tsupport (f : E → ℂ) →
      fourierMultiplier (normalizedAngularSymbol m) (f.toLp 2 volume) x =
        ∫ y, angularKernel m hm (x-y) * f y := by
  obtain ⟨φ, hφ, hPts⟩ := (tendstoInMeasure_of_tendsto_Lp
      (tendsto_fourierMultiplier_partialAngular m (f.toLp 2 volume))).exists_seq_tendsto_ae
  have hEqual : ∀ᵐ x ∂(volume : Measure E), ∀ N,
      fourierMultiplier (partialAngularSymbol m N) (f.toLp 2 volume) x =
        ∫ y, partialAngularKernel m hm N (x-y) * f y :=
    ae_all_iff.mpr fun N => fourierMultiplier_partialAngular_eq_kernel_ae m hm hd N f
  filter_upwards [hPts, hEqual] with x hx hEq hxOff
  have hLeft : Tendsto (fun n => ∫ y, partialAngularKernel m hm (φ n) (x-y) * f y) atTop
      (𝓝 (fourierMultiplier (normalizedAngularSymbol m) (f.toLp 2 volume) x)) :=
    hx.congr (fun n => hEq (φ n))
  have hRight := (convolution_partialAngularKernel_tendsto_of_notMem_tsupport m hm f x hxOff).comp
    hφ.tendsto_atTop
  exact tendsto_nhds_unique hLeft hRight

end Burnett.Microlocal.AngularDyadicKernel
