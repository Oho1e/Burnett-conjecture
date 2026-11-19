import Burnett.Counterexamples.Bianchi.Geometry
import Burnett.Counterexamples.RotatingNull.MeasureModel
import Burnett.Counterexamples.RotatingNull.SpacetimeCutoffs
import Burnett.Geometry.LorentzVolume
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Matrix

set_option autoImplicit false

noncomputable section

set_option autoImplicit false

noncomputable section

namespace Burnett.Bianchi.Transport

open Set MeasureTheory Filter Matrix
open scoped ContDiff Topology BigOperators
open Burnett.RicciSymbol
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial momentumBasis)

abbrev Base := Burnett.CubicExplicit.Space
abbrev Phase := Base × Covector
abbrev Spatial := Fin 3
abbrev SpatialMatrix := Matrix Spatial Spatial ℝ

def spatialCovector : Covector →L[ℝ] (Spatial → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.succ

@[simp] theorem spatialCovector_apply (ξ : Covector) (j : Spatial) :
    spatialCovector ξ j = ξ j.succ := rfl

theorem spatialCovector_momentumBasis_zero :
    spatialCovector (momentumBasis 0) = 0 := by
  ext j
  simp [momentumBasis, Fin.succ_ne_zero]

/-- The true spatial quadratic form on covectors. -/
def spatialValue (J : SpatialMatrix) (u : Spatial → ℝ) : ℝ :=
  u ⬝ᵥ (J *ᵥ u)

theorem spatialValue_eq_sum (J : SpatialMatrix) (u : Spatial → ℝ) :
    spatialValue J u = ∑ i, ∑ j, u i * J i j * u j := by
  simp [spatialValue, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem spatialValue_smul (J : SpatialMatrix) (u : Spatial → ℝ) (r : ℝ) :
    spatialValue J (r • u) = r ^ 2 * spatialValue J u := by
  simp only [spatialValue_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem spatialValue_smooth (J : SpatialMatrix) :
    ContDiff ℝ ∞ (spatialValue J) := by
  change ContDiff ℝ ∞ (fun u : Spatial → ℝ => spatialValue J u)
  simp_rw [spatialValue_eq_sum]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (((contDiff_apply ℝ ℝ i).mul contDiff_const).mul (contDiff_apply ℝ ℝ j))

/-- P for the actual translation invariant inverse block diag(-1,J). -/
def hamiltonian (J : ℝ → SpatialMatrix) (x : Base) (ξ : Covector) : ℝ :=
  (-(ξ 0)^2 + spatialValue (J (x 0)) (spatialCovector ξ)) / 2

/-- The genuine canonical coordinate Poisson derivative in time-space and momenta. -/
def hamilton (J : ℝ → SpatialMatrix) (a : Base → Covector → ℝ) (x : Base) (ξ : Covector) : ℝ :=
  ∑ i, (momentumPartial i (hamiltonian J) x ξ * basePartial i a x ξ -
    basePartial i (hamiltonian J) x ξ * momentumPartial i a x ξ)

theorem momentumPartial_time_hamiltonian (J : ℝ → SpatialMatrix) (x : Base) (ξ : Covector) :
    momentumPartial 0 (hamiltonian J) x ξ = -(ξ 0) := by
  have htime := (((ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ).hasFDerivAt
    (x := ξ)).pow 2).neg
  have hspace := ((spatialValue_smooth (J (x 0))).differentiable (by simp)
    (spatialCovector ξ)).hasFDerivAt.comp ξ spatialCovector.hasFDerivAt
  have h := (htime.fun_add hspace).const_mul ((2 : ℝ)⁻¹)
  have he : hamiltonian J x =
      fun ζ : Covector => (2 : ℝ)⁻¹ * (-((ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ) ζ)^2 +
        (spatialValue (J (x 0)) ∘ spatialCovector) ζ) := by
    funext ζ
    change (-(ζ 0)^2 + spatialValue (J (x 0)) (spatialCovector ζ)) / 2 =
      (2 : ℝ)⁻¹ * (-(ζ 0)^2 + spatialValue (J (x 0)) (spatialCovector ζ))
    exact div_eq_inv_mul _ _
  have hd := h.fderiv
  change fderiv ℝ (fun ζ : Covector => (2 : ℝ)⁻¹ *
    (-((ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ) ζ)^2 +
      (spatialValue (J (x 0)) ∘ spatialCovector) ζ)) ξ = _ at hd
  unfold momentumPartial
  rw [he, hd]
  have hs0 : spatialCovector (Pi.single (0 : Index) (1 : ℝ)) = 0 :=
    spatialCovector_momentumBasis_zero
  simp [momentumBasis, hs0]

private theorem basePartial_of_time_spatial (F : ℝ → ℝ) (x : Base)
    (hF : DifferentiableAt ℝ F (x 0)) (j : Spatial) :
    fderiv ℝ (fun y : Base => F (y 0)) x (Burnett.CubicExplicit.basis j.succ) = 0 := by
  have h := hF.hasFDerivAt.comp x (Burnett.CubicExplicit.coord 0).hasFDerivAt
  change (fderiv ℝ (F ∘ Burnett.CubicExplicit.coord 0) x)
    (Burnett.CubicExplicit.basis j.succ) = 0
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, Burnett.CubicExplicit.coord,
    Burnett.CubicExplicit.basis, EuclideanSpace.single_apply, Ne.symm (Fin.succ_ne_zero j)]

theorem basePartial_spatial_hamiltonian (J : ℝ → SpatialMatrix) (x : Base) (ξ : Covector)
    (h : DifferentiableAt ℝ (fun t => spatialValue (J t) (spatialCovector ξ)) (x 0))
    (j : Spatial) :
    basePartial j.succ (hamiltonian J) x ξ = 0 := by
  exact basePartial_of_time_spatial
    (fun t => (-(ξ 0)^2 + spatialValue (J t) (spatialCovector ξ)) / 2) x
    ((differentiableAt_const _).add h |>.div_const 2) j

/-- This is the numerator chosen in the manuscript, on the entire chart. -/
def numerator (x : Base) (ξ : Covector) : ℝ :=
  ξ 1 * ξ 2 - Real.tan (x 0) * (ξ 1)^2

theorem numerator_base_smoothAt (x : Base) (ξ : Covector) (hcos : Real.cos (x 0) ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => numerator y ξ) x := by
  exact contDiffAt_const.sub
    (((Real.contDiffAt_tan.mpr hcos).comp x (Burnett.CubicExplicit.coord 0).contDiff.contDiffAt).mul
      contDiffAt_const)

theorem numerator_momentum_smooth (x : Base) : ContDiff ℝ ∞ (numerator x) := by
  exact ((contDiff_apply ℝ ℝ 1).mul (contDiff_apply ℝ ℝ 2)).sub
    (contDiff_const.mul ((contDiff_apply ℝ ℝ 1).pow 2))

theorem basePartial_time_numerator (x : Base) (ξ : Covector) (hcos : Real.cos (x 0) ≠ 0) :
    basePartial 0 numerator x ξ = -(1 / Real.cos (x 0)^2) * (ξ 1)^2 := by
  have hd := ((Real.hasDerivAt_tan hcos).mul_const ((ξ 1)^2)).const_sub (ξ 1 * ξ 2)
  have h := hd.hasFDerivAt.comp x (Burnett.CubicExplicit.coord 0).hasFDerivAt
  change (fderiv ℝ ((fun t : ℝ => ξ 1 * ξ 2 - Real.tan t * (ξ 1)^2) ∘
    Burnett.CubicExplicit.coord 0) x) (Burnett.CubicExplicit.basis 0) = _
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, Burnett.CubicExplicit.coord,
    Burnett.CubicExplicit.basis, EuclideanSpace.single_apply, smul_eq_mul]

theorem basePartial_spatial_numerator (x : Base) (ξ : Covector) (hcos : Real.cos (x 0) ≠ 0)
    (j : Spatial) : basePartial j.succ numerator x ξ = 0 := by
  exact basePartial_of_time_spatial (fun t => ξ 1 * ξ 2 - Real.tan t * (ξ 1)^2) x
    (((Real.hasDerivAt_tan hcos).mul_const ((ξ 1)^2)).const_sub (ξ 1 * ξ 2)).differentiableAt j

theorem momentumPartial_time_numerator (x : Base) (ξ : Covector) :
    momentumPartial 0 numerator x ξ = 0 := by
  have h1 := (ContinuousLinearMap.proj 1 : Covector →L[ℝ] ℝ).hasFDerivAt (x := ξ)
  have h2 := (ContinuousLinearMap.proj 2 : Covector →L[ℝ] ℝ).hasFDerivAt (x := ξ)
  have h := (h1.fun_mul h2).fun_sub ((h1.pow 2).const_mul (Real.tan (x 0)))
  change (fderiv ℝ (fun ζ : Covector =>
    (ContinuousLinearMap.proj 1 : Covector →L[ℝ] ℝ) ζ *
      (ContinuousLinearMap.proj 2 : Covector →L[ℝ] ℝ) ζ -
    Real.tan (x 0) * ((ContinuousLinearMap.proj 1 : Covector →L[ℝ] ℝ) ζ)^2) ξ)
      (momentumBasis 0) = 0
  rw [h.fderiv]
  norm_num [momentumBasis, ContinuousLinearMap.proj_apply, Pi.single_apply,
    show (2 : Index) ≠ 0 by decide, show (1 : Index) ≠ 0 by decide]

theorem hamilton_numerator (J : ℝ → SpatialMatrix) (x : Base) (ξ : Covector)
    (hJ : DifferentiableAt ℝ (fun t => spatialValue (J t) (spatialCovector ξ)) (x 0))
    (hcos : Real.cos (x 0) ≠ 0) :
    hamilton J numerator x ξ = ξ 0 * (1 / Real.cos (x 0)^2) * (ξ 1)^2 := by
  unfold hamilton
  rw [Fin.sum_univ_succ]
  simp only [basePartial_spatial_numerator x ξ hcos, basePartial_spatial_hamiltonian J x ξ hJ,
    momentumPartial_time_numerator, mul_zero, zero_mul, sub_zero, Finset.sum_const_zero, add_zero,
    momentumPartial_time_hamiltonian, basePartial_time_numerator x ξ hcos]
  ring

theorem hamilton_mul (J : ℝ → SpatialMatrix) (a b : Base → Covector → ℝ) (x : Base) (ξ : Covector)
    (hax : DifferentiableAt ℝ (fun y => a y ξ) x) (hbx : DifferentiableAt ℝ (fun y => b y ξ) x)
    (haξ : DifferentiableAt ℝ (a x) ξ) (hbξ : DifferentiableAt ℝ (b x) ξ) :
    hamilton J (fun y ζ => a y ζ * b y ζ) x ξ =
      a x ξ * hamilton J b x ξ + b x ξ * hamilton J a x ξ := by
  have hx := (hax.hasFDerivAt.fun_mul hbx.hasFDerivAt).fderiv
  have hξ := (haξ.hasFDerivAt.fun_mul hbξ.hasFDerivAt).fderiv
  unfold hamilton
  simp only [basePartial, momentumPartial, hx, hξ, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Burnett.Bianchi.Transport

namespace Burnett.Bianchi.Transport

open Set MeasureTheory Filter Matrix
open scoped ContDiff Topology BigOperators
open Burnett.RicciSymbol

def domain (τ : ℝ) : Set ℝ := Ioo (-τ) τ

def phaseDomain (τ : ℝ) : Set Phase := {z | z.1 0 ∈ domain τ ∧ z.2 ≠ 0}

theorem cos_pos_of_time_mem {τ t : ℝ} (hτ : τ < Real.pi / 4) (ht : t ∈ domain τ) :
    0 < Real.cos t := by
  exact Real.cos_pos_of_mem_Ioo ⟨by have h := ht.1; linarith [Real.pi_pos],
    by have h := ht.2; linarith [Real.pi_pos]⟩

theorem spatialValue_pos (J : SpatialMatrix) (hJ : J.PosDef)
    (u : Spatial → ℝ) (hu : u ≠ 0) : 0 < spatialValue J u := by
  simpa only [spatialValue, star_trivial] using hJ.2 u hu

theorem spatialValue_nonneg (J : SpatialMatrix) (hJ : J.PosDef) (u : Spatial → ℝ) :
    0 ≤ spatialValue J u := by
  simpa only [spatialValue, star_trivial] using hJ.posSemidef.2 u

def angularDenominator (J : ℝ → SpatialMatrix) (x : Base) (ξ : Covector) : ℝ :=
  (ξ 0)^2 + spatialValue (J (x 0)) (spatialCovector ξ)

theorem angularDenominator_pos (J : ℝ → SpatialMatrix) (x : Base) (ξ : Covector)
    (hJ : (J (x 0)).PosDef) (hξ : ξ ≠ 0) : 0 < angularDenominator J x ξ := by
  by_cases h0 : ξ 0 = 0
  · have hsp : spatialCovector ξ ≠ 0 := by
      intro h
      apply hξ
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun h j
    simpa only [angularDenominator, h0, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using
      spatialValue_pos _ hJ _ hsp
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0) (spatialValue_nonneg _ hJ _)

theorem angularDenominator_eq_of_null (J : ℝ → SpatialMatrix) (x : Base) (ξ : Covector)
    (hnull : hamiltonian J x ξ = 0) :
    angularDenominator J x ξ = 2 * (ξ 0)^2 := by
  unfold angularDenominator
  unfold hamiltonian at hnull
  linarith

theorem timeCovector_ne_zero_of_null (J : ℝ → SpatialMatrix) (x : Base) (ξ : Covector)
    (hJ : (J (x 0)).PosDef) (hξ : ξ ≠ 0) (hnull : hamiltonian J x ξ = 0) : ξ 0 ≠ 0 := by
  have hp := angularDenominator_pos J x ξ hJ hξ
  rw [angularDenominator_eq_of_null J x ξ hnull] at hp
  exact fun hz => by simp [hz] at hp

/-- A single smooth multiplier works on both null sheets and all nonzero angles. -/
def testMultiplier (J : ℝ → SpatialMatrix) (f : Base → ℝ) (x : Base) (ξ : Covector) : ℝ :=
  f x * (-2 * ξ 0) / angularDenominator J x ξ

def transportTest (J : ℝ → SpatialMatrix) (f : Base → ℝ) (x : Base) (ξ : Covector) : ℝ :=
  testMultiplier J f x ξ * numerator x ξ

theorem transportTest_eq_on_null (J : ℝ → SpatialMatrix) (f : Base → ℝ)
    (x : Base) (ξ : Covector) (hJ : (J (x 0)).PosDef) (hξ : ξ ≠ 0)
    (hnull : hamiltonian J x ξ = 0) :
    transportTest J f x ξ = f x * numerator x ξ / (-(ξ 0)) := by
  have h0 := timeCovector_ne_zero_of_null J x ξ hJ hξ hnull
  unfold transportTest testMultiplier
  rw [angularDenominator_eq_of_null J x ξ hnull]
  field_simp

theorem transportTest_oneHomogeneous (J : ℝ → SpatialMatrix) (f : Base → ℝ)
    (x : Base) (ξ : Covector) (hJ : (J (x 0)).PosDef) (hξ : ξ ≠ 0)
    (r : ℝ) (hr : 0 < r) : transportTest J f x (r • ξ) = r * transportTest J f x ξ := by
  have hD := (angularDenominator_pos J x ξ hJ hξ).ne'
  have hd : angularDenominator J x (r • ξ) = r^2 * angularDenominator J x ξ := by
    unfold angularDenominator
    rw [map_smul, spatialValue_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hn : numerator x (r • ξ) = r^2 * numerator x ξ := by
    unfold numerator
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  unfold transportTest testMultiplier
  rw [hd, hn]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hr.ne', hD]

private theorem smoothSpatialValue_at (J : ℝ → SpatialMatrix) (x : Base)
    {I : Set ℝ} (hI : IsOpen I) (hx : x 0 ∈ I)
    (hJ : ∀ i j, ContDiffOn ℝ ∞ (fun t => J t i j) I) (ξ : Covector) :
    ContDiffAt ℝ ∞ (fun z : Phase => spatialValue (J (z.1 0)) (spatialCovector z.2)) (x, ξ) := by
  have htime : ContDiff ℝ ∞ (fun z : Phase => z.1 0) :=
    (Burnett.CubicExplicit.coord 0).contDiff.comp contDiff_fst
  have hmom (i : Spatial) : ContDiff ℝ ∞ (fun z : Phase => spatialCovector z.2 i) :=
    (contDiff_apply ℝ ℝ i.succ).comp contDiff_snd
  have hc (i j : Spatial) : ContDiffAt ℝ ∞ (fun z : Phase => J (z.1 0) i j) (x, ξ) := by
    have hpt : ContDiffAt ℝ ∞ (fun t : ℝ => J t i j) (x 0) :=
      (hJ i j).contDiffAt (hI.mem_nhds hx)
    simpa only [Function.comp_apply] using hpt.comp (x, ξ) htime.contDiffAt
  simp_rw [spatialValue_eq_sum]
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    ((hmom i).contDiffAt.mul (hc i j)).mul (hmom j).contDiffAt

private theorem phase_time_smooth : ContDiff ℝ ∞ (fun z : Phase => z.1 0) :=
  (Burnett.CubicExplicit.coord 0).contDiff.comp contDiff_fst

theorem testMultiplier_smoothAt (J : ℝ → SpatialMatrix) (f : Base → ℝ) (hf : ContDiff ℝ ∞ f)
    {I : Set ℝ} (hI : IsOpen I) (x : Base) (hx : x 0 ∈ I) (ξ : Covector) (hξ : ξ ≠ 0)
    (hJ : ∀ i j, ContDiffOn ℝ ∞ (fun t => J t i j) I)
    (hpos : (J (x 0)).PosDef) :
    ContDiffAt ℝ ∞ (fun z : Phase => testMultiplier J f z.1 z.2) (x, ξ) := by
  have h0 : ContDiff ℝ ∞ (fun z : Phase => z.2 0) := (contDiff_apply ℝ ℝ 0).comp contDiff_snd
  exact (((hf.comp contDiff_fst).mul (contDiff_const.mul h0)).contDiffAt).div
    ((h0.pow 2).contDiffAt.add (smoothSpatialValue_at J x hI hx hJ ξ))
    (angularDenominator_pos J x ξ hpos hξ).ne'

theorem transportTest_smooth (J : ℝ → SpatialMatrix) (f : Base → ℝ) (hf : ContDiff ℝ ∞ f)
    {τ : ℝ} (hτ : τ < Real.pi / 4)
    (hJ : ∀ i j, ContDiffOn ℝ ∞ (fun t => J t i j) (domain τ))
    (hpos : ∀ t ∈ domain τ, (J t).PosDef) :
    ContDiffOn ℝ ∞ (fun z : Phase => transportTest J f z.1 z.2) (phaseDomain τ) := by
  rintro ⟨x, ξ⟩ ⟨hx, hξ⟩
  have hcos := (cos_pos_of_time_mem hτ hx).ne'
  have htanPt : ContDiffAt ℝ ∞ Real.tan (x 0) := Real.contDiffAt_tan.mpr hcos
  have htan : ContDiffAt ℝ ∞ (fun z : Phase => Real.tan (z.1 0)) (x, ξ) := by
    simpa only [Function.comp_apply] using htanPt.comp (x, ξ) phase_time_smooth.contDiffAt
  have hmom (i : Index) : ContDiffAt ℝ ∞ (fun z : Phase => z.2 i) (x, ξ) :=
    ((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffAt
  exact ((testMultiplier_smoothAt J f hf isOpen_Ioo x hx ξ hξ hJ (hpos _ hx)).mul
    (((hmom 1).mul (hmom 2)).sub (htan.mul ((hmom 1).pow 2)))).contDiffWithinAt

theorem hamilton_transportTest_on_forced_null (J : ℝ → SpatialMatrix) (f : Base → ℝ)
    (hf : ContDiff ℝ ∞ f) {τ : ℝ} (hτ : τ < Real.pi / 4)
    (hJ : ∀ i j, ContDiffOn ℝ ∞ (fun t => J t i j) (domain τ))
    (x : Base) (hx : x 0 ∈ domain τ) (ξ : Covector) (hξ : ξ ≠ 0)
    (hpos : (J (x 0)).PosDef) (hnull : hamiltonian J x ξ = 0)
    (hforced : numerator x ξ = 0) :
    hamilton J (transportTest J f) x ξ = -(f x * (1 / Real.cos (x 0)^2) * (ξ 1)^2) := by
  have hcos := (cos_pos_of_time_mem hτ hx).ne'
  have hm := testMultiplier_smoothAt J f hf isOpen_Ioo x hx ξ hξ hJ hpos
  have hmBase : DifferentiableAt ℝ (fun y => testMultiplier J f y ξ) x := by
    simpa only [Function.comp_apply, id] using
      (hm.comp x (contDiff_id.prodMk (contDiff_const (c := ξ))).contDiffAt).differentiableAt (by simp)
  have hmMom : DifferentiableAt ℝ (testMultiplier J f x) ξ := by
    simpa only [Function.comp_apply, id] using
      (hm.comp ξ ((contDiff_const (c := x)).prodMk contDiff_id).contDiffAt).differentiableAt (by simp)
  have hsp : DifferentiableAt ℝ (fun t => spatialValue (J t) (spatialCovector ξ)) (x 0) := by
    simp_rw [spatialValue_eq_sum]
    apply (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
      (contDiffAt_const.mul ((hJ i j).contDiffAt (isOpen_Ioo.mem_nhds hx))).mul
        contDiffAt_const : ContDiffAt ℝ ∞ _ _).differentiableAt (by simp)
  change hamilton J (fun y ζ => testMultiplier J f y ζ * numerator y ζ) x ξ = _
  rw [hamilton_mul J _ _ x ξ hmBase
    ((numerator_base_smoothAt x ξ hcos).differentiableAt (by simp)) hmMom
    ((numerator_momentum_smooth x).differentiable (by simp) ξ), hforced, zero_mul, add_zero,
    hamilton_numerator J x ξ hsp hcos, testMultiplier, angularDenominator_eq_of_null J x ξ hnull]
  have h0 := timeCovector_ne_zero_of_null J x ξ hpos hξ hnull
  field_simp [h0]

end Burnett.Bianchi.Transport

namespace Burnett.Bianchi.Transport

open Set MeasureTheory Filter
open scoped ContDiff Topology
open Burnett.RicciSymbol

def IsTransportTest (τ : ℝ) (a : Base → Covector → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun z : Phase => a z.1 z.2) (phaseDomain τ) ∧
  (∀ x : Base, x 0 ∈ domain τ → ∀ ξ : Covector, ξ ≠ 0 → ∀ r : ℝ, 0 < r →
    a x (r • ξ) = r * a x ξ) ∧
  ∃ K : Set Base, IsCompact K ∧ K ⊆ {x : Base | x 0 ∈ domain τ} ∧
    ∀ x ∉ K, ∀ ξ : Covector, ξ ≠ 0 → a x ξ = 0

theorem transportTest_admissible (J : ℝ → SpatialMatrix) (f : Base → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {τ : ℝ} (hτ : τ < Real.pi / 4)
    (ht : tsupport f ⊆ {x : Base | x 0 ∈ domain τ})
    (hJ : ∀ i j, ContDiffOn ℝ ∞ (fun t => J t i j) (domain τ))
    (hpos : ∀ t ∈ domain τ, (J t).PosDef) :
    IsTransportTest τ (transportTest J f) := by
  refine ⟨transportTest_smooth J f hf hτ hJ hpos, ?_, tsupport f, hc, ht, ?_⟩
  · intro x hx ξ hξ r hr
    exact transportTest_oneHomogeneous J f x ξ (hpos _ hx) hξ r hr
  · intro x hx ξ _
    simp [transportTest, testMultiplier, image_eq_zero_of_notMem_tsupport hx]

theorem hamilton_transportTest_at_zero_cutoff (J : ℝ → SpatialMatrix) (f : Base → ℝ)
    (hf : ContDiff ℝ ∞ f) (hnon : ∀ x, 0 ≤ f x) {τ : ℝ} (hτ : τ < Real.pi / 4)
    (hJ : ∀ i j, ContDiffOn ℝ ∞ (fun t => J t i j) (domain τ))
    (x : Base) (hx : x 0 ∈ domain τ) (ξ : Covector) (hξ : ξ ≠ 0)
    (hpos : (J (x 0)).PosDef) (hz : f x = 0) :
    hamilton J (transportTest J f) x ξ = 0 := by
  have hc := (testMultiplier_smoothAt J (fun _ => 1) contDiff_const isOpen_Ioo x hx ξ hξ hJ hpos)
  let g := fun (y : Base) (ζ : Covector) => testMultiplier J (fun _ => 1) y ζ * numerator y ζ
  have hcgx : DifferentiableAt ℝ (fun y => testMultiplier J (fun _ => 1) y ξ) x := by
    simpa only [Function.comp_apply, id] using
      (hc.comp x (contDiff_id.prodMk (contDiff_const (c := ξ))).contDiffAt).differentiableAt (by simp)
  have hcgξ : DifferentiableAt ℝ (testMultiplier J (fun _ => 1) x) ξ := by
    simpa only [Function.comp_apply, id] using
      (hc.comp ξ ((contDiff_const (c := x)).prodMk contDiff_id).contDiffAt).differentiableAt (by simp)
  have hb : DifferentiableAt ℝ (fun y => g y ξ) x :=
    hcgx.mul ((numerator_base_smoothAt x ξ (cos_pos_of_time_mem hτ hx).ne').differentiableAt (by simp))
  have hbξ : DifferentiableAt ℝ (g x) ξ := hcgξ.mul
    ((numerator_momentum_smooth x).differentiable (by simp) ξ)
  have he : transportTest J f = fun y ζ => f y * g y ζ := by
    funext y ζ
    simp only [transportTest, testMultiplier, one_mul, g, div_eq_mul_inv]
    ring
  have hmin : IsLocalMin f x := by
    exact Filter.Eventually.of_forall (fun y => by rw [hz]; exact hnon y)
  have hdz : fderiv ℝ f x = 0 := hmin.fderiv_eq_zero
  have hfHam : hamilton J (fun y (_ : Covector) => f y) x ξ = 0 := by
    simp [hamilton, Burnett.RotatingNullMoments.CanonicalHamilton.basePartial,
      Burnett.RotatingNullMoments.CanonicalHamilton.momentumPartial, hdz]
  rw [he, hamilton_mul J (fun y _ => f y) g x ξ (hf.differentiable (by simp) x) hb
    (differentiableAt_const (f x)) hbξ, hz, hfHam]
  ring

end Burnett.Bianchi.Transport

namespace Burnett.Bianchi.Transport

open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators
open Burnett.RicciSymbol
open Burnett.RotatingNullMoments.MeasureModel (UnitPhase IsTensorTest phaseContraction)

def HasTensorMoments (τ : ℝ) (baseVolume : Measure Base) (G : Base → Tensor2)
    (μ : Measure (UnitPhase (domain τ))) : Prop :=
  ∀ S : Base → Tensor2, IsTensorTest (domain τ) S →
    (∫ p, phaseContraction (domain τ) S p ∂μ) =
      ∫ x, (∑ a, ∑ b, G x a b * S x a b) ∂baseVolume

def HasHamiltonTransport (τ : ℝ) (J : ℝ → SpatialMatrix)
    (μ : Measure (UnitPhase (domain τ))) : Prop :=
  ∀ a : Base → Covector → ℝ, IsTransportTest τ a →
    (∫ p, hamilton J a p.val.1 p.val.2 ∂μ) = 0

def IsNullSupported (τ : ℝ) (J : ℝ → SpatialMatrix)
    (μ : Measure (UnitPhase (domain τ))) : Prop :=
  ∀ᵐ p ∂μ, hamiltonian J p.val.1 p.val.2 = 0

def transverse (x : Base) (ξ : Covector) : ℝ :=
  Real.cos (x 0) * ξ 2 - Real.sin (x 0) * ξ 1

def transverseCoordinate (x : Base) (i : Index) : ℝ :=
  if i = 1 then -Real.sin (x 0) else if i = 2 then Real.cos (x 0) else 0

def transverseTensorTest (f : Base → ℝ) (x : Base) : Tensor2 :=
  fun i j => f x * transverseCoordinate x i * transverseCoordinate x j

theorem transverseTensor_isTest (τ : ℝ) (f : Base → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ {x : Base | x 0 ∈ domain τ}) :
    IsTensorTest (domain τ) (transverseTensorTest f) := by
  have hcoord (i : Index) : ContDiff ℝ ∞ (fun x => transverseCoordinate x i) := by
    unfold transverseCoordinate
    split_ifs
    · exact (Real.contDiff_sin.comp (Burnett.CubicExplicit.coord 0).contDiff).neg
    · exact Real.contDiff_cos.comp (Burnett.CubicExplicit.coord 0).contDiff
    · exact contDiff_const
  have hs : ContDiff ℝ ∞ (transverseTensorTest f) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact (hf.mul (hcoord i)).mul (hcoord j)
  have hsubset : tsupport (transverseTensorTest f) ⊆ tsupport f := by
    apply closure_mono
    intro x hx
    by_contra hz
    have hfz : f x = 0 := not_ne_iff.mp hz
    exact hx (by funext i j; simp [transverseTensorTest, hfz])
  exact ⟨hs, hc.of_isClosed_subset (isClosed_tsupport _) hsubset, hsubset.trans ht,
    fun x i j => by unfold transverseTensorTest; ring⟩

theorem phaseContraction_transverse (τ : ℝ) (f : Base → ℝ) (u : UnitPhase (domain τ)) :
    phaseContraction (domain τ) (transverseTensorTest f) u =
      f u.val.1 * transverse u.val.1 u.val.2 ^ 2 := by
  simp [phaseContraction, transverseTensorTest, transverse, transverseCoordinate, Fin.sum_univ_succ]
  ring

def HasRotatingComponents (τ : ℝ) (G : Base → Tensor2) (c : ℝ → ℝ) : Prop :=
  ∀ x : Base, x 0 ∈ domain τ →
    G x 1 1 = c (x 0) * (Real.cos (x 0))^2 ∧
    G x 1 2 = c (x 0) * (Real.cos (x 0) * Real.sin (x 0)) ∧
    G x 2 1 = c (x 0) * (Real.cos (x 0) * Real.sin (x 0)) ∧
    G x 2 2 = c (x 0) * (Real.sin (x 0))^2

theorem baseContraction_transverse_zero (τ : ℝ) (G : Base → Tensor2) (c : ℝ → ℝ)
    (hG : HasRotatingComponents τ G c) (f : Base → ℝ)
    (ht : tsupport f ⊆ {x : Base | x 0 ∈ domain τ}) (x : Base) :
    (∑ a, ∑ b, G x a b * transverseTensorTest f x a b) = 0 := by
  by_cases hx : x 0 ∈ domain τ
  · obtain ⟨h11, h12, h21, h22⟩ := hG x hx
    simp [transverseTensorTest, transverseCoordinate, Fin.sum_univ_succ, h11, h12, h21, h22]
    ring
  · have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (ht hh))
    simp [transverseTensorTest, h0]

theorem numerator_eq_zero_of_transverse (x : Base) (ξ : Covector)
    (hcos : Real.cos (x 0) ≠ 0) (h : transverse x ξ = 0) : numerator x ξ = 0 := by
  have h' := sub_eq_zero.mp h
  unfold numerator
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  linear_combination ξ 1 * h'

theorem forced_nullspace_ae_on_cutoff (τ : ℝ) (hτ : τ < Real.pi / 4)
    (μ : Measure (UnitPhase (domain τ))) [IsLocallyFiniteMeasure μ]
    (ν : Measure Base) (G : Base → Tensor2) (c : ℝ → ℝ)
    (hm : HasTensorMoments τ ν G μ) (hG : HasRotatingComponents τ G c)
    (f : Base → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ {x : Base | x 0 ∈ domain τ}) (hnon : ∀ x, 0 ≤ f x) :
    ∀ᵐ p ∂μ, f p.val.1 = 0 ∨ numerator p.val.1 p.val.2 = 0 := by
  have hs := transverseTensor_isTest τ f hf hc ht
  have hi := Burnett.RotatingNullMoments.MeasureModel.tensor_test_phase_integrable (domain τ) μ _ hs
  have he : phaseContraction (domain τ) (transverseTensorTest f) =
      fun p : UnitPhase (domain τ) => f p.val.1 * transverse p.val.1 p.val.2 ^ 2 :=
    funext (phaseContraction_transverse τ f)
  rw [he] at hi
  have hmom := hm (transverseTensorTest f) hs
  rw [he] at hmom
  simp_rw [baseContraction_transverse_zero τ G c hG f ht] at hmom
  rw [integral_zero] at hmom
  have hz := (integral_eq_zero_iff_of_nonneg
    (fun p : UnitPhase (domain τ) =>
      mul_nonneg (hnon p.val.1) (sq_nonneg (transverse p.val.1 p.val.2))) hi).mp hmom
  filter_upwards [hz] with p hp
  change f p.val.1 * transverse p.val.1 p.val.2 ^ 2 = 0 at hp
  rcases mul_eq_zero.mp hp with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (numerator_eq_zero_of_transverse _ _
      (cos_pos_of_time_mem hτ p.property.1).ne' (pow_eq_zero h1))

def diagonal11Test (F : Base → ℝ) (x : Base) : Tensor2 :=
  fun a b => if a = 1 ∧ b = 1 then F x else 0

theorem diagonal11Test_isTest (τ : ℝ) (F : Base → ℝ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (ht : tsupport F ⊆ {x : Base | x 0 ∈ domain τ}) : IsTensorTest (domain τ) (diagonal11Test F) := by
  have hs : ContDiff ℝ ∞ (diagonal11Test F) := by
    apply contDiff_pi.mpr
    intro a
    apply contDiff_pi.mpr
    intro b
    unfold diagonal11Test
    split_ifs
    · exact hF
    · exact contDiff_const
  have hsubset : tsupport (diagonal11Test F) ⊆ tsupport F := by
    apply closure_mono
    intro x hx
    by_contra h
    have hFz : F x = 0 := not_ne_iff.mp h
    exact hx (by funext a b; simp [diagonal11Test, hFz])
  exact ⟨hs, hc.of_isClosed_subset (isClosed_tsupport _) hsubset, hsubset.trans ht,
    fun x a b => by simp [diagonal11Test, and_comm]⟩

theorem moment11 (τ : ℝ) (ν : Measure Base) (G : Base → Tensor2) (μ : Measure (UnitPhase (domain τ)))
    (hm : HasTensorMoments τ ν G μ) (F : Base → ℝ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (ht : tsupport F ⊆ {x : Base | x 0 ∈ domain τ}) :
    (∫ p : UnitPhase (domain τ), F p.val.1 * (p.val.2 1)^2 ∂μ) = ∫ x, G x 1 1 * F x ∂ν := by
  have hs := hm (diagonal11Test F) (diagonal11Test_isTest τ F hF hc ht)
  have he (p : UnitPhase (domain τ)) :
      phaseContraction (domain τ) (diagonal11Test F) p = F p.val.1 * (p.val.2 1)^2 := by
    simp [phaseContraction, diagonal11Test, Fin.sum_univ_succ]
    ring
  simpa [he, diagonal11Test, Fin.sum_univ_succ] using hs

end Burnett.Bianchi.Transport

namespace Burnett.Bianchi.Transport

open Set MeasureTheory Filter Matrix
open scoped ContDiff Topology BigOperators ENNReal NNReal Matrix.Norms.Elementwise
open Burnett.RicciSymbol

def baseDomain (τ : ℝ) : Set Base := {x | x 0 ∈ domain τ}

theorem isOpen_baseDomain (τ : ℝ) : IsOpen (baseDomain τ) :=
  isOpen_Ioo.preimage (Burnett.CubicExplicit.coord 0).continuous

theorem exists_nonnegative_cutoff {τ : ℝ} (hτ : 0 < τ) :
    ∃ f : Base → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ baseDomain τ ∧
      (∀ x, 0 ≤ f x) ∧ f 0 = 1 := by
  have hz : (0 : Base) ∈ baseDomain τ := by
    change (0 : ℝ) ∈ Ioo (-τ) τ
    exact ⟨neg_lt_zero.mpr hτ, hτ⟩
  obtain ⟨f, ht, hc, hf, hr, h1⟩ := exists_smooth_tsupport_subset ((isOpen_baseDomain τ).mem_nhds hz)
  exact ⟨f, hf, hc, ht, fun x => (hr (mem_range_self x)).1, h1⟩

private theorem eventually_zero_of_notMem_baseDomain {τ : ℝ} (f : Base → ℝ)
    (ht : tsupport f ⊆ baseDomain τ) {x : Base} (hx : x ∉ baseDomain τ) :
    ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hxc : x ∈ (tsupport f)ᶜ := fun hh => hx (ht hh)
  filter_upwards [isClosed_tsupport f |>.isOpen_compl |>.mem_nhds hxc] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

theorem weightedCutoff_smooth {τ : ℝ} (f w : Base → ℝ) (hf : ContDiff ℝ ∞ f)
    (ht : tsupport f ⊆ baseDomain τ) (hw : ContDiffOn ℝ ∞ w (baseDomain τ)) :
    ContDiff ℝ ∞ (fun x => f x * w x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ baseDomain τ
  · exact hf.contDiffAt.mul (hw.contDiffAt ((isOpen_baseDomain τ).mem_nhds hx))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_zero_of_notMem_baseDomain f ht hx] with y hy
    simp [hy]

theorem weightedCutoff_continuous {τ : ℝ} (f w : Base → ℝ) (hf : Continuous f)
    (ht : tsupport f ⊆ baseDomain τ) (hw : ContinuousOn w (baseDomain τ)) :
    Continuous (fun x => f x * w x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ baseDomain τ
  · exact hf.continuousAt.mul (hw.continuousAt ((isOpen_baseDomain τ).mem_nhds hx))
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_zero_of_notMem_baseDomain f ht hx] with y hy
    simp [hy]

def secWeight (f : Base → ℝ) (x : Base) : ℝ := f x * (1 / Real.cos (x 0)^2)

theorem secWeight_tsupport (f : Base → ℝ) : tsupport (secWeight f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra h
  exact hx (by simp [secWeight, image_eq_zero_of_notMem_tsupport h])

theorem secWeight_smooth {τ : ℝ} (hτ : τ < Real.pi / 4) (f : Base → ℝ)
    (hf : ContDiff ℝ ∞ f) (ht : tsupport f ⊆ baseDomain τ) :
    ContDiff ℝ ∞ (secWeight f) := by
  apply weightedCutoff_smooth f _ hf ht
  have hc : ContDiff ℝ ∞ (fun x : Base => Real.cos (x 0)^2) :=
    (Real.contDiff_cos.comp (Burnett.CubicExplicit.coord 0).contDiff).pow 2
  exact contDiffOn_const.div hc.contDiffOn
    (fun x hx => pow_ne_zero 2 (cos_pos_of_time_mem hτ hx).ne')

theorem contDiffOn_det {I : Set ℝ} (γ : ℝ → SpatialMatrix)
    (hγ : ContDiffOn ℝ ∞ γ I) : ContDiffOn ℝ ∞ (fun t => Matrix.det (γ t)) I := by
  have hentry (i j : Spatial) : ContDiffOn ℝ ∞ (fun t => γ t i j) I :=
    contDiffOn_pi.mp (contDiffOn_pi.mp hγ i) j
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum (fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod (fun i _ => hentry (σ i) i)))

theorem contDiffOn_inverse_entry {I : Set ℝ} (γ : ℝ → SpatialMatrix)
    (hγ : ContDiffOn ℝ ∞ γ I) (hn : ∀ t ∈ I, Matrix.det (γ t) ≠ 0) (i j : Spatial) :
    ContDiffOn ℝ ∞ (fun t => ((γ t)⁻¹) i j) I := by
  have hentry (a b : Spatial) : ContDiffOn ℝ ∞ (fun t => γ t a b) I :=
    contDiffOn_pi.mp (contDiffOn_pi.mp hγ a) b
  have hAdj : ContDiffOn ℝ ∞ (fun t => (γ t).adjugate i j) I := by
    simp only [Matrix.adjugate_apply]
    apply contDiffOn_det
    apply contDiffOn_pi.mpr
    intro a
    apply contDiffOn_pi.mpr
    intro b
    by_cases ha : a = j
    · subst a
      simpa using (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : ℝ => (Pi.single i (1 : ℝ) : Spatial → ℝ) b) I)
    · simpa [Matrix.updateRow_apply, ha] using hentry a b
  have hInv := ((contDiffOn_det γ hγ).inv hn).mul hAdj
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul] using hInv

def rotatingP (t : ℝ) : Spatial → ℝ := ![Real.cos t, Real.sin t, 0]

def directionSquare (γ : ℝ → SpatialMatrix) (t : ℝ) : ℝ :=
  spatialValue ((γ t)⁻¹) (rotatingP t)

theorem directionSquare_pos (γ : ℝ → SpatialMatrix) {τ t : ℝ}
    (hτ : τ < Real.pi / 4) (ht : t ∈ domain τ) (hγ : (γ t).PosDef) :
    0 < directionSquare γ t := by
  apply spatialValue_pos _ hγ.inv
  intro hh
  have hz := congrFun hh 0
  change Real.cos t = 0 at hz
  exact (cos_pos_of_time_mem hτ ht).ne' hz

theorem directionSquare_continuousOn (γ : ℝ → SpatialMatrix) {τ : ℝ}
    (hγ : ContDiffOn ℝ ∞ γ (domain τ)) (hpos : ∀ t ∈ domain τ, (γ t).PosDef) :
    ContinuousOn (directionSquare γ) (domain τ) := by
  have hp (i : Spatial) : Continuous (fun t => rotatingP t i) := by
    fin_cases i
    · exact Real.continuous_cos
    · exact Real.continuous_sin
    · exact continuous_const
  change ContinuousOn (fun t => spatialValue ((γ t)⁻¹) (rotatingP t)) (domain τ)
  simp_rw [spatialValue_eq_sum]
  exact continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ =>
    ((hp i).continuousOn.mul ((contDiffOn_inverse_entry γ hγ
      (fun t ht => (hpos t ht).det_pos.ne') i j).continuousOn)).mul (hp j).continuousOn

def volumeDensity (τ : ℝ) (γ : ℝ → SpatialMatrix) (x : Base) : ℝ≥0 := by
  classical
  exact if x ∈ baseDomain τ then (Real.sqrt |Matrix.det (γ (x 0))|).toNNReal else 0

/-- The determinant density of the synchronous block metric on the given time interval. -/
def metricVolume (τ : ℝ) (γ : ℝ → SpatialMatrix) : Measure Base :=
  (volume : Measure Base).withDensity (fun x => (volumeDensity τ γ x : ℝ≥0∞))

private theorem sqrtDet_continuousOn (γ : ℝ → SpatialMatrix) {τ : ℝ}
    (hγ : ContDiffOn ℝ ∞ γ (domain τ)) :
    ContinuousOn (fun x : Base => Real.sqrt |Matrix.det (γ (x 0))|) (baseDomain τ) :=
  ((contDiffOn_det γ hγ).continuousOn.abs.sqrt).comp
    (Burnett.CubicExplicit.coord 0).continuous.continuousOn (fun _ hx => hx)

theorem volumeDensity_measurable {τ : ℝ} (γ : ℝ → SpatialMatrix)
    (hγ : ContDiffOn ℝ ∞ γ (domain τ)) : Measurable (volumeDensity τ γ) := by
  classical
  change Measurable ((baseDomain τ).piecewise
    (fun x : Base => (Real.sqrt |Matrix.det (γ (x 0))|).toNNReal) (fun _ => 0))
  exact (continuous_real_toNNReal.comp_continuousOn (sqrtDet_continuousOn γ hγ)).measurable_piecewise
    continuousOn_const ((isOpen_baseDomain τ).measurableSet)

theorem metricVolume_integral_positive {τ : ℝ} (hτ : 0 < τ) (hτ' : τ < Real.pi / 4)
    (γ : ℝ → SpatialMatrix) (ρ : ℝ → ℝ)
    (hγ : ContDiffOn ℝ ∞ γ (domain τ)) (hpos : ∀ t ∈ domain τ, (γ t).PosDef)
    (hρ : ContinuousOn ρ (domain τ)) (hρpos : ∀ t ∈ domain τ, 0 < ρ t)
    (f : Base → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ baseDomain τ) (hnon : ∀ x, 0 ≤ f x) (h0 : f 0 = 1) :
    0 < ∫ x, f x * (ρ (x 0) / directionSquare γ (x 0)) ∂metricVolume τ γ := by
  let w : Base → ℝ := fun x => ρ (x 0) / directionSquare γ (x 0) *
    Real.sqrt |Matrix.det (γ (x 0))|
  have hCoeff : ContinuousOn (fun t => ρ t / directionSquare γ t) (domain τ) :=
    hρ.div (directionSquare_continuousOn γ hγ hpos)
      (fun t ht => (directionSquare_pos γ hτ' ht (hpos t ht)).ne')
  have hw : ContinuousOn w (baseDomain τ) :=
    (hCoeff.comp (Burnett.CubicExplicit.coord 0).continuous.continuousOn (fun _ hx => hx)).mul
      (sqrtDet_continuousOn γ hγ)
  have hCont := weightedCutoff_continuous f w hf ht hw
  have hSupport : HasCompactSupport (fun x => f x * w x) := hc.mul_right
  have hMeasure : (∫ x, f x * (ρ (x 0) / directionSquare γ (x 0)) ∂metricVolume τ γ) =
      ∫ x, f x * w x := by
    rw [metricVolume, integral_withDensity_eq_integral_smul (volumeDensity_measurable γ hγ)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ baseDomain τ
      · simp only [volumeDensity, if_pos hx, NNReal.smul_def, Real.coe_toNNReal _ (Real.sqrt_nonneg _), smul_eq_mul, w]
        ring
      · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (ht h))
        simp [hz]
  rw [hMeasure]
  apply hCont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : Base)) hSupport
  · intro x
    by_cases hx : x ∈ baseDomain τ
    · exact mul_nonneg (hnon x)
        (mul_nonneg (div_pos (hρpos _ hx) (directionSquare_pos γ hτ' hx (hpos _ hx))).le
          (Real.sqrt_nonneg _))
    · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (ht h))
      simp [hz]
  · have hx : (0 : ℝ) ∈ domain τ := ⟨neg_lt_zero.mpr hτ, hτ⟩
    change f 0 * (ρ 0 / directionSquare γ 0 * Real.sqrt |Matrix.det (γ 0)|) ≠ 0
    rw [h0, one_mul]
    exact (mul_pos (div_pos (hρpos _ hx) (directionSquare_pos γ hτ' hx (hpos _ hx)))
      (Real.sqrt_pos.mpr (abs_pos.mpr (hpos _ hx).det_pos.ne'))).ne'

end Burnett.Bianchi.Transport

namespace Burnett.Bianchi.Transport

open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
open Burnett.RicciSymbol
open Burnett.RotatingNullMoments.MeasureModel (UnitPhase unitPhase_covector_ne_zero)

theorem hamilton_integral_eq_negative_moment {τ : ℝ} (hτ : τ < Real.pi / 4)
    (γ : ℝ → SpatialMatrix)
    (hγ : ContDiffOn ℝ ∞ γ (domain τ)) (hpos : ∀ t ∈ domain τ, (γ t).PosDef)
    (μ : Measure (UnitPhase (domain τ))) [IsLocallyFiniteMeasure μ]
    (hn : IsNullSupported τ (fun t => (γ t)⁻¹) μ)
    (G : Base → Tensor2) (c : ℝ → ℝ)
    (hm : HasTensorMoments τ (metricVolume τ γ) G μ) (hG : HasRotatingComponents τ G c)
    (f : Base → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ baseDomain τ) (hnon : ∀ x, 0 ≤ f x) :
    (∫ p : UnitPhase (domain τ),
      hamilton (fun t => (γ t)⁻¹) (transportTest (fun t => (γ t)⁻¹) f) p.val.1 p.val.2 ∂μ) =
      -(∫ x, f x * c (x 0) ∂metricVolume τ γ) := by
  let J := fun t => (γ t)⁻¹
  have hJ (i j : Spatial) : ContDiffOn ℝ ∞ (fun t => J t i j) (domain τ) :=
    contDiffOn_inverse_entry γ hγ (fun t ht => (hpos t ht).det_pos.ne') i j
  have hfS := secWeight_tsupport f
  have hF := secWeight_smooth hτ f hf ht
  have htS := hfS.trans ht
  have hcS := hc.of_isClosed_subset (isClosed_tsupport _) hfS
  have hForce := forced_nullspace_ae_on_cutoff τ hτ μ _ G c hm hG f hf hc ht hnon
  have hAE : ∀ᵐ p : UnitPhase (domain τ) ∂μ,
      hamilton J (transportTest J f) p.val.1 p.val.2 =
        -(secWeight f p.val.1 * (p.val.2 1)^2) := by
    filter_upwards [hForce, hn] with p hp hpn
    have htP := p.property.1
    have hξ := unitPhase_covector_ne_zero (domain τ) p
    have hJP : (J (p.val.1 0)).PosDef := (hpos _ htP).inv
    rcases hp with hz | hN
    · rw [hamilton_transportTest_at_zero_cutoff J f hf hnon hτ hJ _ htP _ hξ hJP hz]
      simp [secWeight, hz]
    · exact hamilton_transportTest_on_forced_null J f hf hτ hJ _ htP _ hξ hJP hpn hN
  change (∫ p : UnitPhase (domain τ),
      hamilton J (transportTest J f) p.val.1 p.val.2 ∂μ) = _
  rw [integral_congr_ae hAE, integral_neg, moment11 τ _ G μ hm _ hF hcS htS]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change G x 1 1 * secWeight f x = f x * c (x 0)
    by_cases hx : x ∈ baseDomain τ
    · have hcos := (cos_pos_of_time_mem hτ hx).ne'
      rw [(hG x hx).1]
      unfold secWeight
      field_simp
    · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (ht h))
      simp [secWeight, hz]

/-- No positive measure, on either or both time sheets, has the two compatible identities. -/
theorem no_positive_representation (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < Real.pi / 4)
    (γ : ℝ → SpatialMatrix) (ρ : ℝ → ℝ)
    (hγ : ContDiffOn ℝ ∞ γ (domain τ)) (hpos : ∀ t ∈ domain τ, (γ t).PosDef)
    (hρ : ContinuousOn ρ (domain τ)) (hρpos : ∀ t ∈ domain τ, 0 < ρ t)
    (G : Base → Tensor2) (hG : HasRotatingComponents τ G (fun t => ρ t / directionSquare γ t)) :
    ¬ ∃ μ : Measure (UnitPhase (domain τ)),
      IsLocallyFiniteMeasure μ ∧ IsNullSupported τ (fun t => (γ t)⁻¹) μ ∧
        HasTensorMoments τ (metricVolume τ γ) G μ ∧
        HasHamiltonTransport τ (fun t => (γ t)⁻¹) μ := by
  rintro ⟨μ, hloc, hn, hm, htransport⟩
  letI : IsLocallyFiniteMeasure μ := hloc
  obtain ⟨f, hf, hc, ht, hnon, h0⟩ := exists_nonnegative_cutoff hτ
  have hJ (i j : Spatial) : ContDiffOn ℝ ∞ (fun t => ((γ t)⁻¹) i j) (domain τ) :=
    contDiffOn_inverse_entry γ hγ (fun t ht => (hpos t ht).det_pos.ne') i j
  have htest := transportTest_admissible (fun t => (γ t)⁻¹) f hf hc hτ' ht hJ
    (fun t ht => (hpos t ht).inv)
  have hz := htransport _ htest
  have heq := hamilton_integral_eq_negative_moment hτ' γ hγ hpos μ hn G _ hm hG f hf hc ht hnon
  have hpositive := metricVolume_integral_positive hτ hτ' γ ρ hγ hpos hρ hρpos f
    hf.continuous hc ht hnon h0
  linarith

end Burnett.Bianchi.Transport

namespace Burnett.Bianchi.Transport

open Set Matrix MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.InverseField
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)
open Burnett.RotatingNullMoments.MeasureModel (UnitPhase)

theorem det_block (c : ℝ) (G : SpatialMatrix) :
    Matrix.det (Burnett.Bianchi.block c G) = c * Matrix.det G := by
  have hminor : (Burnett.Bianchi.block c G).submatrix Fin.succ (0 : Index).succAbove = G := by
    ext i j
    rw [Matrix.submatrix_apply, Fin.zero_succAbove, Burnett.Bianchi.block_space_space]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Burnett.Bianchi.block_time_time, Burnett.Bianchi.block_time_space, Fin.val_zero,
    pow_zero, one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, hminor]

theorem symbolNorm_block (J : SpatialMatrix) (ξ : Covector) :
    symbolNorm (Burnett.Bianchi.block (-1) J) ξ = -(ξ 0)^2 + spatialValue J (spatialCovector ξ) := by
  have hrow (a : Index) : (∑ b : Index, Burnett.Bianchi.block (-1) J a b * ξ a * ξ b) =
      Burnett.Bianchi.block (-1) J a 0 * ξ a * ξ 0 +
        ∑ j : Spatial, Burnett.Bianchi.block (-1) J a j.succ * ξ a * ξ j.succ :=
    Fin.sum_univ_succ _
  unfold symbolNorm
  rw [Fin.sum_univ_succ]
  simp_rw [hrow]
  simp only [Burnett.Bianchi.block_time_time, Burnett.Bianchi.block_time_space,
    Burnett.Bianchi.block_space_time, Burnett.Bianchi.block_space_space, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, spatialValue_eq_sum, spatialCovector_apply]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Canonical Hamiltonian calculated directly from the actual coordinate inverse metric. -/
def metricHamiltonian (γ : ℝ → SpatialMatrix) (x : Base) (ξ : Covector) : ℝ :=
  symbolNorm (matrixInverse (metricComponents (Burnett.Bianchi.metric γ) x)) ξ / 2

theorem metricHamiltonian_eq (γ : ℝ → SpatialMatrix) (x : Base) (ξ : Covector)
    (h : (γ (x 0)).PosDef) :
    metricHamiltonian γ x ξ = hamiltonian (fun t => (γ t)⁻¹) x ξ := by
  rw [metricHamiltonian, Burnett.Bianchi.metric_components,
    Burnett.Bianchi.matrixInverse_block _ h.isUnit, symbolNorm_block]
  rfl

def metricHamiltonTransport (γ : ℝ → SpatialMatrix) (a : Base → Covector → ℝ)
    (x : Base) (ξ : Covector) : ℝ :=
  ∑ i, (momentumPartial i (metricHamiltonian γ) x ξ * basePartial i a x ξ -
    basePartial i (metricHamiltonian γ) x ξ * momentumPartial i a x ξ)

theorem metricHamiltonTransport_eq {τ : ℝ} (γ : ℝ → SpatialMatrix) (a : Base → Covector → ℝ)
    (x : Base) (hx : x ∈ baseDomain τ) (ξ : Covector)
    (hpos : ∀ t ∈ domain τ, (γ t).PosDef) :
    metricHamiltonTransport γ a x ξ = hamilton (fun t => (γ t)⁻¹) a x ξ := by
  have hp : metricHamiltonian γ x = hamiltonian (fun t => (γ t)⁻¹) x :=
    funext fun ζ => metricHamiltonian_eq γ x ζ (hpos _ hx)
  have hb : (fun y => metricHamiltonian γ y ξ) =ᶠ[𝓝 x]
      (fun y => hamiltonian (fun t => (γ t)⁻¹) y ξ) := by
    filter_upwards [(isOpen_baseDomain τ).mem_nhds hx] with y hy
    exact metricHamiltonian_eq γ y ξ (hpos _ hy)
  simp only [metricHamiltonTransport, hamilton, basePartial, momentumPartial, hp, hb.fderiv_eq]

theorem metricVolume_eq_restrict_coordinateMeasure (τ : ℝ) (γ : ℝ → SpatialMatrix) :
    metricVolume τ γ =
      (Burnett.Geometry.LorentzVolume.coordinateMeasure
        (metricComponents (Burnett.Bianchi.metric γ))).restrict (baseDomain τ) := by
  classical
  let density := Burnett.Geometry.LorentzVolume.density (metricComponents (Burnett.Bianchi.metric γ))
  have h : (fun x : Base => (volumeDensity τ γ x : ℝ≥0∞)) = (baseDomain τ).indicator density := by
    funext x
    by_cases hx : x ∈ baseDomain τ
    · rw [volumeDensity, if_pos hx, indicator_of_mem hx]
      simp [density, Burnett.Geometry.LorentzVolume.density, Burnett.Bianchi.metric_components, det_block,
        ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    · simp [volumeDensity, hx]
  rw [metricVolume, h, withDensity_indicator (isOpen_baseDomain τ).measurableSet,
    Burnett.Geometry.LorentzVolume.coordinateMeasure, restrict_withDensity (isOpen_baseDomain τ).measurableSet]

theorem directionSquare_eq_spatialQuadratic (γ : ℝ → SpatialMatrix) (t : ℝ) :
    directionSquare γ t = Burnett.Bianchi.spatialQuadratic ((γ t)⁻¹) (rotatingP t) := by
  rw [directionSquare, spatialValue_eq_sum, Burnett.Bianchi.spatialQuadratic]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rotatingComponents_of_sourceTensor {τ : ℝ} (γ : ℝ → SpatialMatrix) (ρ : ℝ → ℝ)
    (G : Base → Tensor2)
    (h : ∀ x : Base, x ∈ baseDomain τ →
      G x = Burnett.Bianchi.sourceTensor (ρ (x 0))
        (Burnett.Bianchi.spatialQuadratic ((γ (x 0))⁻¹) (rotatingP (x 0))) (rotatingP (x 0))) :
    HasRotatingComponents τ G (fun t => ρ t / directionSquare γ t) := by
  intro x hx
  rw [h x hx, Burnett.Bianchi.sourceTensor]
  simp only [directionSquare_eq_spatialQuadratic]
  change (ρ (x 0) / Burnett.Bianchi.spatialQuadratic _ _) * (Real.cos (x 0) * Real.cos (x 0)) = _ ∧
    (ρ (x 0) / Burnett.Bianchi.spatialQuadratic _ _) * (Real.cos (x 0) * Real.sin (x 0)) = _ ∧
    (ρ (x 0) / Burnett.Bianchi.spatialQuadratic _ _) * (Real.sin (x 0) * Real.cos (x 0)) = _ ∧
    (ρ (x 0) / Burnett.Bianchi.spatialQuadratic _ _) * (Real.sin (x 0) * Real.sin (x 0)) = _
  refine ⟨?_, rfl, ?_, ?_⟩ <;> ring

/-- Exclusion using the actual canonical Hamiltonian and actual restricted metric volume. -/
theorem no_representation_for_coordinate_metric (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < Real.pi / 4)
    (γ : ℝ → SpatialMatrix) (ρ : ℝ → ℝ)
    (hγ : ContDiffOn ℝ ∞ γ (domain τ)) (hpos : ∀ t ∈ domain τ, (γ t).PosDef)
    (hρ : ContinuousOn ρ (domain τ)) (hρpos : ∀ t ∈ domain τ, 0 < ρ t)
    (G : Base → Tensor2)
    (h : ∀ x : Base, x ∈ baseDomain τ →
      G x = Burnett.Bianchi.sourceTensor (ρ (x 0))
        (Burnett.Bianchi.spatialQuadratic ((γ (x 0))⁻¹) (rotatingP (x 0))) (rotatingP (x 0))) :
    ¬ ∃ μ : Measure (UnitPhase (domain τ)),
      IsLocallyFiniteMeasure μ ∧
      (∀ᵐ p ∂μ, metricHamiltonian γ p.val.1 p.val.2 = 0) ∧
      HasTensorMoments τ ((Burnett.Geometry.LorentzVolume.coordinateMeasure
        (metricComponents (Burnett.Bianchi.metric γ))).restrict (baseDomain τ)) G μ ∧
      (∀ a : Base → Covector → ℝ, IsTransportTest τ a →
        ∫ p, metricHamiltonTransport γ a p.val.1 p.val.2 ∂μ = 0) := by
  rintro ⟨μ, hloc, hn, hm, ht⟩
  apply no_positive_representation τ hτ hτ' γ ρ hγ hpos hρ hρpos G
    (rotatingComponents_of_sourceTensor γ ρ G h)
  refine ⟨μ, hloc, ?_, ?_, ?_⟩
  · filter_upwards [hn] with p hp
    exact (metricHamiltonian_eq γ _ _ (hpos _ p.property.1)).symm.trans hp
  · simpa only [metricVolume_eq_restrict_coordinateMeasure] using hm
  · intro a ha
    have heq (p : UnitPhase (domain τ)) :
        metricHamiltonTransport γ a p.val.1 p.val.2 =
          hamilton (fun t => (γ t)⁻¹) a p.val.1 p.val.2 :=
      metricHamiltonTransport_eq γ a _ p.property.1 _ hpos
    simpa only [heq] using ht a ha

end Burnett.Bianchi.Transport
