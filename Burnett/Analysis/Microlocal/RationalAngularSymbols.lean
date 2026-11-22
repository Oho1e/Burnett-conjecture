import Burnett.Analysis.Microlocal.AngularCommutator.FrequencyKernel
import Burnett.Analysis.Sobolev.TestJet
import Burnett.Analysis.Fourier.Projection
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Algebra.MvPolynomial.Basic

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.SmoothAngularTests

open Burnett.Microlocal.AngularCommutator MvPolynomial
open scoped ContDiff

abbrev Space := Burnett.X02.SobolevTestJet.Space
abbrev UnitSphere := ↥(Metric.sphere (0 : Space) 1)
abbrev RationalPolynomial := MvPolynomial (Fin 4) ℚ

/-- Real normalized coordinate, with the canonical zero value at the origin. -/
def angularCoordinate (i : Fin 4) (ξ : Space) : ℝ :=
  ξ i / ‖ξ‖

theorem angularCoordinate_contDiffOn (i : Fin 4) :
    ContDiffOn ℝ ∞ (angularCoordinate i) ({0}ᶜ : Set Space) := by
  intro ξ hξ
  have h0 : ξ ≠ 0 := hξ
  have hcoord : ContDiff ℝ ∞ (fun y : Space => y i) :=
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) i : Space →L[ℝ] ℝ).contDiff
  exact hcoord.contDiffWithinAt.div (contDiffAt_norm ℝ h0).contDiffWithinAt
    (norm_ne_zero_iff.mpr h0)

theorem angularCoordinate_pos_smul (i : Fin 4) (r : ℝ) (hr : 0 < r) (ξ : Space) :
    angularCoordinate i (r • ξ) = angularCoordinate i ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  · rw [angularCoordinate, angularCoordinate, PiLp.smul_apply, smul_eq_mul,
        norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_div_mul_left _ _ (ne_of_gt hr)

theorem norm_angularCoordinate_le_one (i : Fin 4) (ξ : Space) :
    ‖angularCoordinate i ξ‖ ≤ 1 := by
  by_cases hξ : ξ = 0
  · simp [angularCoordinate, hξ]
  · rw [angularCoordinate, norm_div, norm_norm, div_le_iff₀ (norm_pos_iff.mpr hξ),
        one_mul]
    exact PiLp.norm_apply_le ξ i

/-- The pointwise rational polynomial evaluation on the actual frequencies. -/
def rationalAngular (p : RationalPolynomial) (ξ : Space) : ℝ :=
  p.eval₂ (Rat.castHom ℝ) (fun i => angularCoordinate i ξ)

theorem rationalAngular_contDiffOn (p : RationalPolynomial) :
    ContDiffOn ℝ ∞ (rationalAngular p) ({0}ᶜ : Set Space) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [show rationalAngular (C c) = fun _ : Space => (Rat.castHom ℝ) c by
        funext ξ; exact eval₂_C _ _ _]
      exact contDiffOn_const
  | add p q hp hq =>
      rw [show rationalAngular (p + q) = fun ξ => rationalAngular p ξ + rationalAngular q ξ by
        funext ξ; exact eval₂_add _ _]
      exact hp.add hq
  | mul_X p i hp =>
      rw [show rationalAngular (p * X i) = fun ξ => rationalAngular p ξ * angularCoordinate i ξ by
        funext ξ; simp only [rationalAngular, eval₂_mul, eval₂_X]]
      exact hp.mul (angularCoordinate_contDiffOn i)

theorem rationalAngular_pos_smul (p : RationalPolynomial) (r : ℝ) (hr : 0 < r) (ξ : Space) :
    rationalAngular p (r • ξ) = rationalAngular p ξ := by
  unfold rationalAngular
  rw [show (fun i => angularCoordinate i (r • ξ)) = fun i => angularCoordinate i ξ from
    funext fun i => angularCoordinate_pos_smul i r hr ξ]

theorem rationalAngular_uniform_bound (p : RationalPolynomial) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ, ‖rationalAngular p ξ‖ ≤ B := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      exact ⟨‖(Rat.castHom ℝ) c‖, norm_nonneg _, fun ξ => by simp [rationalAngular]⟩
  | add p q hp hq =>
      obtain ⟨Bp, hBp, hp⟩ := hp
      obtain ⟨Bq, hBq, hq⟩ := hq
      refine ⟨Bp + Bq, add_nonneg hBp hBq, fun ξ => ?_⟩
      change ‖(p + q).eval₂ _ _‖ ≤ Bp + Bq
      rw [eval₂_add]
      exact (norm_add_le _ _).trans (add_le_add (hp ξ) (hq ξ))
  | mul_X p i hp =>
      obtain ⟨Bp, hBp, hp⟩ := hp
      refine ⟨Bp, hBp, fun ξ => ?_⟩
      rw [rationalAngular, eval₂_mul, eval₂_X, norm_mul]
      exact (mul_le_mul (hp ξ) (norm_angularCoordinate_le_one i ξ)
        (norm_nonneg _) hBp).trans_eq (mul_one _)

/-- Pairs of rational polynomials supply real and imaginary parts independently. -/
def complexRationalAngular (p : RationalPolynomial × RationalPolynomial) (ξ : Space) : ℂ :=
  (rationalAngular p.1 ξ : ℂ) + Complex.I * (rationalAngular p.2 ξ : ℂ)

theorem complexRationalAngular_contDiffOn (p : RationalPolynomial × RationalPolynomial) :
    ContDiffOn ℝ ∞ (complexRationalAngular p) ({0}ᶜ : Set Space) := by
  have hs (q : RationalPolynomial) :
      ContDiffOn ℝ ∞ (fun ξ => (rationalAngular q ξ : ℂ)) ({0}ᶜ : Set Space) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (rationalAngular_contDiffOn q)
  exact (hs p.1).add (contDiffOn_const.mul (hs p.2))

theorem complexRationalAngular_degreeZero (p : RationalPolynomial × RationalPolynomial) :
    DegreeZero (complexRationalAngular p) := by
  intro r hr ξ
  simp only [complexRationalAngular, rationalAngular_pos_smul _ r hr ξ]

theorem complexRationalAngular_uniform_bound (p : RationalPolynomial × RationalPolynomial) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ, ‖complexRationalAngular p ξ‖ ≤ B := by
  obtain ⟨Br, hBr, hr⟩ := rationalAngular_uniform_bound p.1
  obtain ⟨Bi, hBi, hi⟩ := rationalAngular_uniform_bound p.2
  refine ⟨Br + Bi, add_nonneg hBr hBi, fun ξ => ?_⟩
  unfold complexRationalAngular
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real]
  exact add_le_add (hr ξ) (hi ξ)

/-- An input for the production bounded Fourier multiplier. -/
def complexRationalAngularSymbol (p : RationalPolynomial × RationalPolynomial) :
    Burnett.Fourier.BoundedSymbol Space where
  toFun := complexRationalAngular p
  measurable := (measurable_of_angular_smooth _ (complexRationalAngular_contDiffOn p)).aestronglyMeasurable
  bound := (complexRationalAngular_uniform_bound p).choose
  bound_nonneg := (complexRationalAngular_uniform_bound p).choose_spec.1
  norm_le := (complexRationalAngular_uniform_bound p).choose_spec.2

private theorem countableFinsupp (α β : Type) [Countable α] [Countable β] [Zero β] :
    Countable (α →₀ β) := by
  classical
  letI : Encodable (α × β) := Encodable.ofCountable _
  letI : Countable (Finset (α × β)) := List.toFinset_surjective.countable
  exact (Finsupp.graph_injective α β).countable

theorem exists_rationalAngular_enumeration :
    ∃ e : ℕ → RationalPolynomial × RationalPolynomial, Function.Surjective e := by
  letI : Countable (Fin 4 →₀ ℕ) := countableFinsupp _ _
  letI : Countable RationalPolynomial := countableFinsupp (Fin 4 →₀ ℕ) ℚ
  exact exists_surjective_nat _

end Burnett.Microlocal.SmoothAngularTests
