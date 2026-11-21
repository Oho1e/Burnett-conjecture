import Burnett.Analysis.CubicEnergy.CompleteEnergy.LowerOrderCubicEstimate
import Burnett.Analysis.CubicEnergy.CompleteEnergy.SemilinearCubic

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset Metric Burnett.RicciSymbol
open scoped BigOperators ContDiff ENNReal ComplexConjugate

private abbrev CubicExponent : ℝ≥0∞ := ENNReal.ofReal 3
private abbrev DerivativeIndices (J : Type) := (Index × J) × (Index × J)

private theorem component_W13_le_field {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) (j : J) :
    inhomogeneousComponentNorm (u j) ≤ fieldInhomogeneousNorm u := by
  unfold fieldInhomogeneousNorm
  exact Finset.single_le_sum (f := fun i => inhomogeneousComponentNorm (u i))
    (fun _ _ => zero_le _) (mem_univ j)

private theorem derivative_W13_le_field {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ)
    (a : Index) (j : J) :
    eLpNorm (energyPartial a (u j) : E → ℂ) CubicExponent volume ≤ fieldInhomogeneousNorm u := by
  have h : eLpNorm (energyPartial a (u j) : E → ℂ) CubicExponent volume ≤ energyGradientNorm (u j) := by
    apply eLpNorm_mono
    intro x
    change ‖fderiv ℝ (u j : E → ℂ) x (EuclideanSpace.single a 1)‖ ≤ _
    simpa using (fderiv ℝ (u j : E → ℂ) x).le_opNorm (EuclideanSpace.single a 1)
  exact h.trans ((le_add_of_nonneg_left (zero_le
    (eLpNorm (u j : E → ℂ) CubicExponent volume))).trans (component_W13_le_field u j))

def semilinearCoefficientMass {J : Type} [Fintype J] (q : Index → Index → J → J → J → ℝ) : ℝ≥0∞ :=
  ∑ k, ∑ i : DerivativeIndices J, ‖(q i.1.1 i.2.1 i.1.2 i.2.2 k : ℂ)‖ₑ

theorem semilinearCoefficientMass_finite {J : Type} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) : semilinearCoefficientMass q < ⊤ :=
  ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.sum_lt_top.mpr fun _ _ => enorm_lt_top

/-- The actual semilinear physical pairing with an L³-bounded real Fourier test. -/
theorem lower_order_semilinear_hermitian_W13_bound (m : E → ℝ) (K : ℝ≥0∞)
    (bound : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) CubicExponent volume ∧
      eLpNorm (radianAction m g) CubicExponent volume ≤ K * eLpNorm (g : E → ℂ) CubicExponent volume)
    {J : Type} [Fintype J] (q : Index → Index → J → J → J → ℝ) (u v w : J → SchwartzMap E ℂ) :
    (∀ k, Integrable (fun x => semilinearDerivativeTerm q u v k x * conj (radianAction m (w k) x))) ∧
      ‖semilinearHermitianPairing q m u v w‖ₑ ≤ semilinearCoefficientMass q * K *
        (fieldInhomogeneousNorm u * fieldInhomogeneousNorm v * fieldInhomogeneousNorm w) := by
  let W (k : J) (i : DerivativeIndices J) : ℂ := q i.1.1 i.2.1 i.1.2 i.2.2 k
  let M := fieldInhomogeneousNorm u * fieldInhomogeneousNorm v * fieldInhomogeneousNorm w
  let term (k : J) (i : DerivativeIndices J) (x : E) :=
    (W k i * energyPartial i.1.1 (u i.1.2) x * energyPartial i.2.1 (v i.2.2) x) *
      conj (radianAction m (w k) x)
  have each (k : J) (i : DerivativeIndices J) : Integrable (term k i) ∧
      ‖∫ x, term k i x‖ₑ ≤ (‖W k i‖ₑ * K) * M := by
    let A := energyPartial i.1.1 (u i.1.2)
    let B := energyPartial i.2.1 (v i.2.2)
    let C := radianAction m (w k)
    have hC : eLpNorm C CubicExponent volume ≤ K * fieldInhomogeneousNorm w :=
      (bound (w k)).2.trans (mul_le_mul_left'
        ((le_add_of_nonneg_right (zero_le (energyGradientNorm (w k)))).trans (component_W13_le_field w k)) _)
    have eq : term k i = fun x => W k i * (A x * B x * conj (C x)) := by
      funext x
      simp only [term,A,B,C,mul_assoc]
    have int : Integrable (fun x => A x * B x * conj (C x)) := by
      simpa only [energyProduct_apply,C] using
        radian_test_integrable_of_L3 m (energyProduct A B) (w k) (bound (w k)).1
    rw [eq]
    refine ⟨int.const_mul _,?_⟩
    rw [integral_const_mul,enorm_mul]
    have h := (pair_three_cubic A B C (bound (w k)).1).trans (mul_le_mul'
      (mul_le_mul' (derivative_W13_le_field u i.1.1 i.1.2) (derivative_W13_le_field v i.2.1 i.2.2)) hC)
    exact (mul_le_mul_left' h _).trans_eq (by unfold M; ac_rfl)
  have expand (k : J) (x : E) : semilinearDerivativeTerm q u v k x * conj (radianAction m (w k) x) =
      ∑ i, term k i x := by
    change (∑ i : DerivativeIndices J, W k i * energyPartial i.1.1 (u i.1.2) x *
      energyPartial i.2.1 (v i.2.2) x) * conj (radianAction m (w k) x) = _
    simp only [Finset.sum_mul,term]
  refine ⟨fun k => ?_,?_⟩
  · simp_rw [expand]
    exact integrable_finset_sum _ (fun i _ => (each k i).1)
  · unfold semilinearHermitianPairing
    simp_rw [expand]
    have split (k : J) : (∫ x, ∑ i, term k i x) = ∑ i, ∫ x, term k i x :=
      integral_finset_sum _ (fun i _ => (each k i).1)
    simp_rw [split]
    calc
      _ ≤ ∑ k, ∑ i, ‖∫ x, term k i x‖ₑ :=
        (enorm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => enorm_sum_le _ _)
      _ ≤ ∑ k, ∑ i, (‖W k i‖ₑ * K) * M :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ => (each k i).2
      _ = _ := by simp only [semilinearCoefficientMass,W,M,Finset.sum_mul]

theorem lower_order_semilinear_W13_bound (m : E → ℝ) (K : ℝ≥0∞)
    (bound : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) CubicExponent volume ∧
      eLpNorm (radianAction m g) CubicExponent volume ≤ K * eLpNorm (g : E → ℂ) CubicExponent volume)
    {J : Type} [Fintype J] (q : Index → Index → J → J → J → ℝ) (u v w : J → SchwartzMap E ℂ) :
    ‖semilinearCubicForm q m u v w‖ₑ ≤ 2 * semilinearCoefficientMass q * K *
      (fieldInhomogeneousNorm u * fieldInhomogeneousNorm v * fieldInhomogeneousNorm w) := by
  let z := semilinearHermitianPairing q m u v w
  have im : ‖z.im‖ₑ ≤ ‖z‖ₑ := by
    rw [← ofReal_norm_eq_enorm,← ofReal_norm_eq_enorm,Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm z)
  have h := (lower_order_semilinear_hermitian_W13_bound m K bound q u v w).2
  change ‖(2 : ℝ) * z.im‖ₑ ≤ _
  rw [enorm_mul,show ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) by norm_num [← ofReal_norm_eq_enorm]]
  simpa only [mul_assoc] using mul_le_mul_left' (im.trans h) (2 : ℝ≥0∞)

end Burnett.A02.FrequencySplit
