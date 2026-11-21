import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearCubicAlgebra
import Burnett.Analysis.CubicEnergy.CompleteEnergy.SemilinearCubicAlgebra
import Mathlib.Data.Fintype.Perm

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Finset Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff ENNReal

/-- The real component fields inside the complex Schwartz spaces used by the
Fourier transform. Realness concerns the input fields, in each component. -/
def realEnergyFields (J : Type) : Submodule ℝ (J → SchwartzMap E ℂ) where
  carrier := {u | ∀ j x, conj (u j x) = u j x}
  zero_mem' := by
    intro j x
    change conj (0 : ℂ) = 0
    exact map_zero _
  add_mem' := by
    intro u v hu hv j x
    change conj (u j x + v j x) = u j x + v j x
    rw [map_add, hu j x, hv j x]
  smul_mem' r u hu := by
    intro j x
    change conj (r • u j x) = r • u j x
    rw [Complex.real_smul, map_mul, Complex.conj_ofReal, hu j x]

abbrev RealEnergyField (J : Type) := ↥(realEnergyFields J)

theorem semilinearGradientNorm_eq_fieldEnergyGradientNorm {J : Type} [Fintype J]
    (u : J → SchwartzMap E ℂ) :
    semilinearGradientNorm u = fieldEnergyGradientNorm u := by
  have e3 : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
  simp only [semilinearGradientNorm, fieldEnergyGradientNorm, energyGradientNorm, e3]

/-- The complete physical diagonal with the actual second-derivative and
first-derivative pairings, in the radian convention. -/
def completeCubicEnergy {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ) (u : RealEnergyField J) : ℝ :=
  2 * (quasilinearPairing b (linearEnergyCoefficient c u) u + semilinearHermitianPairing q b u u u).im

private def completeOrderedCubicMap {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) :
    MultilinearMap ℝ (fun _ : Fin 3 => RealEnergyField J) ℝ :=
  (quasilinearSymmetricMultilinearMap c b hb hom + semilinearCubicMultilinearMap q b hb hom).compLinearMap
    (fun _ => (realEnergyFields J).subtype)

private theorem completeOrderedCubicMap_diag {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (u : RealEnergyField J) :
    completeOrderedCubicMap c q b hb hom (fun _ => u) = completeCubicEnergy c q b u := by
  change quasilinearSymmetricMultilinearMap c b hb hom (fun _ => (u : J → SchwartzMap E ℂ)) +
    semilinearCubicMultilinearMap q b hb hom (fun _ => (u : J → SchwartzMap E ℂ)) = _
  rw [quasilinear_symmetric_multilinear_diag, semilinear_cubic_multilinear_apply,
    semilinearCubicForm, completeCubicEnergy, Complex.add_im]
  ring

private theorem completeOrderedCubicMap_bound {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v : Fin 3 → RealEnergyField J,
      ‖completeOrderedCubicMap c q b hb hom v‖ₑ ≤ C * ∏ i, fieldEnergyGradientNorm (v i : J → SchwartzMap E ℂ) := by
  obtain ⟨A,hA,qbound⟩ := quasilinear_symmetric_multilinear_L3_bound c hc b hb hom
  obtain ⟨B,hB,sbound⟩ := semilinear_cubic_multilinear_L3_bound q b hb hom
  refine ⟨A+B,ENNReal.add_lt_top.mpr ⟨hA,hB⟩,?_⟩
  intro v
  let u : Fin 3 → J → SchwartzMap E ℂ := fun i => v i
  have one := qbound u (v 0).property
  have two := sbound u
  simp only [semilinearGradientNorm_eq_fieldEnergyGradientNorm] at two
  change ‖quasilinearSymmetricMultilinearMap c b hb hom u + semilinearCubicMultilinearMap q b hb hom u‖ₑ ≤
    (A+B) * ∏ i, fieldEnergyGradientNorm (u i)
  rw [add_mul]
  exact (enorm_add_le _ _).trans (add_le_add one two)

private theorem permutations_card : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  norm_num [Fintype.card_perm, Nat.factorial_succ]

/-- Average all six assignments of the three real inputs to the exact
quasilinear and semilinear pairings. -/
def completeSymmetricCubicMap {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) :
    MultilinearMap ℝ (fun _ : Fin 3 => RealEnergyField J) ℝ :=
  (6 : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin 3), (completeOrderedCubicMap c q b hb hom).domDomCongr σ

private def permutationAfter (τ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 3) ≃ Equiv.Perm (Fin 3) where
  toFun σ := σ.trans τ
  invFun σ := σ.trans τ.symm
  left_inv σ := by ext i; simp
  right_inv σ := by ext i; simp

theorem complete_cubic_map_symmetric {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (v : Fin 3 → RealEnergyField J) (τ : Equiv.Perm (Fin 3)) :
    completeSymmetricCubicMap c q b hb hom (v ∘ τ) = completeSymmetricCubicMap c q b hb hom v := by
  let T := completeOrderedCubicMap c q b hb hom
  simp only [completeSymmetricCubicMap, MultilinearMap.smul_apply, MultilinearMap.sum_apply,
    MultilinearMap.domDomCongr_apply, Function.comp_apply]
  congr 1
  exact Fintype.sum_equiv (permutationAfter τ) (fun σ => T (fun i => v (τ (σ i))))
    (fun σ => T (fun i => v (σ i))) (fun _ => rfl)

theorem complete_cubic_map_diag {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (u : RealEnergyField J) :
    completeSymmetricCubicMap c q b hb hom (fun _ => u) = completeCubicEnergy c q b u := by
  simp only [completeSymmetricCubicMap, MultilinearMap.smul_apply, MultilinearMap.sum_apply,
    MultilinearMap.domDomCongr_apply, completeOrderedCubicMap_diag, sum_const, card_univ,
    permutations_card, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (6 : ℝ) ≠ 0), one_mul]

theorem complete_cubic_map_L3_bound {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v : Fin 3 → RealEnergyField J,
      ‖completeSymmetricCubicMap c q b hb hom v‖ₑ ≤ C * ∏ i,
        fieldEnergyGradientNorm (v i : J → SchwartzMap E ℂ) := by
  obtain ⟨K,hK,est⟩ := completeOrderedCubicMap_bound c hc q b hb hom
  refine ⟨K,hK,?_⟩
  intro v
  let T := completeOrderedCubicMap c q b hb hom
  let mass := ∏ i, fieldEnergyGradientNorm (v i : J → SchwartzMap E ℂ)
  have each (σ : Equiv.Perm (Fin 3)) : ‖T (fun i => v (σ i))‖ₑ ≤ K * mass := by
    refine (est (fun i => v (σ i))).trans_eq ?_
    exact congrArg (K * ·) (Fintype.prod_equiv σ _ _ (fun _ => rfl))
  have one : ‖(6 : ℝ)⁻¹‖ₑ * (6 : ℝ≥0∞) = 1 := by
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by positivity : 0 ≤ (6 : ℝ)⁻¹),
      show (6 : ℝ≥0∞) = ENNReal.ofReal (6 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (6 : ℝ)⁻¹)]
    norm_num
  simp only [completeSymmetricCubicMap, MultilinearMap.smul_apply, MultilinearMap.sum_apply,
    MultilinearMap.domDomCongr_apply, smul_eq_mul, enorm_mul]
  change ‖(6 : ℝ)⁻¹‖ₑ * ‖∑ σ : Equiv.Perm (Fin 3), T (fun i => v (σ i))‖ₑ ≤ K * mass
  calc
    _ ≤ ‖(6 : ℝ)⁻¹‖ₑ * (∑ σ : Equiv.Perm (Fin 3), K * mass) :=
      mul_le_mul_left' ((enorm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => each σ)) _
    _ = _ := by
      simp only [sum_const, card_univ, permutations_card, nsmul_eq_mul, Nat.cast_ofNat]
      rw [← mul_assoc ‖(6 : ℝ)⁻¹‖ₑ, one, one_mul]

end Burnett.A02.FrequencySplit
