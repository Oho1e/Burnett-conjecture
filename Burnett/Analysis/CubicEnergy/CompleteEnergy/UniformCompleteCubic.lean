import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearUniformCoefficient
import Burnett.Analysis.CubicEnergy.CompleteEnergy.CompleteCubicContinuity
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeSemilinearCubic

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Finset Burnett.RicciSymbol
open scoped BigOperators ContDiff ENNReal

private theorem permutations_card : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  norm_num [Fintype.card_perm, Nat.factorial_succ]

/-- The actual complete symmetric energy is uniformly bounded by the original
degree-one symbol's finite sphere jets and the three input gradients. -/
theorem complete_cubic_map_L3_sphere_bound {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → J → J → J → ℝ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
      (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (D : ℝ), 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ v : Fin 3 → RealEnergyField J,
      ‖completeSymmetricCubicMap c q b hb hom v‖ₑ ≤ C * ENNReal.ofReal D *
        ∏ i, fieldEnergyGradientNorm (v i : J → SchwartzMap E ℂ) := by
  obtain ⟨A, hA, quasilinear⟩ := quasilinear_linear_coefficient_sphere_bound c hc
  obtain ⟨B, hB, semilinear⟩ := semilinear_cubic_multilinear_L3_sphere_bound q
  refine ⟨A + B, ENNReal.add_lt_top.mpr ⟨hA,hB⟩, ?_⟩
  intro b hb hom D hD jet v
  let K := (A + B) * ENNReal.ofReal D
  let T := (quasilinearSymmetricMultilinearMap c b hb hom +
    semilinearCubicMultilinearMap q b hb hom).compLinearMap (fun _ => (realEnergyFields J).subtype)
  have ordered (w : Fin 3 → RealEnergyField J) :
      ‖T w‖ₑ ≤ K * ∏ i, fieldEnergyGradientNorm (w i : J → SchwartzMap E ℂ) := by
    let u : Fin 3 → J → SchwartzMap E ℂ := fun i => w i
    let mass := ∏ i, fieldEnergyGradientNorm (u i)
    have a : ‖quasilinearSymmetricMultilinearMap c b hb hom u‖ₑ ≤ A * ENNReal.ofReal D * mass := by
      rw [quasilinear_symmetric_multilinear_apply, Real.enorm_eq_ofReal_abs]
      dsimp only [mass]
      rw [Fin.prod_univ_three, mul_assoc (fieldEnergyGradientNorm (u 0))]
      exact quasilinear b hb hom D hD jet (u 0) (u 1) (u 2) (w 0).property
    have z : ‖semilinearCubicMultilinearMap q b hb hom u‖ₑ ≤ B * ENNReal.ofReal D * mass := by
      simpa only [semilinearGradientNorm_eq_fieldEnergyGradientNorm, mass] using
        semilinear b hb hom D hD (fun n hn => jet n (le_trans hn (by norm_num))) u
    change ‖quasilinearSymmetricMultilinearMap c b hb hom u + semilinearCubicMultilinearMap q b hb hom u‖ₑ ≤ K * mass
    calc
      _ ≤ _ := (enorm_add_le _ _).trans (add_le_add a z)
      _ = _ := by dsimp only [K]; ring
  let mass := ∏ i, fieldEnergyGradientNorm (v i : J → SchwartzMap E ℂ)
  have each (σ : Equiv.Perm (Fin 3)) : ‖T (fun i => v (σ i))‖ₑ ≤ K * mass := by
    refine (ordered (fun i => v (σ i))).trans_eq ?_
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
    _ ≤ ‖(6 : ℝ)⁻¹‖ₑ * (∑ _σ : Equiv.Perm (Fin 3), K * mass) :=
      mul_le_mul_left' ((enorm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => each σ)) _
    _ = _ := by
      simp only [sum_const, card_univ, permutations_card, nsmul_eq_mul, Nat.cast_ofNat]
      rw [← mul_assoc ‖(6 : ℝ)⁻¹‖ₑ, one, one_mul]

end Burnett.A02.FrequencySplit
