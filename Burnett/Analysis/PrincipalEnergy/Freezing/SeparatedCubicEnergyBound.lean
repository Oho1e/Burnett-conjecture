import Burnett.Analysis.PrincipalEnergy.Freezing.EnergyHolder
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedEnergyFields
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedPrincipalEnergy

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace Burnett.A02.FrequencySplit

open MeasureTheory Metric Burnett.RicciSymbol Burnett.A02.FieldAndCoefficientReview
open scoped BigOperators ComplexConjugate ContDiff ENNReal

/-- The three factors in the cubic bound for one actual separated test. -/
def separatedCubicBoundRhs (C₀ C₁ F₀ F₁ F₂ X Y : ℝ≥0∞) : ℝ≥0∞ :=
  C₀ * F₀ * X ^ 3 + (C₀ * F₁ + C₁ * F₀) * Y * X ^ 2 + C₀ * F₂ * Y ^ 2 * X

private theorem separatedCubic_monomial_bounds (C₀ C₁ F₀ F₁ F₂ X Y : ℝ≥0∞) :
    C₀ * (F₀ * X + F₁ * Y) * X * X ≤ separatedCubicBoundRhs C₀ C₁ F₀ F₁ F₂ X Y ∧
    X * (F₀ * (C₀ * X + C₁ * Y) * X) ≤ separatedCubicBoundRhs C₀ C₁ F₀ F₁ F₂ X Y ∧
    X * (C₀ * Y) * (F₁ * X + F₂ * Y) ≤ separatedCubicBoundRhs C₀ C₁ F₀ F₁ F₂ X Y := by
  let A := C₀ * F₀ * X ^ 3
  let B := C₀ * F₁ * Y * X ^ 2
  let C := C₁ * F₀ * Y * X ^ 2
  let D := C₀ * F₂ * Y ^ 2 * X
  have eq : separatedCubicBoundRhs C₀ C₁ F₀ F₁ F₂ X Y = (A + B) + (C + D) := by
    dsimp only [separatedCubicBoundRhs, A, B, C, D]
    ring
  rw [eq]
  constructor
  · calc
      _ = A + B := by dsimp only [A, B]; ring
      _ ≤ _ := le_add_of_nonneg_right (zero_le _)
  constructor
  · calc
      _ = A + C := by dsimp only [A, C]; ring
      _ ≤ _ := add_le_add (le_add_of_nonneg_right (zero_le _)) (le_add_of_nonneg_right (zero_le _))
  · calc
      _ = B + D := by dsimp only [B, D]; ring
      _ ≤ _ := add_le_add (le_add_of_nonneg_left (zero_le _)) (le_add_of_nonneg_left (zero_le _))

/-- The cubic action uses the same field in all three slots and the actual
separated Fourier test. The constant precedes the symbol and all test data. -/
theorem separated_principal_variation_bound {J : Type} [Fintype J] :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) →
      (∀ ξ, b (-ξ) = -b ξ) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (f : SchwartzMap E ℂ) (C : Index → Index → J → J → J → SchwartzMap E ℂ)
        (z : J → SchwartzMap E ℂ) (C₀ C₁ : ℝ≥0∞),
      (∀ a d i j k, eLpNorm (C a d i j k : E → ℂ) ⊤ volume ≤ C₀) →
      (∀ a d i j k l, eLpNorm (energyPartial l (C a d i j k) : E → ℂ) ⊤ volume ≤ C₁) →
      (∀ x, conj (f x) = f x) → (∀ a d i j k, C a d i j k = C d a i k j) →
      (∀ j x, conj (z j x) = z j x) →
      let X := euclideanFieldGradientNorm z
      let Y := eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume
      let F₀ := eLpNorm (f : E → ℂ) ⊤ volume
      let F₁ := eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume
      let F₂ := eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume
      ‖∫ x, principalVariationDensity (fun a d i j k => C a d i j k) z
          (fun i => separatedSkewAction f b (z i)) x‖ₑ ≤
        K * ENNReal.ofReal D * separatedCubicBoundRhs C₀ C₁ F₀ F₁ F₂ X Y := by
  classical
  obtain ⟨Kt, hKt, testBounds⟩ := separated_skew_field_L3_euclidean_sphere_bounds (J := J)
  obtain ⟨Kr, hKr, commutatorBound⟩ := separated_skew_coefficient_commutator_L32_sphere_bound
  let T := Index × J
  let S := T × T
  let M : ℝ≥0∞ := Fintype.card J
  let N : ℝ≥0∞ := Fintype.card S
  let L : ℝ≥0∞ := (Fintype.card Index : ℝ≥0∞) * M
  let Kslot := Kt + Kr * L + Kt * M
  let count := N * M + N + 2 * N
  have hM : M < ⊤ := by simp [M]
  have hN : N < ⊤ := by simp [N]
  have hL : L < ⊤ := ENNReal.mul_lt_top (by simp) hM
  have hKslot : Kslot < ⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨hKt, ENNReal.mul_lt_top hKr hL⟩, ENNReal.mul_lt_top hKt hM⟩
  have hcount : count < ⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hN hM, hN⟩, ENNReal.mul_lt_top (by simp) hN⟩
  refine ⟨count * Kslot, ENNReal.mul_lt_top hcount hKslot, ?_⟩
  intro b hb hom hodd D hD jet f C z C₀ C₁ hC₀ hC₁ hf symm hz X Y F₀ F₁ F₂
  let P := ENNReal.ofReal 3
  let W := ENNReal.ofReal D
  let A := separatedCubicBoundRhs C₀ C₁ F₀ F₁ F₂ X Y
  let B := Kslot * W * A
  let U (i : T) := energyPartial i.1 (z i.2)
  let Qz (i : J) := separatedSkewAction f b (z i)
  let R (p : S) := principalCoefficientContraction C z p
  let H (i : T) := separatedSkewAction (energyPartial i.1 f) b (z i.2)
  let V (p : S) (i : J) (x : E) := C p.1.1 p.2.1 i p.1.2 p.2.2 x *
    (Qz i x * U p.1 x * U p.2 x)
  let Lr (p : S) (x : E) := U p.1 x * separatedSkewCommutator f b (R p) (U p.2) x
  let Ld (p : S) (x : E) := U p.1 x * R p x * H p.2 x
  have Kvalue : Kt ≤ Kslot :=
    (le_add_of_nonneg_right (zero_le (Kr * L))).trans (le_add_of_nonneg_right (zero_le (Kt * M)))
  have Kcomm : Kr * L ≤ Kslot :=
    (le_add_of_nonneg_left (zero_le Kt)).trans (le_add_of_nonneg_right (zero_le (Kt * M)))
  have Kdiff : Kt * M ≤ Kslot := le_add_of_nonneg_left (zero_le (Kt + Kr * L))
  obtain ⟨monoV, monoR, monoD⟩ := separatedCubic_monomial_bounds C₀ C₁ F₀ F₁ F₂ X Y
  obtain ⟨_, hU, _⟩ := separated_field_component_L3_bounds z
  obtain ⟨⟨hvLp, hvSum⟩, hDiff⟩ := testBounds b hb hom D hD jet f z
  have qzBound (i : J) : eLpNorm (Qz i) P volume ≤ Kt * W * (F₀ * X + F₁ * Y) :=
    (Finset.single_le_sum (fun j _ => zero_le (eLpNorm (Qz j) P volume)) (Finset.mem_univ i)).trans hvSum
  have diffBound (p : T) : MemLp (H p) P volume ∧
      eLpNorm (H p) P volume ≤ Kt * W * (F₁ * X + F₂ * Y) := by
    let Diff (i : J) (x : E) := fderiv ℝ (Qz i) x (EuclideanSpace.single p.1 1) -
      separatedSkewAction f b (energyPartial p.1 (z i)) x
    have eq : Diff p.2 = H p := funext (fun x =>
      (separated_skew_coordinate_commutator f b hb hom (z p.2) x p.1).2)
    obtain ⟨hmem, hsum⟩ := hDiff p.1
    rw [← eq]
    refine ⟨hmem p.2, ?_⟩
    exact (Finset.single_le_sum (fun i _ => zero_le (eLpNorm (Diff i) P volume))
      (Finset.mem_univ p.2)).trans hsum
  have rBound (p : S) := principalCoefficientContraction_value_and_gradient_L3_bound C z C₀ C₁ hC₀ hC₁ p
  have valueTerm (p : S) (i : J) : Integrable (V p i) ∧ ‖∫ x, V p i x‖ₑ ≤ B := by
    let c := C p.1.1 p.2.1 i p.1.2 p.2.2
    have hq : MemLp (Qz i) P volume := hvLp i
    have hcq : MemLp (fun x => c x * Qz i x) P volume := hq.mul' (c.memLp ⊤ volume)
    have hcqNorm : eLpNorm (fun x => c x * Qz i x) P volume ≤
        eLpNorm (c : E → ℂ) ⊤ volume * eLpNorm (Qz i) P volume :=
      eLpNorm_smul_le_mul_eLpNorm (φ := (c : E → ℂ)) (f := Qz i) (p := ⊤) (q := P) (r := P)
        hq.1 c.continuous.aestronglyMeasurable
    have eq : V p i = fun x => c x * Qz i x * U p.1 x * U p.2 x := by
      funext x
      simp only [V, c, mul_assoc]
    rw [eq]
    obtain ⟨hi, hiNorm⟩ := energy_integral_three_factors hcq ((U p.1).memLp P volume) ((U p.2).memLp P volume)
    refine ⟨hi, hiNorm.trans ?_⟩
    calc
      _ ≤ (C₀ * (Kt * W * (F₀ * X + F₁ * Y))) * X * X :=
        mul_le_mul' (mul_le_mul' (hcqNorm.trans (mul_le_mul' (hC₀ _ _ _ _ _) (qzBound i))) (hU p.1))
          (hU p.2)
      _ = Kt * W * (C₀ * (F₀ * X + F₁ * Y) * X * X) := by ring
      _ ≤ B := mul_le_mul' (mul_le_mul_right' Kvalue W) monoV
  have commutatorTerm (p : S) : ‖∫ x, Lr p x‖ₑ ≤ B := by
    obtain ⟨hm, hbnd⟩ := commutatorBound b hb hom D hD jet f (R p) (U p.2)
    have hPair := (energy_integral_three_three_halves ((U p.1).memLp P volume) hm).2
    refine hPair.trans (mul_le_mul_left' hbnd _ |>.trans ?_)
    calc
      _ ≤ X * (Kr * W * (F₀ * (L * (C₀ * X + C₁ * Y)) * X)) :=
        mul_le_mul' (hU p.1) (mul_le_mul_left'
          (mul_le_mul' (mul_le_mul_left' (rBound p).2 F₀) (hU p.2)) _)
      _ = (Kr * L) * W * (X * (F₀ * (C₀ * X + C₁ * Y) * X)) := by ring
      _ ≤ B := mul_le_mul' (mul_le_mul_right' Kcomm W) monoR
  have differentialTerm (p : S) : ‖∫ x, Ld p x‖ₑ ≤ B := by
    have hPair := (energy_integral_three_factors ((U p.1).memLp P volume)
      ((R p).memLp P volume) (diffBound p.2).1).2
    refine hPair.trans ?_
    calc
      _ ≤ X * (M * (C₀ * Y)) * (Kt * W * (F₁ * X + F₂ * Y)) :=
        mul_le_mul' (mul_le_mul' (hU p.1) (rBound p).1) (diffBound p.2).2
      _ = (Kt * M) * W * (X * (C₀ * Y) * (F₁ * X + F₂ * Y)) := by ring
      _ ≤ B := mul_le_mul' (mul_le_mul_right' Kdiff W) monoD
  have sum_bound {ι : Type} [Fintype ι] (v : ι → ℂ) (d : ℝ≥0∞)
      (hv : ∀ i, ‖v i‖ₑ ≤ d) :
      ‖∑ i, v i‖ₑ ≤ (Fintype.card ι : ℝ≥0∞) * d := by
    calc
      _ ≤ ∑ i, ‖v i‖ₑ := enorm_sum_le _ _
      _ ≤ ∑ _i : ι, d := Finset.sum_le_sum (fun i _ => hv i)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hV (p : S) : ‖∫ x, ∑ i, V p i x‖ₑ ≤ M * B := by
    rw [integral_finset_sum Finset.univ (fun i _ => (valueTerm p i).1)]
    exact sum_bound (fun i => ∫ x, V p i x) B (fun i => (valueTerm p i).2)
  have vTotal : ‖∫ x, ∑ p : S, ∑ i, V p i x‖ₑ ≤ N * M * B := by
    rw [integral_finset_sum Finset.univ (fun p _ =>
      integrable_finset_sum Finset.univ (fun i _ => (valueTerm p i).1)), mul_assoc]
    exact sum_bound (fun p : S => ∫ x, ∑ i, V p i x) (M * B) hV
  have rTotal : ‖∑ p : S, ∫ x, Lr p x‖ₑ ≤ N * B := sum_bound _ _ commutatorTerm
  have dTotal : ‖∑ p : S, ∫ x, Ld p x‖ₑ ≤ N * B := sum_bound _ _ differentialTerm
  have eq := separated_principal_variation_formula f b hb hom hf hodd C z symm hz
  change (∫ x, principalVariationDensity (fun a d i j k => C a d i j k) z Qz x) =
    (∫ x, ∑ p : S, ∑ i, V p i x) - (∑ p : S, ∫ x, Lr p x) + 2 * (∑ p : S, ∫ x, Ld p x) at eq
  rw [eq]
  have hsub (u v : ℂ) : ‖u - v‖ₑ ≤ ‖u‖ₑ + ‖v‖ₑ := by
    simpa only [sub_eq_add_neg, enorm_neg] using (enorm_add_le u (-v))
  calc
    _ ≤ (‖∫ x, ∑ p : S, ∑ i, V p i x‖ₑ + ‖∑ p : S, ∫ x, Lr p x‖ₑ) +
        2 * ‖∑ p : S, ∫ x, Ld p x‖ₑ := by
      refine (enorm_add_le _ _).trans (add_le_add (hsub _ _) ?_)
      simp [enorm_eq_nnnorm]
    _ ≤ (N * M * B + N * B) + 2 * (N * B) :=
      add_le_add (add_le_add vTotal rTotal) (mul_le_mul_left' dTotal 2)
    _ = _ := by dsimp only [count, B, W, A]; ring

end Burnett.A02.FrequencySplit
