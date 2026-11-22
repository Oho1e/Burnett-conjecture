import Burnett.Analysis.GaugeProjection.HodgePhysicalAction

set_option autoImplicit false
set_option maxHeartbeats 2900000

noncomputable section

namespace Burnett.P01

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A07 (coordinateDerivative)
open scoped BigOperators ENNReal NNReal

private abbrev l2 (u : E → ℂ) : ℝ≥0∞ := eLpNorm u 2 volume

/-- The sum of the four component \(L^2\) norms. -/
def hodgeL2Mass (w : HodgeSchwartzField) : ℝ≥0∞ := ∑ i, l2 (w i)

private theorem hodgeL2Mass_le (w : HodgeSchwartzField) (M : ℝ≥0∞)
    (hM : ∀ i, l2 (w i) ≤ M) : hodgeL2Mass w ≤ 4 * M := by
  unfold hodgeL2Mass
  calc
    _ ≤ ∑ _ : Fin 4, M := Finset.sum_le_sum (fun j _ => hM j)
    _ = _ := by simp [nsmul_eq_mul]

private theorem hodgeL2Mass_component_le (w : HodgeSchwartzField) (i : Fin 4) :
    l2 (w i) ≤ hodgeL2Mass w := by
  unfold hodgeL2Mass
  exact Finset.single_le_sum (f := fun j : Fin 4 => l2 (w j))
    (fun _ _ => zero_le _) (Finset.mem_univ i)

private theorem hodgeTransverseAction_memLp (w : HodgeSchwartzField) (i : Fin 4) :
    MemLp (hodgeTransverseAction w i) 2 volume := by
  have eq : hodgeTransverseAction w i = ∑ j, radianAction (directionProjectionEntry i j) (w j) := by
    funext x
    simp only [hodgeTransverseAction, Finset.sum_apply]
  rw [eq]
  apply memLp_finset_sum' Finset.univ
  intro j _
  have h := (radianActionSpectrum_degreeZero_data _ (directionProjectionEntry_contDiffOn i j)
    (directionProjectionEntry_scale i j) (w j)).2.2 2 (by norm_num)
  rw [radianActionSpectrum_inverse] at h
  simpa using h

private theorem hodgeLongitudinalAction_memLp (w : HodgeSchwartzField) (i : Fin 4) :
    MemLp (hodgeLongitudinalAction w i) 2 volume :=
  ((w i).memLp 2 volume).sub (hodgeTransverseAction_memLp w i)

private theorem exists_hodgeTransverse_l2_bound :
    ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ (w : HodgeSchwartzField) (i : Fin 4),
      l2 (hodgeTransverseAction w i) ≤ D * hodgeL2Mass w := by
  have h (i j : Fin 4) := homogeneous_multiplier_Schwartz_bound
    (directionProjectionEntry i j) (directionProjectionEntry_contDiffOn i j)
    (directionProjectionEntry_scale i j) 2 (by norm_num)
  choose C finite bound using h
  let D := ∑ i, ∑ j, C i j
  have hD : D < ⊤ := ENNReal.sum_lt_top.mpr fun i _ => ENNReal.sum_lt_top.mpr fun j _ => finite i j
  have each (i j : Fin 4) : C i j ≤ D := by
    have hrow : C i j ≤ ∑ k, C i k :=
      Finset.single_le_sum (f := C i) (fun _ _ => zero_le _) (Finset.mem_univ j)
    exact hrow.trans (Finset.single_le_sum (f := fun r : Fin 4 => ∑ k, C r k)
      (fun _ _ => zero_le _) (Finset.mem_univ i))
  refine ⟨D, hD, fun w i => ?_⟩
  let g (j : Fin 4) := radianAction (directionProjectionEntry i j) (w j)
  have mem (j : Fin 4) : MemLp (g j) 2 volume := by
    have e := (radianActionSpectrum_degreeZero_data _ (directionProjectionEntry_contDiffOn i j)
      (directionProjectionEntry_scale i j) (w j)).2.2 2 (by norm_num)
    rw [radianActionSpectrum_inverse] at e
    simpa [g] using e
  have eq : hodgeTransverseAction w i = ∑ j, g j := by
    funext x
    simp only [hodgeTransverseAction, Finset.sum_apply, g]
  rw [eq]
  calc
    _ ≤ ∑ j, l2 (g j) := eLpNorm_sum_le (fun j _ => (mem j).1) (by norm_num)
    _ ≤ ∑ j, D * l2 (w j) := Finset.sum_le_sum (fun j _ =>
      (by simpa [g] using bound i j (w j) :
        l2 (g j) ≤ C i j * l2 (w j)).trans (mul_le_mul_right' (each i j) _))
    _ = _ := by rw [hodgeL2Mass, Finset.mul_sum]

private theorem hodgeProduct_l2_le (f u : SchwartzMap E ℂ) (L : ℝ≥0)
    (hL : ∀ x, ‖f x‖ₑ ≤ (L : ℝ≥0∞)) :
    l2 (hodgeProduct f u) ≤ (L : ℝ≥0∞) * l2 u := by
  let c : ℂ := (L : ℝ)
  have hc : ‖c‖ₑ = (L : ℝ≥0∞) := by
    simp [c, enorm_eq_nnnorm, Complex.nnnorm_real]
  calc
    _ ≤ l2 (c • (u : E → ℂ)) := by
      apply eLpNorm_mono_enorm
      intro x
      simp only [hodgeProduct_apply, Pi.smul_apply, smul_eq_mul, enorm_mul, hc]
      exact mul_le_mul_right' (hL x) _
    _ = _ := by
      unfold l2
      rw [eLpNorm_const_smul, hc]

private theorem hodgeSkew_l2_le (b j i : Fin 4) (A : HodgeSchwartzField) :
    l2 (hodgeSkew b A j i) ≤ l2 (A i) + l2 (A j) := by
  by_cases hj : j = b <;> by_cases hi : i = b
  · simpa only [hodgeSkew, hj, hi, if_true, l2] using
      (eLpNorm_sub_le (A i).continuous.aestronglyMeasurable
        (A j).continuous.aestronglyMeasurable (p := (2 : ℝ≥0∞)) (by norm_num))
  · simp only [hodgeSkew, hj, hi, if_true, if_false, sub_zero]
    exact le_add_of_nonneg_right (zero_le _)
  · simp only [hodgeSkew, hj, hi, if_true, if_false, zero_sub]
    change eLpNorm (-(A j : E → ℂ)) 2 volume ≤ _
    rw [eLpNorm_neg]
    exact le_add_of_nonneg_left (zero_le _)
  · simp [hodgeSkew, hj, hi, l2]

/-- The actual differentiated commutator estimate on the Schwartz Hodge core.
Only the supremum of the four first derivatives enters the constant. -/
theorem exists_hodgeCommutator_action_l2_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (b : Fin 4) (f : SchwartzMap E ℂ) (w A : HodgeSchwartzField),
        (∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ)) →
        ∀ (L : ℝ≥0), (∀ j x, ‖coordinateDerivative j f x‖ₑ ≤ (L : ℝ≥0∞)) →
          ∀ i, eLpNorm (fun x =>
            hodgeTransverseAction (fun j => hodgeProduct f (coordinateDerivative b (w j))) i x -
              f x * hodgeTransverseAction (fun j => coordinateDerivative b (w j)) i x) 2 volume ≤
            C * (L : ℝ≥0∞) * hodgeL2Mass w := by
  obtain ⟨D, hD, P⟩ := exists_hodgeTransverse_l2_bound
  let C := D * (4 * (1 + D)) + (1 + D) * (16 * (2 * D))
  have h1D : 1 + D < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hD⟩
  have hC : C < ⊤ := by
    exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top hD (ENNReal.mul_lt_top (by norm_num) h1D),
        ENNReal.mul_lt_top h1D (ENNReal.mul_lt_top (by norm_num)
          (ENNReal.mul_lt_top (by norm_num) hD))⟩
  refine ⟨C, hC, fun b f w A hA L hL i => ?_⟩
  let W := hodgeL2Mass w
  let grad : HodgeSchwartzField := fun j => hodgeProduct (coordinateDerivative j f) ((w - A) b)
  let skew : HodgeSchwartzField := fun j => ∑ k, hodgeProduct (coordinateDerivative k f)
    (hodgeSkew b A k j)
  have hA_norm (j : Fin 4) : l2 (A j) ≤ D * W := by
    rw [← hodgeTransverseAction_eq_of_spectrum w A hA j]
    exact P w j
  have lift (u : HodgeSchwartzField) (j : Fin 4) :
      l2 (hodgeLongitudinalAction u j) ≤ (1 + D) * hodgeL2Mass u := by
    calc
      _ ≤ l2 (u j) + l2 (hodgeTransverseAction u j) :=
        eLpNorm_sub_le (u j).continuous.aestronglyMeasurable
          (hodgeTransverseAction_memLp u j).1 (by norm_num)
      _ ≤ hodgeL2Mass u + D * hodgeL2Mass u :=
        add_le_add (hodgeL2Mass_component_le u j) (P u j)
      _ = _ := by rw [add_mul, one_mul]
  have hC_norm : l2 ((w - A) b) ≤ (1 + D) * W := by
    calc
      _ ≤ l2 (w b) + l2 (A b) :=
        eLpNorm_sub_le (w b).continuous.aestronglyMeasurable
          (A b).continuous.aestronglyMeasurable (by norm_num)
      _ ≤ W + D * W := add_le_add (hodgeL2Mass_component_le w b) (hA_norm b)
      _ = _ := by rw [add_mul, one_mul]
  have hg : hodgeL2Mass grad ≤ 4 * ((L : ℝ≥0∞) * ((1 + D) * W)) :=
    hodgeL2Mass_le grad _ fun j =>
      (hodgeProduct_l2_le _ _ L (hL j)).trans (mul_le_mul_left' hC_norm _)
  have count (j : Fin 4) : l2 (skew j) ≤ 4 * ((L : ℝ≥0∞) * ((2 * D) * W)) := by
    let u (k : Fin 4) := hodgeProduct (coordinateDerivative k f) (hodgeSkew b A k j)
    have heq : ((skew j : SchwartzMap E ℂ) : E → ℂ) = ∑ k, (u k : E → ℂ) := by
      funext x
      let evaluation : SchwartzMap E ℂ →+ ℂ :=
        { toFun := fun v => v x, map_zero' := rfl, map_add' := fun _ _ => rfl }
      simp only [Finset.sum_apply]
      exact map_sum evaluation u Finset.univ
    rw [heq]
    calc
      _ ≤ ∑ k, l2 (u k) :=
        eLpNorm_sum_le (fun k _ => (u k).continuous.aestronglyMeasurable) (by norm_num)
      _ ≤ ∑ _ : Fin 4, (L : ℝ≥0∞) * ((2 * D) * W) := by
        apply Finset.sum_le_sum
        intro k _
        apply (hodgeProduct_l2_le _ _ L (hL k)).trans
        apply mul_le_mul_left'
        calc
          _ ≤ l2 (A j) + l2 (A k) := hodgeSkew_l2_le b k j A
          _ ≤ D * W + D * W := add_le_add (hA_norm j) (hA_norm k)
          _ = _ := by rw [two_mul, add_mul]
      _ = _ := by simp [nsmul_eq_mul]
  have hs : hodgeL2Mass skew ≤ 4 * (4 * ((L : ℝ≥0∞) * ((2 * D) * W))) :=
    hodgeL2Mass_le skew _ count
  simp_rw [hodgeCommutator_action b f w A hA i]
  change l2 (-hodgeTransverseAction grad i + hodgeLongitudinalAction skew i) ≤ C * (L : ℝ≥0∞) * W
  calc
    _ ≤ l2 (hodgeTransverseAction grad i) + l2 (hodgeLongitudinalAction skew i) := by
      simpa only [l2, eLpNorm_neg] using
        (eLpNorm_add_le (hodgeTransverseAction_memLp grad i).1.neg
          (hodgeLongitudinalAction_memLp skew i).1 (p := (2 : ℝ≥0∞)) (by norm_num))
    _ ≤ D * hodgeL2Mass grad + (1 + D) * hodgeL2Mass skew := add_le_add (P grad i) (lift skew i)
    _ ≤ D * (4 * ((L : ℝ≥0∞) * ((1 + D) * W))) +
        (1 + D) * (4 * (4 * ((L : ℝ≥0∞) * ((2 * D) * W)))) :=
      add_le_add (mul_le_mul_left' hg _) (mul_le_mul_left' hs _)
    _ = _ := by unfold C; ring

end Burnett.P01
