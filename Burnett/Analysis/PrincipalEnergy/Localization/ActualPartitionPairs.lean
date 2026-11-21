import Burnett.Analysis.PrincipalEnergy.Localization.FiniteFarPairing

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Burnett.Analysis.FirstOrderDyadic
open scoped NNReal FourierTransform ComplexConjugate BigOperators

/-- The actual Fourier integral on Schwartz inputs is bounded and continuous
under the frequency order bound and joint continuity of the symbol. -/
theorem firstOrderAction_continuous_and_bounded {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hCont : Continuous (Function.uncurry a))
    (f : SchwartzMap Space ℂ) :
    Continuous (firstOrderAction a f) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖firstOrderAction a f x‖ ≤ M := by
  obtain ⟨A, hA, hAorder⟩ := ha.order 0
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let P (x ξ : Space) : ℂ := Real.fourierChar (inner ℝ ξ x) • (a x ξ * F ξ)
  let D (ξ : Space) : ℝ := A * ((1 + ‖ξ‖) * ‖F ξ‖)
  have hD : Integrable D := by
    simpa only [D, add_mul, one_mul, pow_one] using
      (F.integrable.norm.add (F.integrable_pow_mul (volume : Measure Space) 1)).const_mul A
  have hDp (ξ : Space) : 0 ≤ D ξ := by dsimp only [D]; positivity
  have hDom (x ξ : Space) : ‖P x ξ‖ ≤ D ξ := by
    have ha₀ : ‖a x ξ‖ ≤ A * (1 + ‖ξ‖) := by
      simpa only [pow_zero, mul_one, norm_iteratedFDeriv_zero] using hAorder x ξ
    change ‖Real.fourierChar (inner ℝ ξ x) • (a x ξ * F ξ)‖ ≤ A * ((1 + ‖ξ‖) * ‖F ξ‖)
    rw [Circle.norm_smul, norm_mul, ← mul_assoc A]
    exact mul_le_mul_of_nonneg_right ha₀ (norm_nonneg _)
  have hIntegral (x : Space) : firstOrderAction a f x = ∫ ξ, P x ξ := by
    rw [firstOrderAction, Real.fourierIntegralInv_eq]
    rfl
  have hMeas (x : Space) : AEStronglyMeasurable (P x) (volume : Measure Space) :=
    ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
      (((ha.smooth x).continuous).mul F.continuous)).aestronglyMeasurable
  have hX (ξ : Space) : Continuous (fun x => P x ξ) :=
    (Real.continuous_fourierChar.comp (continuous_const.inner continuous_id)).smul
      ((hCont.comp (continuous_id.prodMk continuous_const)).mul continuous_const)
  refine ⟨?_, ∫ ξ, D ξ, integral_nonneg hDp, ?_⟩
  · rw [show firstOrderAction a f = (fun x => ∫ ξ, P x ξ) from funext hIntegral]
    exact continuous_of_dominated hMeas (fun x => .of_forall (hDom x)) hD (.of_forall hX)
  · intro x
    rw [hIntegral]
    exact norm_integral_le_of_norm_le hD (.of_forall (hDom x))

/-- Actual tested pairings are integrable without a compact-base restriction
on the symbol. -/
theorem integrable_actualScalarCommutatorPair {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hc : Continuous (Function.uncurry a))
    (r f g : SchwartzMap Space ℂ) :
    Integrable (fun x => conj (g x) * actualCoefficientCommutator a r f x) := by
  obtain ⟨hf, A, _, hA⟩ := firstOrderAction_continuous_and_bounded ha hc f
  obtain ⟨hrf, B, _, hB⟩ := firstOrderAction_continuous_and_bounded ha hc (scalarSchwartzProduct r f)
  have hT : Continuous (actualCoefficientCommutator a r f) := (r.continuous.mul hf).sub hrf
  have hBound : ∃ C : ℝ, ∀ x, ‖actualCoefficientCommutator a r f x‖ ≤ C := by
    refine ⟨SchwartzMap.seminorm ℝ 0 0 r * A + B, ?_⟩
    intro x
    unfold actualCoefficientCommutator
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hB x))
    rw [norm_mul]
    exact mul_le_mul (SchwartzMap.norm_le_seminorm ℝ r x) (hA x) (norm_nonneg _) (apply_nonneg _ _)
  have hConj : Integrable (fun x => conj (g x)) (volume : Measure Space) :=
    g.integrable.norm.mono' (Complex.continuous_conj.comp g.continuous).aestronglyMeasurable
      (.of_forall fun x => (Complex.norm_conj (g x)).le)
  simpa only [mul_comm] using hConj.bdd_mul hT.aestronglyMeasurable hBound

private def firstOrderActionAddHom (a : Space → Space → ℂ) (ha : FrequencyOrderOne a) (x : Space) :
    SchwartzMap Space ℂ →+ ℂ := by
  let T (f : SchwartzMap Space ℂ) := firstOrderAction a f x
  have hSub (f g : SchwartzMap Space ℂ) : T (f-g) = T f - T g := by
    simpa only [one_smul, one_mul] using firstOrderAction_sub_smul a ha x f g 1
  have hZero : T 0 = 0 := by simpa only [sub_zero, sub_self] using hSub 0 0
  have hNeg (f : SchwartzMap Space ℂ) : T (-f) = -T f := by
    simpa only [zero_sub, hZero] using hSub 0 f
  exact {
    toFun := T
    map_zero' := hZero
    map_add' := fun f g => by simpa only [sub_neg_eq_add, hNeg] using hSub f (-g)
  }

private def schwartzProductAddHom (r : SchwartzMap Space ℂ) : SchwartzMap Space ℂ →+ SchwartzMap Space ℂ where
  toFun := scalarSchwartzProduct r
  map_zero' := by ext x; simp [scalarSchwartzProduct_apply]
  map_add' f g := by
    ext x
    simp only [scalarSchwartzProduct_apply, SchwartzMap.add_apply, mul_add]

private def actualCoefficientCommutatorAddHom (a : Space → Space → ℂ) (ha : FrequencyOrderOne a)
    (r : SchwartzMap Space ℂ) (x : Space) : SchwartzMap Space ℂ →+ ℂ where
  toFun f := actualCoefficientCommutator a r f x
  map_zero' := by
    change r x * firstOrderActionAddHom a ha x 0 -
      firstOrderActionAddHom a ha x (schwartzProductAddHom r 0) = 0
    rw [map_zero, map_zero, map_zero, mul_zero, sub_zero]
  map_add' f g := by
    change r x * firstOrderActionAddHom a ha x (f+g) -
      firstOrderActionAddHom a ha x (schwartzProductAddHom r (f+g)) =
      (r x * firstOrderActionAddHom a ha x f -
        firstOrderActionAddHom a ha x (schwartzProductAddHom r f)) +
      (r x * firstOrderActionAddHom a ha x g -
        firstOrderActionAddHom a ha x (schwartzProductAddHom r g))
    simp only [map_add, mul_add]
    ring

private theorem commutator_sum_apply {ι : Type*} (s : Finset ι) (a : Space → Space → ℂ)
    (ha : FrequencyOrderOne a) (r : SchwartzMap Space ℂ) (f : ι → SchwartzMap Space ℂ) (x : Space) :
    actualCoefficientCommutator a r (∑ j ∈ s, f j) x = ∑ j ∈ s, actualCoefficientCommutator a r (f j) x :=
  map_sum (actualCoefficientCommutatorAddHom a ha r x) f s

private theorem schwartz_sum_eval {ι : Type*} (s : Finset ι) (f : ι → SchwartzMap Space ℂ) (x : Space) :
    (∑ j ∈ s, f j) x = ∑ j ∈ s, f j x := by
  let E : SchwartzMap Space ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun g => g x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact map_sum E f s

/-- Exact finite summation after cutting one actual field. The partition
identity is only needed where the input itself is nonzero. -/
theorem sum_scalarSchwartzProduct_eq {ι : Type*} [Fintype ι]
    (α : ι → SchwartzMap Space ℂ) (f : SchwartzMap Space ℂ)
    (hOne : ∀ x, f x ≠ 0 → ∑ i, α i x = 1) :
    (∑ i, scalarSchwartzProduct (α i) f) = f := by
  ext x
  rw [schwartz_sum_eval]
  simp only [scalarSchwartzProduct_apply, ← Finset.sum_mul]
  by_cases hx : f x = 0
  · simp only [hx, mul_zero]
  · rw [hOne x hx, one_mul]

/-- Exact expansion of the actual scalar pairing on finite sums, with
integrability checked for all original tested integrands. -/
theorem actualScalarCommutatorPair_sum_sum {ι : Type*} [Fintype ι]
    {a : Space → Space → ℂ} (ha : FrequencyOrderOne a) (hc : Continuous (Function.uncurry a))
    (r : SchwartzMap Space ℂ) (F G : ι → SchwartzMap Space ℂ) :
    actualScalarCommutatorPair a r (∑ j, F j) (∑ i, G i) =
      ∑ e : ι × ι, actualScalarCommutatorPair a r (F e.2) (G e.1) := by
  let H (e : ι × ι) (x : Space) :=
    conj (G e.1 x) * actualCoefficientCommutator a r (F e.2) x
  have hInt (e : ι × ι) : Integrable (H e) := integrable_actualScalarCommutatorPair ha hc r (F e.2) (G e.1)
  change (∫ x, conj ((∑ i, G i) x) * actualCoefficientCommutator a r (∑ j, F j) x) =
    ∑ e : ι × ι, ∫ x, H e x
  rw [← integral_finset_sum Finset.univ (fun e _ => hInt e)]
  apply integral_congr_ae
  filter_upwards with x
  rw [schwartz_sum_eval, map_sum, commutator_sum_apply _ a ha, ← Finset.univ_product_univ,
    Finset.sum_product, Finset.sum_mul]
  simp only [Finset.mul_sum, H]

end Burnett.Analysis.CarlesonEmbedding
