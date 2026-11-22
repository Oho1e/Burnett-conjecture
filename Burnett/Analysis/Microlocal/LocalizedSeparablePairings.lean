import Burnett.Analysis.Microlocal.SeparableSquareOperators

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.SeparablePairingLocalization

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.AngularCommutator Burnett.Microlocal.SeparablePositive
open scoped InnerProduct BigOperators Topology ComplexConjugate

abbrev Space := Burnett.X02.SobolevTestJet.Space

private theorem ae_coe_finset_sum {ι : Type} (s : Finset ι) (f : ι → ComplexL2 Space) :
    ((∑ i ∈ s, f i : ComplexL2 Space) : Space → ℂ) =ᵐ[volume]
      (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero (E := ℂ)
      (p := 2) (μ := (volume : Measure Space)))
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x h1 h2
      rw [h1]
      change f i x + (∑ j ∈ s, f j : ComplexL2 Space) x = _
      rw [h2]

/-- Pointwise square partition on the essential support resolves the actual physical L² operators. -/
theorem sum_squareCutoff_actions_eq_self {I : Type} [Fintype I]
    (K : Set Space) (χ : I → BoundedSymbol Space)
    (hχ : ∀ x ∈ K, (∑ i, conj (χ i x) * χ i x) = 1)
    (u : ComplexL2 Space) (hu : ∀ᵐ x ∂volume, x ∈ K ∨ u x = 0) :
    (∑ i, symbolCLM (conjugateSymbol (χ i)) (symbolCLM (χ i) u)) = u := by
  let T (i : I) := symbolCLM (conjugateSymbol (χ i)) (symbolCLM (χ i) u)
  have hT : ∀ᵐ x ∂volume, ∀ i, T i x = (conj (χ i x) * χ i x) * u x := by
    apply Filter.eventually_all.mpr
    intro i
    have h := symbolL2_ae (productSymbol (conjugateSymbol (χ i)) (χ i)) u
    change (symbolCLM (productSymbol (conjugateSymbol (χ i)) (χ i)) u : Space → ℂ)
      =ᵐ[volume] fun x => productSymbol (conjugateSymbol (χ i)) (χ i) x * u x at h
    simpa only [T, symbolCLM_product, productSymbol_apply, conjugateSymbol_apply] using h
  change (∑ i, T i) = u
  apply Lp.ext
  filter_upwards [ae_coe_finset_sum Finset.univ T, hT, hu] with x hs htx hux
  rw [hs]
  simp only [htx, ← Finset.sum_mul]
  rcases hux with hk | hz
  · rw [hχ x hk, one_mul]
  · simp [hz]

theorem inner_sum_squareCutoff {I : Type} [Fintype I]
    (K : Set Space) (χ : I → BoundedSymbol Space)
    (hχ : ∀ x ∈ K, (∑ i, conj (χ i x) * χ i x) = 1)
    (u v : ComplexL2 Space) (hu : ∀ᵐ x ∂volume, x ∈ K ∨ u x = 0) :
    (∑ i, inner ℂ (symbolCLM (χ i) u) (symbolCLM (χ i) v)) = inner ℂ u v := by
  calc
    _ = ∑ i, inner ℂ (symbolCLM (conjugateSymbol (χ i)) (symbolCLM (χ i) u)) v := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      simpa only [conjugateSymbol_conjugateSymbol] using
        (inner_symbolCLM_left (conjugateSymbol (χ i)) (symbolCLM (χ i) u) v)
    _ = _ := by rw [← sum_inner, sum_squareCutoff_actions_eq_self K χ hχ u hu]

theorem sum_norm_sq_squareCutoff {I : Type} [Fintype I]
    (K : Set Space) (χ : I → BoundedSymbol Space)
    (hχ : ∀ x ∈ K, (∑ i, conj (χ i x) * χ i x) = 1)
    (u : ComplexL2 Space) (hu : ∀ᵐ x ∂volume, x ∈ K ∨ u x = 0) :
    (∑ i, ‖symbolCLM (χ i) u‖ ^ 2) = ‖u‖ ^ 2 := by
  have h := congrArg Complex.re (inner_sum_squareCutoff K χ hχ u u hu)
  have hnorm (w : ComplexL2 Space) : (inner ℂ w w).re = ‖w‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (x := w)).symm
  simpa only [Complex.re_sum, hnorm] using h

private theorem symbolCLM_commute (a b : BoundedSymbol Space) (u : ComplexL2 Space) :
    symbolCLM a (symbolCLM b u) = symbolCLM b (symbolCLM a u) := by
  rw [← symbolCLM_product, ← symbolCLM_product]
  apply Lp.ext
  filter_upwards [symbolL2_ae (productSymbol a b) u, symbolL2_ae (productSymbol b a) u]
    with x ha hb
  change symbolL2 (productSymbol a b) u x = symbolL2 (productSymbol b a) u x
  rw [ha, hb, productSymbol_apply, productSymbol_apply, mul_comm (a x) (b x)]

theorem finiteSeparableOperator_cutoff_action {J : Type} [Fintype J]
    (a m : J → BoundedSymbol Space) (χ : BoundedSymbol Space) (u : ComplexL2 Space) :
    symbolCLM χ (finiteSeparableOperator a m u) =
      finiteSeparableOperator a m (symbolCLM χ u) -
        ∑ j, symbolCLM (a j) (cutoffCommutator (m j) χ u) := by
  simp only [finiteSeparableOperator, ContinuousLinearMap.sum_apply, map_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [separableOperator, ContinuousLinearMap.comp_apply,
    cutoffCommutator, ContinuousLinearMap.sub_apply, map_sub, sub_sub_cancel]
  exact symbolCLM_commute χ (a j) (fourierMultiplier (m j) u)

/-- The pairing with the operator in Lean's second slot localizes with an exact signed error. -/
theorem finiteSeparable_pairing_squareCutoff {I J : Type} [Fintype I] [Fintype J]
    (a m : J → BoundedSymbol Space) (K : Set Space) (χ : I → BoundedSymbol Space)
    (hχ : ∀ x ∈ K, (∑ i, conj (χ i x) * χ i x) = 1)
    (u : ComplexL2 Space) (hu : ∀ᵐ x ∂volume, x ∈ K ∨ u x = 0) :
    inner ℂ u (finiteSeparableOperator a m u) =
      (∑ i, inner ℂ (symbolCLM (χ i) u)
        (finiteSeparableOperator a m (symbolCLM (χ i) u))) -
      ∑ i, ∑ j, inner ℂ (symbolCLM (χ i) u)
        (symbolCLM (a j) (cutoffCommutator (m j) (χ i) u)) := by
  calc
    _ = ∑ i, inner ℂ (symbolCLM (χ i) u)
          (symbolCLM (χ i) (finiteSeparableOperator a m u)) :=
      (inner_sum_squareCutoff K χ hχ u _ hu).symm
    _ = _ := by
      simp only [finiteSeparableOperator_cutoff_action, inner_sub_right, inner_sum,
        Finset.sum_sub_distrib]

theorem squareCutoff_pairing_error_tendsto_zero {I J : Type} [Fintype I] [Fintype J]
    (a m : J → BoundedSymbol Space) (χ : I → BoundedSymbol Space)
    (u : ℕ → ComplexL2 Space) (B : ℝ) (hB : ∀ n, ‖u n‖ ≤ B)
    (hcomm : ∀ i j, Tendsto (fun n => cutoffCommutator (m j) (χ i) (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i, ∑ j, inner ℂ (symbolCLM (χ i) (u n))
      (symbolCLM (a j) (cutoffCommutator (m j) (χ i) (u n)))) atTop (𝓝 0) := by
  let e (i : I) (j : J) (n : ℕ) := cutoffCommutator (m j) (χ i) (u n)
  let q (i : I) (j : J) (n : ℕ) :=
    inner ℂ (symbolCLM (χ i) (u n)) (symbolCLM (a j) (e i j n))
  have hB₀ : 0 ≤ B := (norm_nonneg (u 0)).trans (hB 0)
  have hl (i : I) (j : J) : Tendsto (q i j) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hlim : Tendsto (fun n => ((χ i).bound * B * (a j).bound) * ‖e i j n‖) atTop (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using ((hcomm i j).norm.const_mul
        ((χ i).bound * B * (a j).bound))
    apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
    intro n
    have hx : ‖symbolCLM (χ i) (u n)‖ ≤ (χ i).bound * B :=
      (symbolL2_norm_le (χ i) (u n)).trans
        (mul_le_mul_of_nonneg_left (hB n) (χ i).bound_nonneg)
    have hy : ‖symbolCLM (a j) (e i j n)‖ ≤ (a j).bound * ‖e i j n‖ :=
      symbolL2_norm_le (a j) (e i j n)
    calc
      ‖q i j n‖ ≤ ‖symbolCLM (χ i) (u n)‖ * ‖symbolCLM (a j) (e i j n)‖ :=
        norm_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ((χ i).bound * B) * ((a j).bound * ‖e i j n‖) :=
        mul_le_mul hx hy (norm_nonneg _) (mul_nonneg (χ i).bound_nonneg hB₀)
      _ = _ := (mul_assoc _ _ _).symm
  have hs (i : I) : Tendsto (fun n => ∑ j, q i j n) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun j _ => hl i j)
  simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun i _ => hs i)

theorem finiteSeparable_pairing_minus_localized_tendsto_zero {I J : Type} [Fintype I] [Fintype J]
    (a m : J → BoundedSymbol Space) (K : Set Space) (χ : I → BoundedSymbol Space)
    (hχ : ∀ x ∈ K, (∑ i, conj (χ i x) * χ i x) = 1)
    (u : ℕ → ComplexL2 Space) (hu : ∀ n, ∀ᵐ x ∂volume, x ∈ K ∨ u n x = 0)
    (B : ℝ) (hB : ∀ n, ‖u n‖ ≤ B)
    (hcomm : ∀ i j, Tendsto (fun n => cutoffCommutator (m j) (χ i) (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => inner ℂ (u n) (finiteSeparableOperator a m (u n)) -
      ∑ i, inner ℂ (symbolCLM (χ i) (u n))
        (finiteSeparableOperator a m (symbolCLM (χ i) (u n)))) atTop (𝓝 0) := by
  have ht := (squareCutoff_pairing_error_tendsto_zero a m χ u B hB hcomm).neg
  rw [neg_zero] at ht
  apply ht.congr
  intro n
  rw [finiteSeparable_pairing_squareCutoff a m K χ hχ (u n) (hu n)]
  abel

end Burnett.Microlocal.SeparablePairingLocalization
