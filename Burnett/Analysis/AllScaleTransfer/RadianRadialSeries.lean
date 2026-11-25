import Burnett.Analysis.AllScaleTransfer.ActualRadialModeBound
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearModeSeries

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.A05

open Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight
  integrable_radianTrilinearWeight_of_bounded)
open scoped ENNReal RealInnerProductSpace Topology

private theorem annulus_indices (r : ℝ) :
    ∃ J : Finset ℤ, J.card ≤ 3 ∧
      ∀ j : ℤ, 1/2 < (2 : ℝ)^(-j) * r → (2 : ℝ)^(-j) * r < 2 → j ∈ J := by
  by_cases h : ∃ j : ℤ, 1/2 < (2 : ℝ)^(-j) * r ∧ (2 : ℝ)^(-j) * r < 2
  · obtain ⟨k, hk⟩ := h
    have hr : 0 ≤ r := by
      by_contra! hn
      have hneg := mul_nonpos_of_nonneg_of_nonpos
        (zpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (-k)) hn.le
      linarith only [hneg, hk.1]
    have close (i j : ℤ) (hi : (2 : ℝ)^(-i) * r < 2)
        (hj : 1/2 < (2 : ℝ)^(-j) * r) : j ≤ i + 1 := by
      by_contra! hfar
      have hexp : -j + 2 ≤ -i := by omega
      have hpow := zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hexp
      have hpow' : (4 : ℝ) * 2^(-j) ≤ 2^(-i) := by
        calc
          _ = (2 : ℝ)^(-j) * 2^(2 : ℤ) := by norm_num [mul_comm]
          _ = (2 : ℝ)^(-j + 2) := (zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) _ _).symm
          _ ≤ _ := hpow
      have hm := mul_le_mul_of_nonneg_right hpow' hr
      nlinarith only [hm, hi, hj]
    refine ⟨Finset.Icc (k - 1) (k + 1), ?_, ?_⟩
    · rw [Int.card_Icc]
      omega
    · intro j hj₁ hj₂
      refine Finset.mem_Icc.mpr ⟨?_, close k j hk.2 hj₁⟩
      have := close j k hj₂ hk.1
      omega
  · exact ⟨∅, by simp, fun j h₁ h₂ => (h ⟨j, h₁, h₂⟩).elim⟩

private def radialPhase (t : ℝ) : ℂ := Complex.exp ((↑(tau * t) : ℂ) * Complex.I)

private theorem radialPhase_norm (t : ℝ) : ‖radialPhase t‖ = 1 := by
  simp [radialPhase, Complex.norm_exp]

private theorem separated_formula (a b d : SchwartzMap E ℂ) (t u v : ℝ)
    (q r : E) (p : Joint) :
    radianSeparatedWindowSymbol a b d t u v q r p =
      (radialPhase (inner ℝ (t • (tau⁻¹ • p.1)) q) * a (t • (tau⁻¹ • p.1))) *
      (radialPhase (inner ℝ (u • (tau⁻¹ • p.2)) r) * b (u • (tau⁻¹ • p.2))) *
      d (v • (-((tau⁻¹ • p.1) + (tau⁻¹ • p.2)))) := rfl

/-- The integer-scale series is the actual Fourier integral of the summed
radial windows. Bounded pointwise annular overlap provides the integrable
majorant on the same two frequencies and keeps the third negative-sum slot. -/
theorem radianTrilinearForm_hasSum_of_radial_windows
    (a b d f g h : SchwartzMap E ℂ) (t u : ℝ) (ht : 0 < t) (v : ℤ → ℝ)
    (q r : E) (ha : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    let F (j : ℤ) := radianSeparatedWindowSymbol a b d
      ((2 : ℝ)^(-j) * t) ((2 : ℝ)^(-j) * u) (v j) q r
    HasSum (fun j => radianTrilinearForm (F j) f g h)
      (radianTrilinearForm (fun p => ∑' j, F j p) f g h) := by
  intro F
  let K := radianWeight (fun _ => 1) f g h
  have hone : radianTrilinearWeight (fun _ => (1 : ℂ)) f g h = K := by
    funext p
    change (1 : ℂ) * K p = K p
    exact one_mul _
  have hK : Integrable K := by
    rw [← hone]
    exact integrable_radianTrilinearWeight_of_bounded (fun _ => (1 : ℂ))
      aestronglyMeasurable_const 1 (fun p => norm_one.le) f g h
  let B := SchwartzMap.seminorm ℝ 0 0 a * SchwartzMap.seminorm ℝ 0 0 b *
    SchwartzMap.seminorm ℝ 0 0 d
  have hB : 0 ≤ B := by unfold B; positivity
  have hCont (j : ℤ) : Continuous (F j) := by
    change Continuous (fun p : Joint =>
      radianSeparatedWindowSymbol a b d ((2 : ℝ)^(-j) * t) ((2 : ℝ)^(-j) * u) (v j) q r p)
    simp only [separated_formula, radialPhase]
    fun_prop
  have hnorm (j : ℤ) (p : Joint) : ‖F j p‖ ≤ B := by
    simp only [F, separated_formula, norm_mul, radialPhase_norm, one_mul]
    exact mul_le_mul
      (mul_le_mul (a.norm_le_seminorm ℝ _) (b.norm_le_seminorm ℝ _) (norm_nonneg _) (apply_nonneg _ _))
      (d.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)
  have hLoc (p : Joint) : ∃ J : Finset ℤ, J.card ≤ 3 ∧ ∀ j ∉ J, F j p = 0 := by
    let ρ := t * ‖tau⁻¹ • p.1‖
    obtain ⟨J,hJ,hAnn⟩ := annulus_indices ρ
    refine ⟨J,hJ,?_⟩
    intro j hj
    by_contra hn
    have hn' : a (((2 : ℝ)^(-j) * t) • (tau⁻¹ • p.1)) ≠ 0 := by
      intro hz
      apply hn
      simp only [F, separated_formula, hz, mul_zero, zero_mul]
    have ha' := ha _ hn'
    rw [norm_smul, norm_mul, Real.norm_of_nonneg (zpow_nonneg (by norm_num) _),
      Real.norm_of_nonneg ht.le, mul_assoc] at ha'
    exact hj (hAnn j ha'.1 ha'.2)
  have hPartial (J : Finset ℤ) (p : Joint) : ‖∑ j ∈ J, F j p‖ ≤ 3 * B := by
    obtain ⟨I,hI,hZero⟩ := hLoc p
    have hEq : (∑ j ∈ J, F j p) = ∑ j ∈ J ∩ I, F j p := by
      classical
      refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
      intro j hj hn
      exact hZero j (fun hi => hn (Finset.mem_inter.mpr ⟨hj, hi⟩))
    rw [hEq]
    have hCard : (J ∩ I).card ≤ 3 := (Finset.card_le_card Finset.inter_subset_right).trans hI
    calc
      _ ≤ ∑ j ∈ J ∩ I, B := norm_sum_le_of_le _ (fun j _ => hnorm j p)
      _ = ((J ∩ I).card : ℝ) * B := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) hB
  have hInt (j : ℤ) : Integrable (radianTrilinearWeight (F j) f g h) :=
    integrable_radianTrilinearWeight_of_bounded (F j) (hCont j).aestronglyMeasurable B (hnorm j) f g h
  have hT : Tendsto (fun J : Finset ℤ => ∫ p, (∑ j ∈ J, F j p) * K p) atTop
      (𝓝 (∫ p, (∑' j, F j p) * K p)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p => (3 * B) * ‖K p‖)
    · exact Eventually.of_forall (fun J =>
        (J.aestronglyMeasurable_fun_sum (fun j _ => (hCont j).aestronglyMeasurable)).mul hK.1)
    · exact Eventually.of_forall (fun J => Eventually.of_forall (fun p => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hPartial J p) (norm_nonneg _)))
    · exact hK.norm.const_mul _
    · apply Eventually.of_forall
      intro p
      obtain ⟨I, _, hI⟩ := hLoc p
      have hsum : HasSum (fun j => F j p) (∑' j, F j p) :=
        (summable_of_ne_finset_zero hI).hasSum
      change Tendsto (fun J : Finset ℤ => ∑ j ∈ J, F j p) atTop (𝓝 (∑' j, F j p)) at hsum
      exact hsum.mul tendsto_const_nhds
  have hEq (J : Finset ℤ) : (∑ j ∈ J, radianTrilinearForm (F j) f g h) =
      (tau ^ 8)⁻¹ • ∫ p, (∑ j ∈ J, F j p) * K p := by
    unfold radianTrilinearForm
    rw [← Finset.smul_sum, ← integral_finset_sum _ (fun j _ => hInt j)]
    simp only [radianTrilinearWeight, K, Finset.sum_mul]
  change Tendsto (fun J : Finset ℤ => ∑ j ∈ J, radianTrilinearForm (F j) f g h) atTop _
  have hEqAll : (fun J : Finset ℤ => ∑ j ∈ J, radianTrilinearForm (F j) f g h) =
      (fun J : Finset ℤ => (tau ^ 8)⁻¹ • ∫ p, (∑ j ∈ J, F j p) * K p) := funext hEq
  rw [hEqAll]
  exact hT.const_smul ((tau ^ 8)⁻¹ : ℝ)

/-- The trilinear bound extends from arbitrary finite selections of
integer scales to the Fourier integral of the entire radial sum. -/
theorem integer_radial_mode_full_trilinear_bound
    (a b d : SchwartzMap E ℂ) (ha : HasCompactSupport (a : E → ℂ))
    (hb : HasCompactSupport (b : E → ℂ)) (ca : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (cb : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (t u : ℝ), 0 < t → 0 < u → ∀ (q r : E)
      (v : ℤ → ℝ), (∀ j, 0 < v j) → ∀ (f g h : SchwartzMap E ℂ),
        let F (j : ℤ) := radianSeparatedWindowSymbol a b d
          ((2 : ℝ)^(-j) * t) ((2 : ℝ)^(-j) * u) (v j) q r
        ‖radianTrilinearForm (fun p => ∑' j, F j p) f g h‖ₑ ≤
          C * ENNReal.ofReal (1 + ‖q‖) * ENNReal.ofReal (1 + ‖r‖) * triLpMass f g h 3 3 3 := by
  obtain ⟨C,hC,H⟩ := integer_radial_mode_trilinear_bound a b d ha hb ca cb
  refine ⟨C,hC,?_⟩
  intro t u ht hu q r v hv f g h F
  let T (j : ℤ) := radianTrilinearForm (F j) f g h
  have lim : HasSum T (radianTrilinearForm (fun p => ∑' j, F j p) f g h) :=
    radianTrilinearForm_hasSum_of_radial_windows a b d f g h t u ht v q r ca
  change Tendsto (fun J : Finset ℤ => ∑ j ∈ J, T j) atTop
    (𝓝 (radianTrilinearForm (fun p => ∑' j, F j p) f g h)) at lim
  apply le_of_tendsto' (continuous_enorm.continuousAt.tendsto.comp lim)
  intro J
  let n := Fintype.card (↑J : Type)
  let e : (↑J : Type) ≃ Fin n := Fintype.equivFin _
  let j : Fin n ↪ ℤ := e.symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have heq : (∑ k : Fin n, T (j k)) = ∑ k ∈ J, T k := by
    calc
      _ = ∑ k : (↑J : Type), T k.val := e.symm.sum_comp (fun k => T k.val)
      _ = _ := Finset.sum_attach J T
  simp only [Function.comp_apply]
  rw [← heq]
  exact H t u ht hu q r n j (fun k => v (j k)) (fun k => hv (j k)) f g h

end Burnett.A05
