import Burnett.Analysis.PrincipalEnergy.Localization.UniformCompactMatrixPair
import Burnett.Analysis.PrincipalEnergy.Commutator.SchwartzCoordinateJet

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter BoundedContinuousFunction Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic Burnett.Analysis.SymmetricEnergy
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open scoped ContDiff ComplexConjugate InnerProductSpace

/-- The actual compact-base action bound in the coordinate H¹ pairing. -/
theorem exists_compactBase_firstOrderAction_h1_pair_bound {a : Space → Space → ℂ}
    (ha : CompactBaseOrderOne a) (hc : Continuous (uncurry a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : SchwartzMap Space ℂ,
      ‖∫ x, conj (g x) * firstOrderAction a f x‖ ≤
        C * coordinateH1 f * ‖g.toLp 2 volume‖ := by
  obtain ⟨C, hC, bound⟩ := exists_compactBase_firstOrderAction_h1_to_l2 ha hc
  refine ⟨C, hC, fun f g => ?_⟩
  obtain ⟨hT, hb⟩ := bound f
  let T := hT.toLp (firstOrderAction a f)
  have hEnergy : 0 ≤ schwartzH1Energy f := add_nonneg (sq_nonneg _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hH : 0 ≤ coordinateH1 f := Real.sqrt_nonneg _
  have hT' : ‖T‖ ≤ C * coordinateH1 f := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC hH)).mp
    rw [mul_pow, show coordinateH1 f = Real.sqrt (schwartzH1Energy f) from rfl, Real.sq_sqrt hEnergy]
    exact hb
  have hI : ⟪g.toLp 2 volume, T⟫_ℂ = ∫ x, conj (g x) * firstOrderAction a f x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [g.coeFn_toLp 2 volume, MemLp.coeFn_toLp hT] with x hg hx
    change inner ℂ ((g.toLp 2 volume) x) ((hT.toLp _) x) = _
    rw [hg, hx, RCLike.inner_apply']
  rw [← hI]
  exact ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hT' (norm_nonneg _))).trans_eq
    (mul_comm _ _)

/-- A common compact support and the verified derivative bounds give one
coordinate H¹-to-L² tested bound for the whole family. -/
theorem exists_uniformCompactSymbolFamily_h1_pair_bound {ι : Type*} {a : ι → Space → Space → ℂ}
    (ha : UniformCompactSymbolFamily a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (f g : SchwartzMap Space ℂ),
      ‖∫ x, conj (g x) * firstOrderAction (a n) f x‖ ≤
        C * coordinateH1 f * ‖g.toLp 2 volume‖ := by
  let X := SchwartzMap Space ℂ × SchwartzMap Space ℂ
  let V (α : Space → Space → ℂ) (t : X) := ∫ x, conj (t.2 x) * firstOrderAction α t.1 x
  let W (t : X) := coordinateH1 t.1 * ‖t.2.toLp 2 volume‖
  have hW (t : X) : 0 ≤ W t := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  let F (n : ι) (t : X) : ℂ := V (a n) t / (W t : ℂ)
  have hFixed (t : X) : ∃ M : ℝ, ∀ n, ‖F n t‖ ≤ M := by
    obtain ⟨M, _, hM⟩ := uniformCompactSymbolFamily_action_bound ha t.1
    refine ⟨(M * (∫ x, ‖t.2 x‖)) / W t, fun n => ?_⟩
    rw [show F n t = V (a n) t / (W t : ℂ) from rfl,
      norm_div, Complex.norm_real, Real.norm_of_nonneg (hW t)]
    apply div_le_div_of_nonneg_right _ (hW t)
    change ‖∫ x, conj (t.2 x) * firstOrderAction (a n) t.1 x‖ ≤ _
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (t.2.integrable.norm.const_mul M)
    filter_upwards with x
    rw [norm_mul, Complex.norm_conj, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM n x) (norm_nonneg _)
  have compact_bound {b : Space → Space → ℂ} (hb : CompactBaseOrderOne b)
      (hc : Continuous (uncurry b)) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖V b t‖ ≤ C * W t := by
    obtain ⟨C, hC, h⟩ := exists_compactBase_firstOrderAction_h1_pair_bound hb hc
    refine ⟨C, hC, fun t => ?_⟩
    simpa only [V, W, mul_assoc] using h t.1 t.2
  have hSuper (c : ℕ → ι) (v : ℕ →ᵇ ℝ) : ∃ M : ℝ, ∀ t,
      ‖∑' n, ((((1 : ℝ)/2)^n) * v n) • F (c n) t‖ ≤ M := by
    let u (n : ℕ) := (((1 : ℝ)/2)^n) * v n
    have hg : Summable (fun n : ℕ => ((1 : ℝ)/2)^n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hu : Summable (fun n => ‖u n‖) := by
      refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hg.mul_right ‖v‖)
      dsimp only [u]
      rw [norm_mul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (norm_coe_le_norm v n) (by positivity)
    let b := summableSymbolSum (fun n => a (c n)) u
    obtain ⟨_, hB, hCont⟩ := summableSymbolSum_compactBase_inputs (ha.reindex c) hu
    obtain ⟨C, hC, hb⟩ := compact_bound hB hCont
    refine ⟨C, fun t => ?_⟩
    have eq : V b t / (W t : ℂ) = ∑' n, u n • F (c n) t := by
      unfold V b
      rw [integral_pair_firstOrderAction_summableSymbolSum (ha.reindex c) hu, div_eq_mul_inv,
        real_weighted_tsum_mul]
      apply tsum_congr
      intro n
      rfl
    change ‖∑' n, u n • F (c n) t‖ ≤ C
    rw [← eq]
    by_cases h0 : W t = 0
    · simp only [h0, Complex.ofReal_zero, div_zero, norm_zero]
      exact hC
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hW t)]
      exact (div_le_iff₀ (lt_of_le_of_ne (hW t) (Ne.symm h0))).mpr (hb t)
  obtain ⟨C, hC, h⟩ := exists_uniform_symbol_family_bound_of_superpositions F hFixed hSuper
  refine ⟨C, hC, fun n f g => ?_⟩
  let t : X := (f,g)
  suffices h' : ‖V (a n) t‖ ≤ C * W t by
    simpa only [V, W, t, mul_assoc] using h'
  by_cases h0 : W t = 0
  · have hBase : CompactBaseOrderOne (a n) := by
      refine ⟨?_, ha.smoothBase n, fun k => ?_⟩
      · obtain ⟨K, hK, hS⟩ := ha.support
        exact ⟨K, hK, hS n⟩
      · obtain ⟨M, hM, hS⟩ := ha.pureBaseOrder k
        exact ⟨M, hM, hS n⟩
    obtain ⟨M, _, hM⟩ := compact_bound hBase (ha.jointlyContinuous n)
    simpa only [h0, mul_zero] using hM t
  · have hb := h n t
    rw [show F n t = V (a n) t / (W t : ℂ) from rfl,
      norm_div, Complex.norm_real, Real.norm_of_nonneg (hW t)] at hb
    exact (div_le_iff₀ (lt_of_le_of_ne (hW t) (Ne.symm h0))).mp hb

end Burnett.Analysis.CarlesonEmbedding
