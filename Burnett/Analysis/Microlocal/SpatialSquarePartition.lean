import Burnett.Analysis.Microlocal.RationalAngularSymbols
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.SmoothSquarePartition

open Set Filter Burnett.Microlocal.SmoothAngularTests
open scoped ContDiff Topology BigOperators ComplexConjugate

private theorem exists_subordinate_bumps
    (K : Set Space) (hK : IsCompact K) (U : Space → Set Space)
    (hU : ∀ x ∈ K, U x ∈ 𝓝 x) :
    ∃ (n : ℕ) (c : Fin n → Space) (b : ∀ i, ContDiffBump (c i)),
      (∀ i, c i ∈ K) ∧ (∀ i, tsupport (b i) ⊆ U (c i)) ∧
        (∀ x ∈ K, ∃ i, b i x = 1) := by
  classical
  choose r hr hsub using fun x : K => Metric.mem_nhds_iff.mp (hU x x.property)
  let B (x : K) : ContDiffBump (x : Space) :=
    ⟨r x / 4, r x / 2, by linarith [hr x], by linarith [hr x]⟩
  have hcover : K ⊆ ⋃ x : K, Metric.ball (x : Space) (B x).rIn := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (B ⟨x, hx⟩).rIn_pos⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball (x : Space) (B x).rIn) (fun _ => Metric.isOpen_ball) hcover
  let e := (Fintype.equivFin ↥s).symm
  refine ⟨Fintype.card ↥s, fun i => ((e i).1 : Space), fun i => B (e i).1,
    fun i => (e i).1.property, ?_, ?_⟩
  · intro i
    rw [(B (e i).1).tsupport_eq]
    exact (Metric.closedBall_subset_ball (show (B (e i).1).rOut < r (e i).1 by
      change r (e i).1 / 2 < r (e i).1
      linarith [hr (e i).1])).trans (hsub (e i).1)
  · intro x hx
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hys, hxy⟩ := mem_iUnion.mp hy
    obtain ⟨i, hi⟩ := e.surjective (⟨y, hys⟩ : ↥s)
    refine ⟨i, ?_⟩
    change B (e i).1 x = 1
    rw [hi]
    exact (B y).one_of_mem_closedBall (Metric.ball_subset_closedBall hxy)

private def regularizer : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

private theorem regularizer_zero_of_one_le {y : ℝ} (hy : 1 ≤ y) : regularizer y = 0 := by
  apply regularizer.zero_of_le_dist
  rw [Real.dist_0_eq_abs, abs_of_nonneg (zero_le_one.trans hy)]
  change (1 / 2 : ℝ) ≤ y
  linarith

private theorem regularizer_one_at_zero : regularizer 0 = 1 :=
  regularizer.one_of_mem_closedBall
    (Metric.mem_closedBall_self (le_of_lt regularizer.rIn_pos))

/-- A finite smooth partition by squares on a compact set, subordinate to the given neighborhoods. -/
theorem exists_subordinate_smooth_square_partition
    (K : Set Space) (hK : IsCompact K) (U : Space → Set Space)
    (hU : ∀ x ∈ K, U x ∈ 𝓝 x) :
    ∃ (n : ℕ) (c : Fin n → Space) (χ : Fin n → Space → ℝ),
      (∀ i, c i ∈ K) ∧ (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i, HasCompactSupport (χ i)) ∧ (∀ i, tsupport (χ i) ⊆ U (c i)) ∧
      (∀ x ∈ K, ∑ i, χ i x ^ 2 = 1) := by
  obtain ⟨n, c, b, hc, hsupport, hone⟩ := exists_subordinate_bumps K hK U hU
  let S (x : Space) := ∑ i, b i x ^ 2
  have hSdiff : ContDiff ℝ ∞ S :=
    ContDiff.sum (fun i _ => (b i).contDiff.pow 2)
  have hSnonneg (x : Space) : 0 ≤ S x :=
    Finset.sum_nonneg fun i _ => sq_nonneg (b i x)
  have hSone (x : Space) (hx : x ∈ K) : 1 ≤ S x := by
    obtain ⟨i, hi⟩ := hone x hx
    have hle : b i x ^ 2 ≤ S x :=
      Finset.single_le_sum (fun j _ => sq_nonneg (b j x)) (Finset.mem_univ i)
    simpa only [hi, one_pow] using hle
  let D (x : Space) := S x + (regularizer (S x)) ^ 2
  have hDpos (x : Space) : 0 < D x := by
    by_cases hx : S x = 0
    · simp [D, hx, regularizer_one_at_zero]
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hSnonneg x) (Ne.symm hx)) (sq_nonneg _)
  have hDdiff : ContDiff ℝ ∞ D := hSdiff.add ((regularizer.contDiff.comp hSdiff).pow 2)
  let d (x : Space) := Real.sqrt (D x)
  have hd (x : Space) : 0 < d x := Real.sqrt_pos.2 (hDpos x)
  have hddiff : ContDiff ℝ ∞ d := hDdiff.sqrt (fun x => (hDpos x).ne')
  let χ (i : Fin n) (x : Space) := b i x / d x
  have ht (i : Fin n) : tsupport (χ i) ⊆ tsupport (b i) := by
    simpa only [χ, div_eq_mul_inv] using
      (tsupport_mul_subset_left (f := fun x => b i x) (g := fun x => (d x)⁻¹))
  refine ⟨n, c, χ, hc, fun i => (b i).contDiff.div hddiff (fun x => (hd x).ne'), ?_,
    fun i => (ht i).trans (hsupport i), ?_⟩
  · intro i
    exact ((b i).hasCompactSupport : IsCompact (tsupport (b i))).of_isClosed_subset
      isClosed_closure (ht i)
  · intro x hx
    have hden : d x ^ 2 = S x := by
      change Real.sqrt (D x) ^ 2 = S x
      rw [Real.sq_sqrt (hDpos x).le]
      simp [D, regularizer_zero_of_one_le (hSone x hx)]
    calc
      (∑ i, χ i x ^ 2) = S x * (d x ^ 2)⁻¹ := by
        simp only [χ, div_pow]
        simp only [div_eq_mul_inv, Finset.sum_mul, S]
      _ = 1 := by
        rw [hden]
        exact mul_inv_cancel₀ (zero_lt_one.trans_le (hSone x hx)).ne'

/-- A partition with simultaneous small oscillation of finitely many continuous coefficients. -/
theorem exists_smooth_square_partition_for_oscillation {J : Type} [Finite J]
    (K : Set Space) (hK : IsCompact K) (W : Set Space) (hW : ∀ x ∈ K, W ∈ 𝓝 x)
    (a : J → Space → ℂ) (ha : ∀ j, Continuous (a j)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → Space) (χ : Fin n → Space → ℝ),
      (∀ i, c i ∈ K) ∧ (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i, HasCompactSupport (χ i)) ∧ (∀ i, tsupport (χ i) ⊆ W) ∧
      (∀ i x, x ∈ tsupport (χ i) → ∀ j, ‖a j x - a j (c i)‖ < ε) ∧
      (∀ x ∈ K, ∑ i, χ i x ^ 2 = 1) := by
  let U (x : Space) := W ∩ {y : Space | ∀ j, ‖a j y - a j x‖ < ε}
  have hU (x : Space) (hx : x ∈ K) : U x ∈ 𝓝 x := by
    apply Filter.inter_mem (hW x hx)
    apply Filter.eventually_all.mpr
    intro j
    have hcont : ContinuousAt (fun y => ‖a j y - a j x‖) x :=
      ((ha j).sub continuous_const).norm.continuousAt
    have hval : ‖a j x - a j x‖ < ε := by simpa only [sub_self, norm_zero] using hε
    exact hcont (Iio_mem_nhds hval)
  obtain ⟨n, c, χ, hc, hdiff, hcompact, hsupport, hsum⟩ :=
    exists_subordinate_smooth_square_partition K hK U hU
  exact ⟨n, c, χ, hc, hdiff, hcompact, fun i _ hx => (hsupport i hx).1,
    fun i _ hx => (hsupport i hx).2, hsum⟩

private theorem complexCutoff_bound (χ : Space → ℝ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖(χ x : ℂ)‖ ≤ B := by
  have hk : IsCompact (tsupport χ) := hc
  obtain ⟨B, hB, hb⟩ := (hk.image hχ).isBounded.exists_pos_norm_le
  refine ⟨B, hB.le, fun x => ?_⟩
  rw [Complex.norm_real]
  by_cases hx : x ∈ tsupport χ
  · exact hb _ ⟨x, hx, rfl⟩
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact hB.le

/-- A real smooth compact cutoff interpreted as an actual bounded physical multiplier symbol. -/
def physicalCutoffSymbol (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    Burnett.Fourier.BoundedSymbol Space where
  toFun x := (χ x : ℂ)
  measurable := (Complex.ofRealCLM.continuous.comp hχ.continuous).measurable.aestronglyMeasurable
  bound := (complexCutoff_bound χ hχ.continuous hc).choose
  bound_nonneg := (complexCutoff_bound χ hχ.continuous hc).choose_spec.1
  norm_le := (complexCutoff_bound χ hχ.continuous hc).choose_spec.2

theorem physicalCutoffSymbol_apply (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (x : Space) :
    physicalCutoffSymbol χ hχ hc x = (χ x : ℂ) :=
  rfl

theorem sum_physicalCutoffSymbol_conj_mul {n : ℕ} (χ : Fin n → Space → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hc : ∀ i, HasCompactSupport (χ i))
    {x : Space} (hsum : ∑ i, χ i x ^ 2 = 1) :
    ∑ i, conj (physicalCutoffSymbol (χ i) (hχ i) (hc i) x) *
      physicalCutoffSymbol (χ i) (hχ i) (hc i) x = 1 := by
  simp only [physicalCutoffSymbol_apply, Complex.conj_ofReal]
  have hcast : (↑(∑ i, χ i x ^ 2) : ℂ) = 1 := by rw [hsum, Complex.ofReal_one]
  push_cast at hcast
  simpa only [pow_two] using hcast

end Burnett.Microlocal.SmoothSquarePartition
