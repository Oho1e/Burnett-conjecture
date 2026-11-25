import Burnett.Analysis.CubicEnergy.HighSlotCommutator.LowCartesianQuantitative
import Mathlib.Analysis.Seminorm

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A06

open Set Metric
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff

/-- The inhomogeneous weight on the two independent Fourier frequencies. -/
def symbolFrequencyWeight (x : Joint) : ℝ := 1 + ‖x.1‖ + ‖x.2‖

theorem symbolFrequencyWeight_pos (x : Joint) : 0 < symbolFrequencyWeight x := by
  unfold symbolFrequencyWeight
  positivity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- One weighted Cartesian jet, using the operator norm on the full Fréchet derivative. -/
def orderOneWeightedJet (n : ℕ) (b : Joint → 𝕜) (x : Joint) : ℝ :=
  ‖iteratedFDeriv ℝ n b x‖ * (symbolFrequencyWeight x ^ n / symbolFrequencyWeight x)

theorem orderOneWeightedJet_eq_zpow (n : ℕ) (b : Joint → 𝕜) (x : Joint) :
    orderOneWeightedJet n b x =
      symbolFrequencyWeight x ^ ((n : ℤ) - 1) * ‖iteratedFDeriv ℝ n b x‖ := by
  rw [orderOneWeightedJet, zpow_sub₀ (symbolFrequencyWeight_pos x).ne', zpow_natCast, zpow_one,
    mul_comm]

private theorem orderOneWeight_nonneg (n : ℕ) (x : Joint) :
    0 ≤ symbolFrequencyWeight x ^ n / symbolFrequencyWeight x :=
  div_nonneg (pow_nonneg (symbolFrequencyWeight_pos x).le _) (symbolFrequencyWeight_pos x).le

private theorem orderOneWeightedJet_zero (n : ℕ) (x : Joint) :
    orderOneWeightedJet n (0 : Joint → 𝕜) x = 0 := by
  change ‖iteratedFDeriv ℝ n (fun _ : Joint => (0 : 𝕜)) x‖ *
    (symbolFrequencyWeight x ^ n / symbolFrequencyWeight x) = 0
  rw [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero, zero_mul]

private theorem nat_le_smooth (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  change ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

private theorem orderOneWeightedJet_add_le {b c : Joint → 𝕜}
    (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c) (n : ℕ) (x : Joint) :
    orderOneWeightedJet n (b+c) x ≤ orderOneWeightedJet n b x + orderOneWeightedJet n c x := by
  have bs := (hb.of_le (nat_le_smooth n)).contDiffAt (x := x)
  have cs := (hc.of_le (nat_le_smooth n)).contDiffAt (x := x)
  unfold orderOneWeightedJet
  rw [iteratedFDeriv_add_apply bs cs, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (orderOneWeight_nonneg n x)

private theorem orderOneWeightedJet_smul {b : Joint → 𝕜}
    (hb : ContDiff ℝ ∞ b) (a : 𝕜) (n : ℕ) (x : Joint) :
    orderOneWeightedJet n (a • b) x = ‖a‖ * orderOneWeightedJet n b x := by
  have bs := (hb.of_le (nat_le_smooth n)).contDiffAt (x := x)
  unfold orderOneWeightedJet
  rw [iteratedFDeriv_const_smul_apply bs, norm_smul, mul_assoc]

/-- Translation-invariant order-one symbols on the manuscript's joint frequency space.
The coefficient field can be real or complex. -/
def orderOneSymbolSubmodule (𝕜 : Type*) [RCLike 𝕜] : Submodule 𝕜 (Joint → 𝕜) where
  carrier := {b | ContDiff ℝ ∞ b ∧ ∀ n, BddAbove (range (orderOneWeightedJet n b))}
  zero_mem' := by
    refine ⟨contDiff_const, ?_⟩
    intro n
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [orderOneWeightedJet_zero]
  add_mem' := by
    rintro b c ⟨hb, bb⟩ ⟨hc, bc⟩
    refine ⟨hb.add hc, ?_⟩
    intro n
    obtain ⟨B,hB⟩ := bb n
    obtain ⟨C,hC⟩ := bc n
    refine ⟨B+C, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (orderOneWeightedJet_add_le hb hc n x).trans
      (add_le_add (hB (mem_range_self x)) (hC (mem_range_self x)))
  smul_mem' := by
    rintro a b ⟨hb, bb⟩
    refine ⟨hb.const_smul a, ?_⟩
    intro n
    obtain ⟨B,hB⟩ := bb n
    refine ⟨‖a‖*B, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [orderOneWeightedJet_smul hb]
    exact mul_le_mul_of_nonneg_left (hB (mem_range_self x)) (norm_nonneg a)

abbrev OrderOneSymbol (𝕜 : Type*) [RCLike 𝕜] := ↥(orderOneSymbolSubmodule 𝕜)

theorem mem_orderOneSymbolSubmodule_iff {b : Joint → 𝕜} :
    b ∈ orderOneSymbolSubmodule 𝕜 ↔
      ContDiff ℝ ∞ b ∧ ∀ n, BddAbove (range (orderOneWeightedJet n b)) := Iff.rfl

theorem OrderOneSymbol.contDiff (b : OrderOneSymbol 𝕜) : ContDiff ℝ ∞ (b : Joint → 𝕜) :=
  (mem_orderOneSymbolSubmodule_iff.mp b.property).1

private theorem OrderOneSymbol.bddAbove (b : OrderOneSymbol 𝕜) (n : ℕ) :
    BddAbove (range (orderOneWeightedJet n (b : Joint → 𝕜))) :=
  (mem_orderOneSymbolSubmodule_iff.mp b.property).2 n

/-- The weighted jet at a fixed order, maximized over all physical frequencies. -/
def orderOneWeightedSeminorm (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) : Seminorm 𝕜 (OrderOneSymbol 𝕜) := by
  let q := fun b : OrderOneSymbol 𝕜 => sSup (range (orderOneWeightedJet n (b : Joint → 𝕜)))
  refine Seminorm.ofSMulLE q ?_ ?_ ?_
  · change sSup (range (orderOneWeightedJet n (0 : Joint → 𝕜))) = 0
    rw [show orderOneWeightedJet n (0 : Joint → 𝕜) = (fun _ => 0) from
      funext (orderOneWeightedJet_zero n), range_const, csSup_singleton]
  · intro b c
    apply csSup_le (range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact (orderOneWeightedJet_add_le b.contDiff c.contDiff n x).trans
      (add_le_add (le_csSup (b.bddAbove n) (mem_range_self x))
        (le_csSup (c.bddAbove n) (mem_range_self x)))
  · intro a b
    apply csSup_le (range_nonempty _)
    rintro _ ⟨x, rfl⟩
    change orderOneWeightedJet n (a • (b : Joint → 𝕜)) x ≤ _
    rw [orderOneWeightedJet_smul b.contDiff]
    exact mul_le_mul_of_nonneg_left (le_csSup (b.bddAbove n) (mem_range_self x)) (norm_nonneg a)

theorem orderOneWeightedSeminorm_apply (n : ℕ) (b : OrderOneSymbol 𝕜) :
    orderOneWeightedSeminorm 𝕜 n b = sSup (range (orderOneWeightedJet n (b : Joint → 𝕜))) := rfl

/-- The finite maximum over derivative orders from zero through the given threshold. -/
def orderOneSymbolSeminorm (𝕜 : Type*) [RCLike 𝕜] (K : ℕ) : Seminorm 𝕜 (OrderOneSymbol 𝕜) :=
  (Finset.range (K+1)).sup (orderOneWeightedSeminorm 𝕜)

theorem orderOneSymbolSeminorm_monotone (𝕜 : Type*) [RCLike 𝕜] :
    Monotone (orderOneSymbolSeminorm 𝕜) := by
  intro K L h
  exact Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ h))

theorem orderOneSymbolSeminorm_eq_order (K : ℕ) (b : OrderOneSymbol 𝕜) :
    ∃ n ≤ K, orderOneSymbolSeminorm 𝕜 K b =
      sSup (range (orderOneWeightedJet n (b : Joint → 𝕜))) := by
  obtain ⟨n,hn,h⟩ := Seminorm.exists_apply_eq_finset_sup (orderOneWeightedSeminorm 𝕜)
    (Finset.nonempty_range_add_one (n := K)) b
  exact ⟨n, Nat.le_of_lt_succ (Finset.mem_range.mp hn), h⟩

theorem orderOneWeightedJet_le_symbolSeminorm {n K : ℕ} (hn : n ≤ K)
    (b : OrderOneSymbol 𝕜) (x : Joint) :
    orderOneWeightedJet n (b : Joint → 𝕜) x ≤ orderOneSymbolSeminorm 𝕜 K b := by
  calc
    _ ≤ orderOneWeightedSeminorm 𝕜 n b := le_csSup (b.bddAbove n) (mem_range_self x)
    _ ≤ _ := Seminorm.le_finset_sup_apply (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

theorem orderOneSymbolSeminorm_le_iff {K : ℕ} {C : ℝ} (hC : 0 ≤ C) (b : OrderOneSymbol 𝕜) :
    orderOneSymbolSeminorm 𝕜 K b ≤ C ↔
      ∀ n ≤ K, ∀ x, orderOneWeightedJet n (b : Joint → 𝕜) x ≤ C := by
  constructor
  · intro h n hn x
    exact (orderOneWeightedJet_le_symbolSeminorm hn b x).trans h
  · intro h
    apply Seminorm.finset_sup_apply_le hC
    intro n hn
    rw [orderOneWeightedSeminorm_apply]
    apply csSup_le (range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact h n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) x

/-- The same seminorm family after forgetting complex scalar multiplication. -/
def realOrderOneSymbolSeminorm (𝕜 : Type*) [RCLike 𝕜] :
    SeminormFamily ℝ (OrderOneSymbol 𝕜) ℕ :=
  fun K => (orderOneSymbolSeminorm 𝕜 K).restrictScalars ℝ

theorem realOrderOneSymbolSeminorm_monotone (𝕜 : Type*) [RCLike 𝕜] :
    Monotone (realOrderOneSymbolSeminorm 𝕜) :=
  fun _ _ h x => orderOneSymbolSeminorm_monotone 𝕜 h x

/-- The previously constructed Cartesian coefficient lies in the actual symbol submodule. -/
theorem regularizedLowCartesianSymbol_mem_orderOneSymbolSubmodule
    (η χ : ℝ → ℝ) (c : Joint → ℂ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hηzero : ∀ s ≤ r, η s = 0) (hηone : ∀ s ≥ R, η s = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ s ≥ ρ^2, χ s = 0)
    {V : Set Joint} (hV : IsOpen V)
    (hContains : closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V)
    (hc : ContDiffOn ℝ ∞ c V) :
    regularizedLowCartesianSymbol η χ c ∈ orderOneSymbolSubmodule ℂ := by
  refine mem_orderOneSymbolSubmodule_iff.mpr ⟨?_, ?_⟩
  · exact regularizedLowCartesianSymbol_contDiff η χ c hr hρ hη hηzero hχ hcut hV hContains hc
  · intro n
    have hn := nat_le_smooth n
    obtain ⟨C,_,bound⟩ := exists_regularizedLowCartesianSymbol_orderOne_bound n η χ c
      hr hρ hR (hη.of_le hn) hηzero hηone (hχ.of_le hn) hcut hV hContains (hc.of_le hn)
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [orderOneWeightedJet, ← mul_div_assoc, div_le_iff₀ (symbolFrequencyWeight_pos x)]
    exact bound x

end Burnett.A06
