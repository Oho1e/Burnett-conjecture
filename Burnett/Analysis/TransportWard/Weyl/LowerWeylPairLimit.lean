import Burnett.Analysis.TransportWard.Weyl.LowerEulerWeylCommutator

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 1900

noncomputable section

namespace Burnett.V03.Palatini

open Filter Function MeasureTheory Set Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open scoped ContDiff Topology ComplexConjugate InnerProductSpace BigOperators

local notation "D" => frozenSchwartzCoordinatePartial

private theorem exists_compactBaseOrderOne_pair_bound {q : E → E → ℂ}
    (hq : CompactBaseOrderOne q) (hs : Continuous (uncurry q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : SchwartzMap E ℂ,
      ‖∫ x, conj (v x) * firstOrderAction q u x‖ ≤ C * Real.sqrt (schwartzH1Energy u) * ‖v.toLp 2 volume‖ := by
  obtain ⟨C,hC,hBound⟩ := exists_compactBase_firstOrderAction_h1_to_l2 hq hs
  refine ⟨C,hC,fun u v => ?_⟩
  obtain ⟨hL,hL₂⟩ := hBound u
  let T := hL.toLp (firstOrderAction q u)
  have hE : 0 ≤ schwartzH1Energy u := by
    unfold schwartzH1Energy
    exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hT : ‖T‖ ≤ C * Real.sqrt (schwartzH1Energy u) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hE]
    exact hL₂
  have hEq : ⟪v.toLp 2 volume,T⟫_ℂ = ∫ x, conj (v x) * firstOrderAction q u x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [v.coeFn_toLp 2 volume,MemLp.coeFn_toLp hL] with x hv ht
    change inner ℂ ((v.toLp 2 volume) x) ((hL.toLp _) x) = _
    rw [hv,ht,RCLike.inner_apply']
  rw [← hEq]
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    ((mul_le_mul_of_nonneg_left hT (norm_nonneg _)).trans_eq (mul_comm _ _))

private theorem tendsto_compactBaseOrderOne_pair_zero {q : E → E → ℂ}
    (hq : CompactBaseOrderOne q) (hs : Continuous (uncurry q))
    (u v : ℕ → SchwartzMap E ℂ) (M : ℝ) (hU : ∀ n, Real.sqrt (schwartzH1Energy (u n)) ≤ M)
    (hV : Tendsto (fun n => ‖(v n).toLp 2 volume‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, conj (v n x) * firstOrderAction q (u n) x) atTop (𝓝 0) := by
  obtain ⟨C,hC,hBound⟩ := exists_compactBaseOrderOne_pair_bound hq hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h0 : Tendsto (fun n => C*M*‖(v n).toLp 2 volume‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hV.const_mul (C*M)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
  exact (hBound (u n) (v n)).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hU n) hC) (norm_nonneg _))

/-- Each actual zero-order and first-order Euler coefficient commutator
in the two-window action makes a vanishing matrix pairing. -/
theorem tendsto_lowerEulerWeylComm_pair_zero {ι : Type*} [Fintype ι]
    {a : E → E → ℂ} (ha : ScaledJointOrderOne a) {K : Set E}
    (hK : IsCompact K) (hZero : ∀ x ∉ K, ∀ ξ, a x ξ = 0)
    (c₀ : ι → ι → SchwartzMap E ℂ) (c₁ : ι → ι → Fin 4 → SchwartzMap E ℂ)
    (u v : ℕ → ι → SchwartzMap E ℂ)
    (hU : ∀ j, ∃ M : ℝ, ∀ n, Real.sqrt (schwartzH1Energy (u n j)) ≤ M)
    (hV : ∀ i, Tendsto (fun n => ‖(v n i).toLp 2 volume‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i, ∑ j, (
      (∫ x, conj (v n i x) * (Complex.I * (c₀ i j x * firstOrderAction a (u n j) x -
        firstOrderAction a (scalarSchwartzProduct (c₀ i j) (u n j)) x))) +
      ∑ k : Fin 4, ∫ x, conj (v n i x) * (Complex.I *
        (c₁ i j k x * physicalCoordinatePartial k (firstOrderAction a (u n j)) x -
          firstOrderAction a (scalarSchwartzProduct (c₁ i j k) (D k (u n j))) x))))
      atTop (𝓝 0) := by
  let L₀ (i j : ι) (n : ℕ) :=
    ∫ x, conj (v n i x) * firstOrderAction (fun y ξ => -coefficientCommutatorSymbol a (c₀ i j) y ξ) (u n j) x
  let L₁ (i j : ι) (k : Fin 4) (n : ℕ) :=
    ∫ x, conj (v n i x) * firstOrderAction (lowerFirstOrderWeylCommutatorSymbol a (c₁ i j k) k) (u n j) x
  have h₀ (i j : ι) : Tendsto (L₀ i j) atTop (𝓝 0) := by
    obtain ⟨M,hM⟩ := hU j
    have hS : ContDiff ℝ ∞ (uncurry (fun y ξ => -coefficientCommutatorSymbol a (c₀ i j) y ξ)) :=
      (coefficientCommutatorSymbol_order_zero ha (c₀ i j)).1.neg
    exact tendsto_compactBaseOrderOne_pair_zero
      (lowerZeroOrderWeylCommutator_compactBaseOrderOne ha (c₀ i j) hK hZero) hS.continuous
      (fun n => u n j) (fun n => v n i) M hM (hV i)
  have h₁ (i j : ι) (k : Fin 4) : Tendsto (L₁ i j k) atTop (𝓝 0) := by
    obtain ⟨M,hM⟩ := hU j
    exact tendsto_compactBaseOrderOne_pair_zero
      (lowerFirstOrderWeylCommutatorSymbol_compactBaseOrderOne ha (c₁ i j k) k hK hZero)
      (lowerFirstOrderWeylCommutatorSymbol_profile ha (c₁ i j k) k).1.continuous
      (fun n => u n j) (fun n => v n i) M hM (hV i)
  have hR (i j : ι) : Tendsto (fun n => L₀ i j n + ∑ k, L₁ i j k n) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero,add_zero] using
      (h₀ i j).add (tendsto_finset_sum Finset.univ (fun k _ => h₁ i j k))
  have hRow (i : ι) : Tendsto (fun n => ∑ j, (L₀ i j n + ∑ k, L₁ i j k n)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun j _ => hR i j)
  have hAll : Tendsto (fun n => ∑ i, ∑ j, (L₀ i j n + ∑ k, L₁ i j k n)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun i _ => hRow i)
  exact hAll.congr (fun n => by
    simp only [L₀,L₁,firstOrderAction_lowerZeroOrderWeylCommutator ha,
      firstOrderAction_lowerFirstOrderWeylCommutatorSymbol ha])

end Burnett.V03.Palatini
