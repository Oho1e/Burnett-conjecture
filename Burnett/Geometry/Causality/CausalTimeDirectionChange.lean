import Burnett.Geometry.Causality.ChartTimeOrientation

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set
open Burnett.RicciSymbol
open Burnett.Geometry.CotangentHamiltonCauchySlice

/-- Two timelike reference directions in the same component select the same
sign on every nonzero causal vector. The segment between the references is
timelike, which prevents the causal pairing from vanishing along it. -/
theorem causal_sign_preserved_between_timelike_directions {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hSym : B.IsSymm) (b : Module.Basis Index ℝ E)
    (hb : ∀ i j, B (b i) (b j) = TensorFrame.standardInverse i j)
    (n T v : E) (hn : B n n < 0) (hT : B T T < 0) (hnT : B n T < 0)
    (hv : v ≠ 0) (hvv : B v v ≤ 0) (hnv : B n v < 0) : B T v < 0 := by
  let w (s : ℝ) := (1 - s) • n + s • T
  have hww (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : B (w s) (w s) < 0 := by
    have hExp : B (w s) (w s) = (1 - s)^2 * B n n +
        2 * (1 - s) * s * B n T + s^2 * B T T := by
      simp only [w, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hSym.eq T n]
      ring
    rw [hExp]
    have hCross : 2 * (1 - s) * s * B n T ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hs.2)) hs.1) hnT.le
    have hBase : (1 - s)^2 * B n n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hn.le
    by_cases hzero : s = 0
    · simpa [hzero] using hn
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hzero)
      exact add_neg_of_nonpos_of_neg (add_nonpos hBase hCross) (mul_neg_of_pos_of_neg (sq_pos_of_pos hspos) hT)
  let f (s : ℝ) := B (w s) v
  have hc : Continuous f := by
    have hw : Continuous w := by dsimp only [w]; fun_prop
    exact ((B.flip v).toContinuousLinearMap.continuous).comp hw
  have hne (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : f s ≠ 0 := by
    intro he
    exact (not_lt_of_ge hvv) (positive_of_timelike_orthogonal B b hb (hww s hs) hv he)
  have hf0 : f 0 = B n v := by simp [f, w]
  have hf1 : f 1 = B T v := by simp [f, w]
  by_contra! hEnd
  have h0 : f 0 ≤ 0 := hf0.symm ▸ hnv.le
  have h1 : 0 ≤ f 1 := hf1.symm ▸ hEnd
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc zero_le_one hc.continuousOn ⟨h0, h1⟩
  exact hne t ht hz

end Burnett.Geometry.FiniteCausalVolume
