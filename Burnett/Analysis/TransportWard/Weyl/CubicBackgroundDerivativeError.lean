import Burnett.Analysis.PrincipalEnergy.Localization.OrderOneCutoffH1Energy
import Burnett.Analysis.PrincipalEnergy.Commutator.CanceledPairH1Bound

set_option autoImplicit false
set_option maxHeartbeats 2300000

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.CarlesonEmbedding (scalarSchwartzProduct_pderiv)
open Burnett.Analysis.SymmetricEnergy
open scoped ComplexConjugate InnerProductSpace Topology

open private scalarSchwartzProduct_L2_bound from Burnett.Analysis.PrincipalEnergy.Commutator.CanceledPairH1Bound

local notation "⊙" => scalarSchwartzProduct

private theorem scalarSchwartzProduct_swap (u v : SchwartzMap Space ℂ) : ⊙ u v = ⊙ v u := by
  ext x
  exact mul_comm (u x) (v x)

private theorem scalarSchwartzProduct_addLeft (u v w : SchwartzMap Space ℂ) :
    ⊙ (u + v) w = ⊙ u w + ⊙ v w := by
  ext x
  exact add_mul (u x) (v x) (w x)

/-- The derivative on the order-one Weyl test can be moved onto the two
small perturbation factors. Only an L² bound on the test is used. -/
theorem tendsto_cubicBackground_test_derivative_pair_zero
    (e : Space) (r : SchwartzMap Space ℂ) (u v k : ℕ → SchwartzMap Space ℂ)
    (ε δ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hδ : ∀ n, 0 ≤ δ n)
    (hLimε : Tendsto ε atTop (𝓝 0)) (hLimδ : Tendsto δ atTop (𝓝 0))
    (hu : ∀ n x, ‖u n x‖ ≤ ε n) (hv : ∀ n x, ‖v n x‖ ≤ δ n)
    (M : ℝ) (hM : 0 ≤ M) :
    let D := SchwartzMap.pderivCLM ℂ e
    (∀ n, ‖(u n).toLp 2 volume‖ ≤ M) →
    (∀ n, ‖(D (u n)).toLp 2 volume‖ ≤ M) →
    (∀ n, ‖(D (v n)).toLp 2 volume‖ ≤ M) →
    (∀ n, ‖(k n).toLp 2 volume‖ ≤ M) →
    Tendsto (fun n => ∫ x, conj (D (k n) x) * (r x * u n x * v n x)) atTop (𝓝 0) := by
  intro D hu₂ hdu hdv hk
  let P (n : ℕ) := ⊙ (⊙ r (u n)) (v n)
  let A := SchwartzMap.seminorm ℝ 0 0 r + SchwartzMap.seminorm ℝ 0 0 (D r)
  have hA : 0 ≤ A := by positivity
  have hr (x : Space) : ‖r x‖ ≤ A :=
    (SchwartzMap.norm_le_seminorm ℝ r x).trans (le_add_of_nonneg_right (apply_nonneg _ _))
  have hdr (x : Space) : ‖D r x‖ ≤ A :=
    (SchwartzMap.norm_le_seminorm ℝ (D r) x).trans (le_add_of_nonneg_left (apply_nonneg _ _))
  have hProd (n : ℕ) : ‖(D (P n)).toLp 2 volume‖ ≤ A * M * (ε n + 2 * δ n) := by
    let T := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)
    have he : D (P n) = ⊙ (⊙ r (u n)) (D (v n)) +
        (⊙ (⊙ r (D (u n))) (v n) + ⊙ (⊙ (D r) (u n)) (v n)) := by
      dsimp only [D, P]
      rw [scalarSchwartzProduct_pderiv, scalarSchwartzProduct_pderiv, scalarSchwartzProduct_addLeft]
    have hC (x : Space) : ‖⊙ r (u n) x‖ ≤ A * ε n := by
      rw [scalarSchwartzProduct_apply, norm_mul]
      exact mul_le_mul (hr x) (hu n x) (norm_nonneg _) hA
    have h1 := (scalarSchwartzProduct_L2_bound (⊙ r (u n)) (D (v n)) (mul_nonneg hA (hε n)) hC).trans
      (mul_le_mul_of_nonneg_left (hdv n) (mul_nonneg hA (hε n)))
    have h2 : ‖(⊙ (⊙ r (D (u n))) (v n)).toLp 2 volume‖ ≤ δ n * (A * M) := by
      rw [scalarSchwartzProduct_swap (⊙ r (D (u n))) (v n)]
      exact (scalarSchwartzProduct_L2_bound (v n) _ (hδ n) (hv n)).trans (mul_le_mul_of_nonneg_left
        ((scalarSchwartzProduct_L2_bound r _ hA hr).trans (mul_le_mul_of_nonneg_left (hdu n) hA)) (hδ n))
    have h3 : ‖(⊙ (⊙ (D r) (u n)) (v n)).toLp 2 volume‖ ≤ δ n * (A * M) := by
      rw [scalarSchwartzProduct_swap (⊙ (D r) (u n)) (v n)]
      exact (scalarSchwartzProduct_L2_bound (v n) _ (hδ n) (hv n)).trans (mul_le_mul_of_nonneg_left
        ((scalarSchwartzProduct_L2_bound (D r) _ hA hdr).trans (mul_le_mul_of_nonneg_left (hu₂ n) hA)) (hδ n))
    change ‖T (D (P n))‖ ≤ _
    rw [he, map_add, map_add]
    refine (norm_add_le _ _).trans (add_le_add h1 ((norm_add_le _ _).trans (add_le_add h2 h3)) |>.trans ?_)
    ring_nf
    exact le_rfl
  have hBound (n : ℕ) : ‖∫ x, conj (D (k n) x) * (r x * u n x * v n x)‖ ≤ M * (A * M * (ε n + 2 * δ n)) := by
    have hq := schwartz_derivative_isSkew (F := ℂ) e (schwartzTestEquiv (k n)) (schwartzTestEquiv (P n))
    change ⟪schwartzDerivative e (schwartzTestEquiv (k n)), schwartzTestEquiv (P n)⟫_ℂ = _ at hq
    simp only [schwartzDerivative, transportSchwartzOp_on_equiv, ContinuousLinearMap.coe_coe,
      schwartzTestEquiv_inner, RCLike.inner_apply', P, scalarSchwartzProduct_apply] at hq
    rw [hq, norm_neg]
    have he : ⟪schwartzTestEquiv (k n), schwartzTestEquiv (D (P n))⟫_ℂ =
        ∫ x : Space, conj (k n x) * D (P n) x := by
      simp only [schwartzTestEquiv_inner, RCLike.inner_apply']
    rw [← he]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul (hk n) (hProd n) (norm_nonneg _) hM)
  apply squeeze_zero_norm hBound
  simpa only [mul_zero, add_zero] using
    (((hLimε.add (hLimδ.const_mul (2 : ℝ))).const_mul (A * M)).const_mul M)

end Burnett.V03
