import Burnett.Analysis.PrincipalEnergy.Commutator.CanceledPairH1Bound

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Burnett.Fourier Burnett.Analysis.FirstOrderDyadic Burnett.Analysis.SymmetricEnergy
open scoped ComplexConjugate ContDiff InnerProductSpace Topology

open private scalarSchwartzProduct_L2_bound from Burnett.Analysis.PrincipalEnergy.Commutator.CanceledPairH1Bound

/-- A fixed smooth coefficient and one undifferentiated small input suffice
for the cubic background terms in which no derivative hits the test. -/
theorem tendsto_cubicBackground_small_value_pair_zero
    (r : Space → ℂ) (u v k : ℕ → SchwartzMap Space ℂ) (R M : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hr : ∀ x, ‖r x‖ ≤ R)
    (hrs : HasCompactSupport r) (hSmooth : ContDiff ℝ ∞ r)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hLim : Tendsto ε atTop (𝓝 0))
    (hu : ∀ n x, ‖u n x‖ ≤ ε n)
    (hv : ∀ n, ‖(v n).toLp 2 volume‖ ≤ M) (hk : ∀ n, ‖(k n).toLp 2 volume‖ ≤ M) :
    Tendsto (fun n => ∫ x, conj (k n x) * (r x * u n x * v n x)) atTop (𝓝 0) := by
  let c : SchwartzMap Space ℂ := hrs.toSchwartzMap hSmooth
  let P (n : ℕ) := scalarSchwartzProduct (scalarSchwartzProduct c (u n)) (v n)
  have hS (n : ℕ) (x : Space) : ‖scalarSchwartzProduct c (u n) x‖ ≤ R * ε n := by
    rw [scalarSchwartzProduct_apply, norm_mul]
    exact mul_le_mul (hr x) (hu n x) (norm_nonneg _) hR
  have hP (n : ℕ) : ‖(P n).toLp 2 volume‖ ≤ (R * ε n) * M :=
    (scalarSchwartzProduct_L2_bound _ _ (mul_nonneg hR (hε n)) (hS n)).trans
      (mul_le_mul_of_nonneg_left (hv n) (mul_nonneg hR (hε n)))
  have hPair (n : ℕ) :
      ⟪schwartzTestEquiv (k n), schwartzTestEquiv (P n)⟫_ℂ =
        ∫ x, conj (k n x) * (r x * u n x * v n x) := by
    simpa only [RCLike.inner_apply', P, scalarSchwartzProduct_apply] using schwartzTestEquiv_inner (k n) (P n)
  apply squeeze_zero_norm (a := fun n => M * ((R * ε n) * M))
  · intro n
    rw [← hPair n]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul (hk n) (hP n) (norm_nonneg _) hM)
  · simpa only [mul_zero, zero_mul] using (((hLim.const_mul R).mul_const M).const_mul M)

end Burnett.V03
