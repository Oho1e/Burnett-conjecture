import Burnett.Analysis.PrincipalEnergy.Freezing.OrderZeroMikhlin
import Burnett.Analysis.PrincipalEnergy.Freezing.FixedInfraredWeyl

set_option autoImplicit false
set_option maxHeartbeats 2150000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal Topology

theorem mikhlin_order_zero_budget_dilate (m : E → ℝ) (hm : ContDiff ℝ ∞ m)
    (D : ℝ) (budget : MikhlinOrderZeroBudget m D) (s : ℝ) (hs : 0 < s) :
    MikhlinOrderZeroBudget (fun ξ : E => m (s • ξ)) D := by
  intro n hn ξ hξ
  let L : E →L[ℝ] E := s • ContinuousLinearMap.id ℝ E
  change ‖ξ‖ ^ n * ‖iteratedFDeriv ℝ n (m ∘ L) ξ‖ ≤ D
  have normL : ‖L‖ ≤ s := by
    dsimp only [L]
    rw [norm_smul, Real.norm_of_nonneg hs.le]
    exact mul_le_of_le_one_right hs.le ContinuousLinearMap.norm_id_le
  have hZ : ‖L ξ‖ = s * ‖ξ‖ := by
    change ‖s • ξ‖ = _
    rw [norm_smul, Real.norm_of_nonneg hs.le]
  have hZ0 : L ξ ≠ 0 := smul_ne_zero hs.ne' hξ
  rw [L.iteratedFDeriv_comp_right hm ξ (by exact_mod_cast le_top)]
  have h := (iteratedFDeriv ℝ n m (L ξ)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  refine (mul_le_mul_of_nonneg_left h (pow_nonneg (norm_nonneg _) _)).trans ?_
  calc
    _ ≤ ‖ξ‖ ^ n * (‖iteratedFDeriv ℝ n m (L ξ)‖ * s ^ n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) normL _)
        (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _)
    _ = ‖L ξ‖ ^ n * ‖iteratedFDeriv ℝ n m (L ξ)‖ := by rw [hZ, mul_pow]; ring
    _ ≤ D := budget n hn _ hZ0

theorem mikhlin_order_zero_budget_value_bound (m : E → ℝ) (hm : ContDiff ℝ ∞ m)
    (D : ℝ) (budget : MikhlinOrderZeroBudget m D) : ∀ ξ, ‖m ξ‖ ≤ D := by
  let B : Set E := {ξ | ‖m ξ‖ ≤ D}
  have hB : IsClosed B := isClosed_le hm.continuous.norm continuous_const
  have inclusion : ({0}ᶜ : Set E) ⊆ B := by
    intro ξ hξ
    have nonzero : ξ ≠ 0 := hξ
    simpa only [B, mem_setOf_eq, pow_zero, one_mul, norm_iteratedFDeriv_zero] using
      budget 0 (by decide) ξ nonzero
  have all : (univ : Set E) ⊆ B := by
    rw [← (dense_compl_singleton (0 : E)).closure_eq]
    exact closure_minimal inclusion hB
  exact fun ξ => all (mem_univ ξ)

/-- General smooth real order-zero frequency symbols yield a uniform
Schwartz-input W¹,³ estimate for the literal left or Weyl separated action. -/
theorem exists_radian_mikhlin_order_zero_separated_W13 :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : E → ℝ), ContDiff ℝ ∞ m → ∀ D : ℝ, 0 ≤ D →
      MikhlinOrderZeroBudget m D → ∀ (σ : ℝ) (f u : SchwartzMap E ℂ),
        let p := ENNReal.ofReal 3
        let W := separatedRadianQuantization σ m f u
        MemLp W p volume ∧
          eLpNorm W p volume ≤ ENNReal.ofReal (K * D * patchFourierMoment 0 f) * eLpNorm (u : E → ℂ) p volume ∧
          Differentiable ℝ W ∧
          ∀ j : Index, let d (x : E) := fderiv ℝ W x (EuclideanSpace.single j 1)
            MemLp d p volume ∧ eLpNorm d p volume ≤
              ENNReal.ofReal (K * D * patchFourierMoment 0 f) * eLpNorm (energyPartial j u : E → ℂ) p volume +
              ENNReal.ofReal (K * D * tau * patchFourierMoment 1 f) * eLpNorm (u : E → ℂ) p volume := by
  obtain ⟨A, Afin, est⟩ := exists_order_zero_mikhlin_L3_bound
  let K := max 1 A.toReal
  have K0 : 0 ≤ K := zero_le_one.trans (le_max_left _ _)
  refine ⟨K, K0, ?_⟩
  intro m hm D D0 budget σ f u
  have τp : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  let b (ξ : E) := m (tau • ξ)
  have hb : ContDiff ℝ ∞ b := hm.comp (contDiff_const.smul contDiff_id)
  have hBudget : MikhlinOrderZeroBudget b D := mikhlin_order_zero_budget_dilate m hm D budget tau τp
  have hA : A ≤ ENNReal.ofReal K := by
    rw [← ENNReal.ofReal_toReal Afin.ne]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have sup (ξ : E) : ‖m ξ‖ ≤ K * D :=
    (mikhlin_order_zero_budget_value_bound m hm D budget ξ).trans
      (le_mul_of_one_le_left D0 (le_max_left _ _))
  have sec (v : SchwartzMap E ℂ) :
      MemLp (radianAction m v) (ENNReal.ofReal 3) volume ∧ eLpNorm (radianAction m v) (ENNReal.ofReal 3) volume ≤
        ENNReal.ofReal (K * D) * eLpNorm (v : E → ℂ) (ENNReal.ofReal 3) volume := by
    have eq : radianAction m v = normalizedComplexFourierAction (fun ξ => (b ξ : ℂ)) v := by
      rw [← radianActionSpectrum_inverse]
      rfl
    rw [eq]
    have h := est b hb D D0 hBudget v
    rw [ENNReal.ofReal_mul K0]
    exact ⟨h.1, h.2.trans (mul_le_mul_right' (mul_le_mul_right' hA _) _)⟩
  exact separated_radian_order_zero_W13 m hm.continuous.measurable (K * D) (mul_nonneg K0 D0) sup sec σ f u

end Burnett.A03
