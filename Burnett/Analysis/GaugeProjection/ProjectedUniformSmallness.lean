import Burnett.Analysis.GaugeProjection.ProjectedShellBounds
import Burnett.Analysis.GaugeProjection.ProjectedCutoffAction
import Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.P01

open MeasureTheory Set Filter Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open scoped ContDiff FourierTransform Topology NNReal ENNReal

private theorem integrable_convolution (k : E → ℂ) (hk : Integrable k)
    (f : SchwartzMap E ℂ) (x : E) (M : ℝ) (hM : ∀ y, ‖f y‖ ≤ M) :
    Integrable (fun y => k (x-y) * f y) := by
  have hk' : Integrable fun y => k (x-y) := (integrable_comp_sub_left k x).2 hk
  refine (hk'.norm.mul_const M).mono'
    (hk'.aestronglyMeasurable.mul f.continuous.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun y => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _)

private theorem dyadic_inverse_add (J j : ℕ) :
    (dyadicScale (J+j))⁻¹ = (dyadicScale J)⁻¹ * (1/2 : ℝ)^j := by
  simp only [dyadicScale, pow_add, mul_inv_rev, ← inv_pow, one_div, mul_comm]

private theorem dyadic_inverse_sum_le (J K : ℕ) :
    (∑ j ∈ Finset.range K, (dyadicScale (J+j))⁻¹) ≤ 2 * (dyadicScale J)⁻¹ := by
  simp_rw [dyadic_inverse_add, ← Finset.mul_sum]
  have hs : (∑ j ∈ Finset.range K, (1/2 : ℝ)^j) ≤ 2 := by
    have hsum := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)
    calc
      _ ≤ ∑' j : ℕ, (1/2 : ℝ)^j := hsum.sum_le_tsum _ (by intro j _; positivity)
      _ = 2 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  simpa only [mul_comm (2 : ℝ)] using
    mul_le_mul_of_nonneg_left hs (by unfold dyadicScale; positivity : 0 ≤ (dyadicScale J)⁻¹)

private theorem norm_projectionDyadicApproximation_le (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (f : SchwartzMap E ℂ) (J K : ℕ) (x : E)
    (M : ℝ) (hM : ∀ y, ‖f y‖ ≤ M) (L : ℝ≥0) (hL : LipschitzWith L (f : E → ℂ)) :
    ‖projectionDyadicApproximation m hm f (J+K) x‖ ≤
      ((∫ z, ‖projectionCorrectionKernel m hm z‖)
        + (J : ℝ) * (∫ z, ‖inverseAnnularSchwartz m hm z‖)) * M +
      2 * (∫ z, ‖inverseAnnularSchwartz m hm z‖ * ‖z‖) *
        (dyadicScale J)⁻¹ * (L : ℝ) := by
  let k₀ := projectionCorrectionKernel m hm
  let k (j : ℕ) := shellKernel m hm j
  let c₀ := ∫ y, k₀ (x-y) * f y
  let c (j : ℕ) := ∫ y, k j (x-y) * f y
  let A₀ := ∫ z, ‖k₀ z‖
  let A := ∫ z, ‖inverseAnnularSchwartz m hm z‖
  let B := ∫ z, ‖inverseAnnularSchwartz m hm z‖ * ‖z‖
  have hB : 0 ≤ B := integral_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc : projectionDyadicApproximation m hm f (J+K) x = c₀ + ∑ j ∈ Finset.range (J+K), c j := by
    rw [projectionDyadicApproximation_eq_convolution m hm hd]
    change (∫ y, (k₀ (x-y) + ∑ j ∈ Finset.range (J+K), k j (x-y)) * f y) = _
    have h₀ := integrable_convolution (k₀ : E → ℂ) k₀.integrable f x M hM
    have hi (j : ℕ) := integrable_convolution (k j)
      (projectedShellKernel_integrable m hm j) f x M hM
    simp_rw [add_mul, Finset.sum_mul]
    rw [integral_add h₀ (integrable_finset_sum _ fun j _ => hi j),
      integral_finset_sum _ fun j _ => hi j]
  rw [hc, Finset.sum_range_add]
  have hl : ‖∑ j ∈ Finset.range J, c j‖ ≤ (J : ℝ) * (A * M) := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, ‖c j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range J, A*M := Finset.sum_le_sum fun j _ =>
        (projected_shell_convolution_bounds m hm j f x M hM L hL).1
      _ = _ := by simp
  have hh : ‖∑ j ∈ Finset.range K, c (J+j)‖ ≤ 2 * B * (dyadicScale J)⁻¹ * (L : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range K, ‖c (J+j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range K, B * (dyadicScale (J+j))⁻¹ * (L : ℝ) :=
        Finset.sum_le_sum fun j _ =>
          (projected_shell_convolution_bounds m hm (J+j) f x M hM L hL).2
      _ = B * (∑ j ∈ Finset.range K, (dyadicScale (J+j))⁻¹) * (L : ℝ) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ B * (2 * (dyadicScale J)⁻¹) * (L : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (dyadic_inverse_sum_le J K) hB) L.coe_nonneg
      _ = _ := by ring
  have hc₀ : ‖c₀‖ ≤ A₀ * M := norm_integral_convolution_le k₀ f k₀.integrable x M hM
  calc
    _ ≤ ‖c₀‖ + ‖∑ j ∈ Finset.range J, c j‖ + ‖∑ j ∈ Finset.range K, c (J+j)‖ := by
      apply (norm_add_le _ _).trans
      rw [add_assoc]
      exact add_le_add_left (norm_add_le _ _) _
    _ ≤ A₀ * M + (J : ℝ) * (A * M) + 2 * B * (dyadicScale J)⁻¹ * (L : ℝ) :=
      add_le_add (add_le_add hc₀ hl) hh
    _ = _ := by ring

/-- The original regularized scalar projection obeys a whole-space bound
on its actual output, with an arbitrary finite dyadic splitting point. -/
theorem gaugeProjectionSchwartzComponent_sup_bound (a b c d : Fin 4)
    (f : SchwartzMap E ℂ) (J : ℕ) (x : E) (M : ℝ) (hM : ∀ y, ‖f y‖ ≤ M)
    (L : ℝ≥0) (hL : LipschitzWith L (f : E → ℂ)) :
    let m := gaugeDyadicAngularSymbol a b c d
    let hm := gaugeDyadicAngularSymbol_smooth a b c d
    ‖gaugeProjectionSchwartzComponent a b c d f x‖ ≤
      ((∫ z, ‖projectionCorrectionKernel m hm z‖)
        + (J : ℝ) * (∫ z, ‖inverseAnnularSchwartz m hm z‖)) * M +
      2 * (∫ z, ‖inverseAnnularSchwartz m hm z‖ * ‖z‖) *
        (dyadicScale J)⁻¹ * (L : ℝ) := by
  dsimp only
  apply le_of_tendsto (projectionDyadicApproximation_tendsto a b c d f x).norm
  refine eventually_atTop.2 ⟨J, fun N hN => ?_⟩
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hN
  exact norm_projectionDyadicApproximation_le _ _ (gaugeDyadicAngularSymbol_degreeZero a b c d)
    f J K x M hM L hL

theorem gaugeProjectionSchwartzComponent_uniform_small (a b c d : Fin 4)
    (L : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (f : SchwartzMap E ℂ), LipschitzWith L (f : E → ℂ) →
      (∀ y, ‖f y‖ ≤ δ) → ∀ x, ‖gaugeProjectionSchwartzComponent a b c d f x‖ < ε := by
  let m := gaugeDyadicAngularSymbol a b c d
  let hm := gaugeDyadicAngularSymbol_smooth a b c d
  let B := ∫ z, ‖inverseAnnularSchwartz m hm z‖ * ‖z‖
  have hT : Tendsto (fun j : ℕ => 2 * B * (dyadicScale j)⁻¹ * (L : ℝ)) atTop (𝓝 0) := by
    have h₀ : Tendsto (fun j : ℕ => (dyadicScale j)⁻¹) atTop (𝓝 0) := by
      simpa only [dyadicScale, ← inv_pow, one_div] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
          (by norm_num : (1/2 : ℝ) < 1))
    simpa only [mul_zero, zero_mul] using (h₀.const_mul (2*B)).mul_const (L : ℝ)
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hT.eventually (gt_mem_nhds (by linarith : 0 < ε/2)))
  let A := (∫ z, ‖projectionCorrectionKernel m hm z‖)
    + (J : ℝ) * (∫ z, ‖inverseAnnularSchwartz m hm z‖)
  have hA : 0 ≤ A := add_nonneg (integral_nonneg fun x => norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg J) (integral_nonneg fun x => norm_nonneg _))
  let δ := (ε/2) / (A+1)
  have hA1 : 0 < A+1 := by positivity
  refine ⟨δ, div_pos (by linarith) hA1, fun f hL hsmall x => ?_⟩
  have hl := gaugeProjectionSchwartzComponent_sup_bound a b c d f J x δ hsmall L hL
  change ‖gaugeProjectionSchwartzComponent a b c d f x‖ ≤ A * δ +
    2 * B * (dyadicScale J)⁻¹ * (L : ℝ) at hl
  have hδ : A * δ ≤ ε / 2 := by
    calc
      _ ≤ (A+1)*δ := mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (by linarith) hA1.le)
      _ = _ := by dsimp only [δ]; field_simp
  linarith [hJ J le_rfl]

/-- The actual original matrix projection converges uniformly on the whole
coordinate space for uniformly small Schwartz matrices with one Lipschitz bound. -/
theorem projectionFullSchwartz_uniformly_small (w : ℕ → ProjectionSchwartzMatrix)
    (L : ℝ≥0) (hL : ∀ n c d, LipschitzWith L (w n c d : E → ℂ))
    (hsmall : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ x c d, ‖w n c d x‖ < ε) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ x a b, ‖projectionFullSchwartz (w n) a b x‖ < ε := by
  intro ε hε
  have hentry (a b c d : Fin 4) : ∀ᶠ n in atTop,
      ∀ x, ‖gaugeProjectionSchwartzComponent a b c d (w n c d) x‖ < ε/32 := by
    obtain ⟨δ, hδ, hb⟩ := gaugeProjectionSchwartzComponent_uniform_small a b c d L (ε/32) (by linarith)
    filter_upwards [hsmall δ hδ] with n hn
    exact hb (w n c d) (hL n c d) (fun y => (hn y c d).le)
  have hall : ∀ᶠ n in atTop, ∀ a b c d x,
      ‖gaugeProjectionSchwartzComponent a b c d (w n c d) x‖ < ε/32 :=
    Filter.eventually_all.2 (fun a => Filter.eventually_all.2 (fun b =>
      Filter.eventually_all.2 (fun c => Filter.eventually_all.2 (hentry a b c))))
  filter_upwards [hall] with n hn x a b
  let S (c d : Fin 4) := gaugeProjectionSchwartzComponent a b c d (w n c d) x
  have hsum : projectionFullSchwartz (w n) a b x = ∑ c, ∑ d, S c d := by
    let eval : SchwartzMap E ℂ →+ ℂ :=
      { toFun := fun v => v x
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change eval (∑ c, ∑ d, gaugeProjectionSchwartzComponent a b c d (w n c d)) =
      ∑ c, ∑ d, eval (gaugeProjectionSchwartzComponent a b c d (w n c d))
    simp_rw [map_sum]
  rw [hsum]
  calc
    _ ≤ ∑ c, ∑ d, ‖S c d‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => norm_sum_le _ _)
    _ ≤ ∑ c : Fin 4, ∑ d : Fin 4, ε/32 :=
      Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => (hn a b c d x).le
    _ < ε := by simp; linarith

/-- The componentwise whole-space L∞ norm of the original projected matrix
goes to zero, with the same input and the same uniform Lipschitz bound. -/
theorem projectionFullSchwartz_eLpNorm_top_tendsto_zero (w : ℕ → ProjectionSchwartzMatrix)
    (L : ℝ≥0) (hL : ∀ n c d, LipschitzWith L (w n c d : E → ℂ))
    (hsmall : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ x c d, ‖w n c d x‖ < ε) :
    Tendsto (fun n => eLpNorm (fun x : E => fun a b => projectionFullSchwartz (w n) a b x)
      ⊤ volume) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  let r := (min ε 1).toReal
  have hfinite : min ε 1 ≠ ⊤ :=
    ((min_le_right ε 1).trans_lt ENNReal.one_lt_top).ne
  have hr : 0 < r := ENNReal.toReal_pos (lt_min hε zero_lt_one).ne' hfinite
  filter_upwards [projectionFullSchwartz_uniformly_small w L hL hsmall r hr] with n hn
  have ha : ∀ᵐ x ∂(volume : Measure E), ‖fun a b => projectionFullSchwartz (w n) a b x‖ ≤ r :=
    Eventually.of_forall fun x => (pi_norm_le_iff_of_nonneg hr.le).2 fun a =>
      (pi_norm_le_iff_of_nonneg hr.le).2 fun b => (hn x a b).le
  have hb := eLpNorm_le_of_ae_bound (p := (⊤ : ℝ≥0∞)) ha
  simp only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, one_mul] at hb
  exact hb.trans ((ENNReal.ofReal_toReal hfinite).trans_le (min_le_left ε 1))

end Burnett.P01
