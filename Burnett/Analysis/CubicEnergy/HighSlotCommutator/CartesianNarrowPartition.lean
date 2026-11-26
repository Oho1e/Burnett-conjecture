import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CoefficientRadialProfile
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Filter Finset
open scoped ContDiff Topology BigOperators

def cartesianBandDilation (j : ℕ) : ℝ := 1+(j:ℝ)/8

def cartesianNarrowScale (s : ℝ) (i : ℕ) : ℝ :=
  cartesianBandDilation (i+1)*s

def cartesianNarrowProfile (w : SchwartzMap E ℂ) (i : ℕ) (q : E) : ℂ :=
  w ((cartesianBandDilation i/cartesianBandDilation (i+1)) • q)-w q

def cartesianNarrowWindow (w : SchwartzMap E ℂ) (s : ℝ) (i k : ℕ) (q : E) : ℂ :=
  cartesianNarrowProfile w i
    ((dyadicCoefficientScale (cartesianNarrowScale s i) k/tau) • q)

private theorem cartesianBandDilation_ge_one (j : ℕ) : 1≤cartesianBandDilation j :=
  le_add_of_nonneg_right (by positivity : (0:ℝ)≤(j:ℝ)/8)

private theorem cartesianBandDilation_pos (j : ℕ) : 0<cartesianBandDilation j :=
  zero_lt_one.trans_le (cartesianBandDilation_ge_one j)

private theorem cartesianBandDilation_succ (j : ℕ) :
    cartesianBandDilation (j+1)=cartesianBandDilation j+1/8 := by
  unfold cartesianBandDilation
  push_cast
  ring

theorem cartesianNarrowScale_pos {s : ℝ} (hs : 0<s) (i : ℕ) :
    0<cartesianNarrowScale s i := mul_pos (cartesianBandDilation_pos _) hs

theorem cartesianNarrowScale_le {s : ℝ} (hs : 0≤s) {i : ℕ} (hi : i<8) :
    cartesianNarrowScale s i ≤ 2*s := by
  unfold cartesianNarrowScale
  apply mul_le_mul_of_nonneg_right _ hs
  have h : ((i+1:ℕ):ℝ)≤8 := by exact_mod_cast hi
  unfold cartesianBandDilation
  linarith only [h]

theorem cartesianNarrowProfile_contDiff (w : SchwartzMap E ℂ) (i : ℕ) :
    ContDiff ℝ ∞ (cartesianNarrowProfile w i) :=
  (w.smooth'.comp (contDiff_const.smul contDiff_id)).sub w.smooth'

/-- Eight fixed relative dilations split one dyadic annulus. Each normalized
piece is supported in the narrow annulus required by the coefficient estimate. -/
theorem cartesianNarrowProfile_support (w : SchwartzMap E ℂ)
    (h₁ : ∀ q : E, ‖q‖≤1 → w q=1)
    (h₀ : ∀ q : E, (17/16 : ℝ)≤‖q‖ → w q=0)
    (i : ℕ) (q : E) (hq : cartesianNarrowProfile w i q≠0) :
    1≤‖q‖ ∧ ‖q‖≤5/4 := by
  let r := cartesianBandDilation i/cartesianBandDilation (i+1)
  have hp : 0<cartesianBandDilation (i+1) := cartesianBandDilation_pos _
  have rlo : (8/9 : ℝ)≤r := by
    apply (le_div_iff₀ hp).mpr
    rw [cartesianBandDilation_succ]
    linarith only [cartesianBandDilation_ge_one i]
  have rhi : r≤1 := by
    apply (div_le_iff₀ hp).mpr
    rw [cartesianBandDilation_succ,one_mul]
    linarith
  have hn : ‖r • q‖=r*‖q‖ := by
    rw [norm_smul,Real.norm_of_nonneg ((by norm_num : (0:ℝ)≤8/9).trans rlo)]
  change w (r • q) - w q ≠ 0 at hq
  constructor
  · by_contra! h
    have hR : ‖r • q‖≤1 := by
      rw [hn]
      exact (mul_le_of_le_one_left (norm_nonneg q) rhi).trans h.le
    exact hq (by rw [h₁ _ hR,h₁ _ h.le,sub_self])
  · by_contra! h
    have hR : (17/16 : ℝ)≤‖r • q‖ := by
      rw [hn]
      have hA := mul_le_mul_of_nonneg_right rlo (norm_nonneg q)
      linarith only [hA,h]
    exact hq (by rw [h₀ _ hR,h₀ _ (by linarith only [h]),sub_self])

private theorem cartesianNarrowProfile_dilated (w : SchwartzMap E ℂ) (i : ℕ) (z : E) :
    cartesianNarrowProfile w i (cartesianBandDilation (i+1) • z) =
      w (cartesianBandDilation i • z)-w (cartesianBandDilation (i+1) • z) := by
  unfold cartesianNarrowProfile
  rw [smul_smul,div_mul_cancel₀ _ (cartesianBandDilation_pos _).ne']

private theorem cartesian_narrow_sum (w : SchwartzMap E ℂ) (z : E) (I : ℕ) :
    (∑ i ∈ range I, cartesianNarrowProfile w i (cartesianBandDilation (i+1) • z)) =
      w z - w (cartesianBandDilation I • z) := by
  induction I with
  | zero =>
    have hs : cartesianBandDilation 0=1 := by norm_num [cartesianBandDilation]
    simp only [range_zero,sum_empty,hs,one_smul,sub_self]
  | succ i ih =>
    rw [sum_range_succ,ih,cartesianNarrowProfile_dilated]
    abel

private theorem cartesianNarrowWindow_at_scale (w : SchwartzMap E ℂ) (s : ℝ) (i k : ℕ) (q : E) :
    cartesianNarrowWindow w s i k q = cartesianNarrowProfile w i
      (cartesianBandDilation (i+1) • ((dyadicCoefficientScale s k/tau) • q)) := by
  unfold cartesianNarrowWindow
  rw [smul_smul]
  congr 2
  unfold dyadicCoefficientScale cartesianNarrowScale
  ring

/-- The finite radial decomposition is an exact telescope of the same low
window, preserving the dyadic and radian arguments. -/
theorem cartesianNarrowWindow_partial_sum (w : SchwartzMap E ℂ) (s : ℝ) (N : ℕ) (q : E) :
    (∑ i ∈ range 8, ∑ k ∈ range (N+1), cartesianNarrowWindow w s i k q) =
      w ((dyadicCoefficientScale s N/tau) • q)-w ((2*s/tau) • q) := by
  rw [sum_comm]
  simp_rw [cartesianNarrowWindow_at_scale]
  simp_rw [cartesian_narrow_sum]
  have h8 : cartesianBandDilation 8=2 := by norm_num [cartesianBandDilation]
  simp only [h8,smul_smul]
  induction N with
  | zero =>
    simp only [zero_add,range_one,sum_singleton,dyadicCoefficientScale,pow_zero,div_one,mul_div_assoc]
  | succ n ih =>
    rw [sum_range_succ,ih,← mul_div_assoc,dyadicCoefficientScale_succ]
    abel

theorem cartesianNarrowWindow_summable (w : SchwartzMap E ℂ)
    (h₁ : ∀ q : E, ‖q‖≤1 → w q=1)
    (h₀ : ∀ q : E, (17/16 : ℝ)≤‖q‖ → w q=0)
    (s : ℝ) (i : ℕ) (q : E) : Summable (fun k => cartesianNarrowWindow w s i k q) := by
  have lim : Tendsto (fun k => (dyadicCoefficientScale (cartesianNarrowScale s i) k/tau) • q) atTop
      (𝓝 (0:E)) := by
    simpa only [zero_div,zero_smul] using
      (((dyadicCoefficientScale_tendsto_zero (cartesianNarrowScale s i)).div_const tau).smul
        (tendsto_const_nhds (x := q)))
  have hn : ∀ᶠ k : ℕ in atTop, ‖(dyadicCoefficientScale (cartesianNarrowScale s i) k/tau) • q‖<1 :=
    lim.norm.eventually (gt_mem_nhds (by simp))
  obtain ⟨K,hK⟩ := eventually_atTop.mp hn
  refine summable_of_ne_finset_zero (s := range K) fun k hk => ?_
  by_contra h
  exact (not_le_of_gt (hK k (not_lt.mp fun hk' => hk (mem_range.mpr hk'))))
    (cartesianNarrowProfile_support w h₁ h₀ i _ h).1

/-- All high radii are selected by finitely many narrow orbits, with no
missing radial sector. The remaining multiplier is the stated low-pass. -/
theorem cartesianNarrowWindow_tsum_sum (w : SchwartzMap E ℂ)
    (h₁ : ∀ q : E, ‖q‖≤1 → w q=1) (h₀ : ∀ q : E, (17/16 : ℝ)≤‖q‖ → w q=0)
    (s : ℝ) (q : E) :
    (∑ i ∈ range 8, ∑' k : ℕ, cartesianNarrowWindow w s i k q) =
      1-w ((2*s/tau) • q) := by
  have lim : Tendsto (fun N => ∑ i ∈ range 8, ∑ k ∈ range (N+1), cartesianNarrowWindow w s i k q)
      atTop (𝓝 (∑ i ∈ range 8, ∑' k : ℕ, cartesianNarrowWindow w s i k q)) := by
    apply tendsto_finset_sum
    intro i _
    exact (cartesianNarrowWindow_summable w h₁ h₀ s i q).hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)
  simp_rw [cartesianNarrowWindow_partial_sum] at lim
  have zlim : Tendsto (fun N => (dyadicCoefficientScale s N/tau) • q) atTop (𝓝 (0:E)) := by
    simpa only [zero_div,zero_smul] using
      (((dyadicCoefficientScale_tendsto_zero s).div_const tau).smul (tendsto_const_nhds (x := q)))
  have wlim := (w.continuous.continuousAt.tendsto.comp zlim).sub_const (w ((2*s/tau) • q))
  have w0 := h₁ 0 (by simp)
  rw [w0] at wlim
  exact tendsto_nhds_unique lim wlim

end Burnett.A06
