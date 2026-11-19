import Burnett.Analysis.SignedFourierWindow.CalderonBadSum

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- A continuous bounded integrable kernel convolves absolutely, at each point,
with every finite Lᵖ input for p≥1. Split at unit input size. -/
theorem kernel_integrand_Lp (K : Space → ℂ) (hK : Continuous K) (hi : Integrable K)
    (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D) (p : ℝ) (hp : 1≤p) (f : Space → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) volume) (x : Space) :
    Integrable (fun y => K (x-y)*f y) := by
  have hp0 : 0<p := by linarith
  have ihr : Integrable (fun y : Space => K (x-y)) :=
    ((volume.measurePreserving_sub_left x).integrable_comp hi.1).2 hi
  have ip : Integrable (fun y : Space => ‖f y‖^p) := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      hf.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
  have dpos : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine (ihr.norm.add (ip.const_mul D)).mono' ((hK.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hf.1) ?_
  filter_upwards with y
  change ‖K (x-y)*f y‖ ≤ ‖K (x-y)‖+D*‖f y‖^p
  rw [norm_mul]
  by_cases small : ‖f y‖ ≤ 1
  · exact (mul_le_of_le_one_right (norm_nonneg _) small).trans (le_add_of_nonneg_right (mul_nonneg dpos (Real.rpow_nonneg (norm_nonneg _) _)))
  · exact (mul_le_mul (hD _) (Real.self_le_rpow_of_one_le (not_le.mp small).le hp) (norm_nonneg _) dpos).trans
      (le_add_of_nonneg_left (norm_nonneg _))

/-- A uniform seminorm estimate on integrable Borel inputs gives the same bound
on all Lᵖ inputs. Absolute convergence identifies the limit with the original convolution. -/
theorem kernelLp_exhaustion (K : Space → ℂ) (hK : Continuous K) (hi : Integrable K) (D : ℝ)
    (hD : ∀ z, ‖K z‖ ≤ D) (p : ℝ) (hp : 1≤p) (C : ℝ≥0∞)
    (test : ∀ g : Space → ℂ, Measurable g → Integrable g →
      eLpNorm (kernelApply K g) (ENNReal.ofReal p) volume ≤ C*eLpNorm g (ENNReal.ofReal p) volume)
    (f : Space → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (kernelApply K f) (ENNReal.ofReal p) volume ≤ C*eLpNorm f (ENNReal.ofReal p) volume := by
  let g := hf.1.mk f
  have hg : Measurable g := hf.1.stronglyMeasurable_mk.measurable
  have eq : f =ᵐ[volume] g := hf.1.ae_eq_mk
  have hgLp := hf.ae_eq eq
  let S := fun n : ℕ => closedBall (0:Space) (n:ℝ)
  let v := fun n : ℕ => (S n).indicator g
  have hmS (n : ℕ) : MeasurableSet (S n) := measurableSet_closedBall
  have mon : Monotone S := fun i j h => closedBall_subset_closedBall (by exact_mod_cast h)
  have un : (⋃ n, S n) = univ := iUnion_closedBall_nat _
  have hm (n : ℕ) : Measurable (v n) := hg.indicator (hmS n)
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have vi (n : ℕ) : Integrable (v n) := by
    letI : IsFiniteMeasure ((volume : Measure Space).restrict (S n)) := isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
    exact (integrable_indicator_iff (hmS n)).mpr ((hgLp.restrict (S n)).integrable h1)
  have limit (x : Space) : Tendsto (fun n => kernelApply K (v n) x) atTop (𝓝 (kernelApply K f x)) := by
    have intg := kernel_integrand_Lp K hK hi D hD p hp g hgLp x
    have ev (n : ℕ) : kernelApply K (v n) x = ∫ y in S n, K (x-y)*g y := by
      rw [← integral_indicator (hmS n)]
      apply integral_congr_ae
      filter_upwards with y
      by_cases mem : y ∈ S n <;> simp [v,mem]
    have val : kernelApply K f x = ∫ y, K (x-y)*g y := integral_congr_ae
      (eq.mono fun y hy => congrArg (fun z => K (x-y)*z) hy)
    simp_rw [ev,val]
    simpa only [un,Measure.restrict_univ] using tendsto_setIntegral_of_monotone hmS mon intg.integrableOn
  have fatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p) (μ := (volume : Measure Space))
    (fun n => (measurable_kernelApply K (v n) hK (hm n)).aestronglyMeasurable) _ (Eventually.of_forall limit)
  have each (n : ℕ) := (test (v n) (hm n) (vi n)).trans
    (mul_le_mul_left' (eLpNorm_indicator_le (μ := (volume : Measure Space)) (p := ENNReal.ofReal p) (s := S n) g) C)
  rw [eLpNorm_congr_ae eq]
  exact fatou.trans ((Filter.liminf_le_liminf (Eventually.of_forall each)).trans_eq (liminf_const _))

end Burnett.Analysis.SignedFourierWindow
