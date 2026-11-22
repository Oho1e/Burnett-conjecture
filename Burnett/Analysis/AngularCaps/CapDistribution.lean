import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Set Filter
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lp_moment_eq_norm_rpow {p : ℝ≥0∞} [Fact (1 ≤ p)] (hzero : p ≠ 0) (htop : p ≠ ⊤)
    (u : Lp ℂ p μ) :
    (∫⁻ x, ‖u x‖ₑ^p.toReal ∂μ) = ENNReal.ofReal (‖u‖^p.toReal) := by
  have h : p.toReal ≠ 0 := by
    rw [Ne,ENNReal.toReal_eq_zero_iff]
    exact not_or_intro hzero htop
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg u) ENNReal.toReal_nonneg,Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.memLp u).2.ne,
    eLpNorm_eq_lintegral_rpow_enorm hzero htop,← ENNReal.rpow_mul,one_div_mul_cancel h,ENNReal.rpow_one]

theorem lp_indicator_moment {p : ℝ≥0∞} [Fact (1 ≤ p)] (hzero : p ≠ 0) (htop : p ≠ ⊤)
    {u : X → ℂ} (hu : MemLp u p μ) {s : Set X} (hs : MeasurableSet s) :
    ENNReal.ofReal (‖(hu.indicator hs).toLp (s.indicator u)‖^p.toReal) =
      ∫⁻ x in s, ‖u x‖ₑ^p.toReal ∂μ := by
  rw [← lp_moment_eq_norm_rpow hzero htop,← lintegral_indicator hs]
  apply lintegral_congr_ae
  filter_upwards [(hu.indicator hs).coeFn_toLp] with x hx
  rw [hx]
  by_cases h : x ∈ s
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h,ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hzero htop)]

/-- The Chebyshev inequality with the output weight required by the L³
distribution integral. -/
theorem lp_tail_weighted_square {p : ℝ≥0∞} [Fact (1 ≤ p)] (hzero : p ≠ 0) (htop : p ≠ ⊤)
    (u : Lp ℂ p μ) {t : ℝ} (ht : 0 < t) :
    (ENNReal.ofReal t)^(2:ℕ) * μ {x | t < ‖u x‖} ≤
      ENNReal.ofReal (t^(2-p.toReal)) * ENNReal.ofReal (‖u‖^p.toReal) := by
  let q := p.toReal
  have hvol : μ {x | t < ‖u x‖} ≤ μ {x | ENNReal.ofReal t ≤ ‖u x‖ₑ} := by
    apply measure_mono
    intro x hx
    change t < ‖u x‖ at hx
    change ENNReal.ofReal t ≤ ‖u x‖ₑ
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal hx.le
  have cheb := mul_meas_ge_le_pow_eLpNorm' μ hzero htop (Lp.aestronglyMeasurable u) (ENNReal.ofReal t)
  rw [← ENNReal.ofReal_toReal (Lp.memLp u).2.ne,
    ← Lp.norm_def u,ENNReal.ofReal_rpow_of_nonneg (norm_nonneg u) ENNReal.toReal_nonneg,
    ENNReal.ofReal_rpow_of_nonneg ht.le ENNReal.toReal_nonneg] at cheb
  have hbase : ENNReal.ofReal (t^q) * μ {x | t < ‖u x‖} ≤ ENNReal.ofReal (‖u‖^q) :=
    (mul_le_mul_left' hvol _).trans cheb
  have hpow : (ENNReal.ofReal t)^(2:ℕ) = ENNReal.ofReal (t^(2-q)) * ENNReal.ofReal (t^q) := by
    rw [← ENNReal.ofReal_pow ht.le,← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ← Real.rpow_add ht,sub_add_cancel,Real.rpow_two]
  rw [hpow,mul_assoc]
  exact mul_le_mul_left' hbase _

/-- Apply the layer formula to the half norm so that the two parts can both
be tested at the same positive level t. -/
theorem cube_moment_eq_halfNorm_layer (u : X → ℂ) (hu : AEStronglyMeasurable u μ) :
    (∫⁻ x, ‖u x‖ₑ^(3:ℕ) ∂μ) =
      24 * ∫⁻ t in Ioi (0:ℝ), μ {x | 2*t < ‖u x‖} * (ENNReal.ofReal t)^(2:ℕ) := by
  let G (x : X) := ‖u x‖ / 2
  have hg : AEMeasurable G μ := hu.norm.aemeasurable.div_const _
  have hn (x : X) : 0 ≤ G x := div_nonneg (norm_nonneg _) (by norm_num)
  have layer := lintegral_comp_eq_lintegral_meas_lt_mul μ (Eventually.of_forall hn) hg
    (g := fun t : ℝ => t^2) (fun t _ => (continuous_pow 2).intervalIntegrable _ _)
    (Eventually.of_forall (fun t => sq_nonneg t))
  have poweq (x : X) : ‖u x‖ₑ^(3:ℕ) = 24 * ENNReal.ofReal (∫ t in 0..G x, t^2) := by
    rw [← ofReal_norm_eq_enorm,← ENNReal.ofReal_pow (norm_nonneg (u x)),integral_pow,
      ← ENNReal.ofReal_ofNat,← ENNReal.ofReal_mul (by norm_num : 0 ≤ (24:ℝ))]
    congr 1
    dsimp only [G]
    ring
  have sets (t : ℝ) : {x | t < G x} = {x | 2*t < ‖u x‖} := by
    ext x
    change t < ‖u x‖ / 2 ↔ 2*t < ‖u x‖
    rw [lt_div_iff₀ (by norm_num : (0:ℝ)<2),mul_comm t 2]
  simp_rw [poweq]
  rw [lintegral_const_mul' _ _ (by norm_num),layer]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
  rw [sets t,ENNReal.ofReal_pow ht.le]

end Burnett.Analysis.CapFourier
