import Burnett.Analysis.TransportPatches.WidePatchErrorInterpolation

/-! Whole-vector L³ norms for the ordered gradient, using the same coordinate fields. -/
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 6100000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ENNReal Topology

local notation "GradSlot" => Index × OrderedPair

def orderedGradientValue (f : GradSlot → ComplexL2 E) (x : E) : PiLp 2 (fun _ : GradSlot => ℂ) :=
  WithLp.toLp 2 (fun a => f a x)

theorem orderedGradientValue_L3_le_sum (f : GradSlot → ComplexL2 E)
    (hf : ∀ a, MemLp (f a : E → ℂ) 3 volume) :
    MemLp (orderedGradientValue f) 3 volume ∧
    (eLpNorm (orderedGradientValue f) 3 volume).toReal ≤
      ∑ a : GradSlot, (eLpNorm (f a : E → ℂ) 3 volume).toReal := by
  have hPoint (x : E) : ‖orderedGradientValue f x‖ ≤ ∑ a : GradSlot, ‖f a x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).1
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
  have hLe : eLpNorm (orderedGradientValue f) 3 volume ≤
      ∑ a : GradSlot, eLpNorm (f a : E → ℂ) 3 volume := by
    calc
      _ ≤ eLpNorm (fun x => ∑ a : GradSlot, ‖f a x‖) 3 volume := eLpNorm_mono_real hPoint
      _ ≤ ∑ a : GradSlot, eLpNorm (fun x => ‖f a x‖) 3 volume := by
        rw [show (fun x => ∑ a : GradSlot, ‖f a x‖) = ∑ a : GradSlot, (fun x => ‖f a x‖) from
          funext (fun x => (Finset.sum_apply x Finset.univ (fun a : GradSlot => fun y : E => ‖f a y‖)).symm)]
        exact eLpNorm_sum_le (fun a _ => (hf a).1.norm) (by norm_num)
      _ = _ := Finset.sum_congr rfl (fun a _ => eLpNorm_norm (f a : E → ℂ))
  have hFin : (∑ a : GradSlot, eLpNorm (f a : E → ℂ) 3 volume) < ⊤ :=
    ENNReal.sum_lt_top.2 (fun a _ => (hf a).eLpNorm_lt_top)
  have hPi : Measurable (fun x : E => fun a : GradSlot => f a x) :=
    measurable_pi_lambda _ (fun a => (Lp.stronglyMeasurable (f a)).measurable)
  have hMeas : AEStronglyMeasurable (orderedGradientValue f) (volume : Measure E) :=
    ((PiLp.continuous_toLp 2 (fun _ : GradSlot => ℂ)).comp_stronglyMeasurable hPi.stronglyMeasurable).aestronglyMeasurable
  refine ⟨⟨hMeas, hLe.trans_lt hFin⟩, ?_⟩
  exact (ENNReal.toReal_mono hFin.ne hLe).trans_eq (ENNReal.toReal_sum (fun a _ => (hf a).eLpNorm_lt_top.ne))

theorem memLp_three_of_complexL2_and_finiteP (p : ℝ) (hp : 3 < p) (f : ComplexL2 E)
    (hf : MemLp (f : E → ℂ) (ENNReal.ofReal p) volume) : MemLp (f : E → ℂ) 3 volume := by
  have hp₀ : 0 < p := by linarith
  have h₂ : eLpNorm' (f : E → ℂ) 2 volume < ⊤ := by
    have h := Lp.eLpNorm_lt_top f
    rwa [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp), ENNReal.toReal_ofNat] at h
  have hₚ : eLpNorm' (f : E → ℂ) p volume < ⊤ := by
    have h := hf.eLpNorm_lt_top
    rwa [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hp₀) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp₀.le] at h
  obtain ⟨ha, ha₁, _⟩ := frozenErrorExponent_bounds hp
  refine ⟨Lp.aestronglyMeasurable f, ?_⟩
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by simp), ENNReal.toReal_ofNat]
  exact (frozenError_interpolate hp (Lp.aestronglyMeasurable f)).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ha.le h₂.ne)
      (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr ha₁.le) hₚ.ne))

/-- A simultaneous row-wise bound is an actual full-space ordered-vector bound. -/
theorem orderedGradientValue_eventually_L3 (f : ℕ → GradSlot → ComplexL2 E) (R : ℝ)
    (hf : ∀ n a, MemLp (f n a : E → ℂ) 3 volume)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ a : GradSlot,
      (eLpNorm' (f n a : E → ℂ) 3 volume).toReal ≤ R + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, (eLpNorm (orderedGradientValue (f n)) 3 volume).toReal ≤ 64 * R + ε := by
  intro ε hε
  filter_upwards [h (ε / 64) (by positivity)] with n hn
  refine (orderedGradientValue_L3_le_sum (f n) (hf n)).2.trans ?_
  calc
    _ ≤ ∑ _a : GradSlot, (R + ε / 64) := by
      apply Finset.sum_le_sum
      intro a _
      rw [eLpNorm_eq_eLpNorm' (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by simp), ENNReal.toReal_ofNat]
      exact hn a
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, show Fintype.card GradSlot = 64 by decide, nsmul_eq_mul]
      push_cast
      ring

end Burnett.C02
