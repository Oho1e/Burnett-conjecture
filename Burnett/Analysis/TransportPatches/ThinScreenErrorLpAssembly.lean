import Burnett.Analysis.TransportPatches.ActualThinScreenCombination
import Burnett.Analysis.TransportPatches.WideGradientVectorL3

/-! The L³ error estimate for the exact thin-screen composition of the two wide errors. -/
set_option autoImplicit false
set_option maxRecDepth 5300
set_option maxHeartbeats 7800000

noncomputable section

namespace Burnett.C02

open Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix)
open scoped BigOperators ENNReal Topology

local notation "GradSlot" => Index × OrderedPair

private theorem complexL2_L3_norm_eq (f : ComplexL2 E) :
    eLpNorm (f : E → ℂ) 3 volume = eLpNorm' (f : E → ℂ) 3 volume := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by simp), ENNReal.toReal_ofNat]

theorem orderedGradientValue_component_L3 (F : GradSlot → ComplexL2 E)
    (h : MemLp (orderedGradientValue F) 3 volume) (a : GradSlot) :
    MemLp (F a : E → ℂ) 3 volume ∧ (eLpNorm (F a : E → ℂ) 3 volume).toReal ≤
      (eLpNorm (orderedGradientValue F) 3 volume).toReal := by
  have hBound : eLpNorm (F a : E → ℂ) 3 volume ≤ eLpNorm (orderedGradientValue F) 3 volume :=
    eLpNorm_mono (fun x => PiLp.norm_apply_le (orderedGradientValue F x) a)
  exact ⟨⟨Lp.aestronglyMeasurable _, hBound.trans_lt h.eLpNorm_lt_top⟩, ENNReal.toReal_mono h.eLpNorm_lt_top.ne hBound⟩

private theorem complexL2_sum_L3 (f g : ComplexL2 E)
    (hf : MemLp (f : E → ℂ) 3 volume) (hg : MemLp (g : E → ℂ) 3 volume) :
    MemLp ((f + g : ComplexL2 E) : E → ℂ) 3 volume ∧
    (eLpNorm ((f + g : ComplexL2 E) : E → ℂ) 3 volume).toReal ≤
      (eLpNorm (f : E → ℂ) 3 volume).toReal + (eLpNorm (g : E → ℂ) 3 volume).toReal := by
  have hE := Lp.coeFn_add f g
  refine ⟨(memLp_congr_ae hE).2 (hf.add hg), ?_⟩
  rw [eLpNorm_congr_ae hE, ← ENNReal.toReal_add hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne]
  exact ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨hf.eLpNorm_lt_top, hg.eLpNorm_lt_top⟩).ne
    (eLpNorm_add_le hf.1 hg.1 (by norm_num))

/-- Both rates consume the bounded thin scalar on L³ of the actual wide
errors. The extra term in the first rate is the strongly zero complement. -/
theorem actualThinScreen_gradient_errors_L3_of_wide
    (m : Tensor2) (wideInner wideOuter : ℝ) (hm : WideScreenFrequencySmooth wideInner wideOuter m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ℕ → ProjectionSchwartzMatrix) (A R : ℝ) (hA : 0 ≤ A)
    (hScalar : ∀ f : ComplexL2 E, MemLp (f : E → ℂ) 3 volume →
      let F := fourierMultiplier (thinConeScalar m hη i o) f
      MemLp (F : E → ℂ) 3 volume ∧ (eLpNorm (F : E → ℂ) 3 volume).toReal ≤
        A * (eLpNorm (f : E → ℂ) 3 volume).toReal) :
    let U (n : ℕ) (a : GradSlot) := multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z n) a.1 a.2
    let V (n : ℕ) (a : GradSlot) :=
      multiplierCoordinateDerivative (actualThinScreenMultiplier m wideInner wideOuter hm hη i o) (z n) a.1 a.2
    let E₁ (n : ℕ) (a : GradSlot) :=
      multiplierCoordinateDerivative (actualFrozenScreenErrorMultiplier wideInner wideOuter m hm) (z n) a.1 a.2
    let E₂ (n : ℕ) (a : GradSlot) :=
      multiplierCoordinateDerivative (actualFrozenPhaseErrorMultiplier wideInner wideOuter m hm) (z n) a.1 a.2
    let C (n : ℕ) (a : GradSlot) :=
      multiplierCoordinateDerivative (actualThinConeComplementMultiplier m hη i o) (z n) a.1 a.2
    let diff (n : ℕ) (a : GradSlot) := U n a - V n a
    let phase (n : ℕ) (a : GradSlot) := fourierMultiplier (frozenPhaseScalar m) (V n a)
    (∀ n, MemLp (orderedGradientValue (E₁ n)) 3 volume ∧ MemLp (orderedGradientValue (E₂ n)) 3 volume) →
    (∀ ε > 0, ∀ᶠ n in atTop,
      (eLpNorm (orderedGradientValue (E₁ n)) 3 volume).toReal ≤ R + ε ∧
      (eLpNorm (orderedGradientValue (E₂ n)) 3 volume).toReal ≤ R + ε) →
    (∀ n a, MemLp (C n a : E → ℂ) 3 volume) →
    (∀ a, Tendsto (fun n => (eLpNorm' (C n a : E → ℂ) 3 volume).toReal) atTop (𝓝 0)) →
    (∀ n, MemLp (orderedGradientValue (diff n)) 3 volume ∧ MemLp (orderedGradientValue (phase n)) 3 volume) ∧
    ∀ ε > 0, ∀ᶠ n in atTop,
      (eLpNorm (orderedGradientValue (diff n)) 3 volume).toReal ≤ 64 * A * R + ε ∧
      (eLpNorm (orderedGradientValue (phase n)) 3 volume).toReal ≤ 64 * A * R + ε := by
  intro U V E₁ E₂ C diff phase hWideMem hWide hCompMem hZero
  let S := fourierMultiplier (thinConeScalar m hη i o)
  have hId₁ (n : ℕ) (a : GradSlot) : diff n a = C n a + S (E₁ n a) :=
    (actualThinScreen_gradient_identities m wideInner wideOuter hm hη i o (z n) a.1 a.2).1
  have hId₂ (n : ℕ) (a : GradSlot) : phase n a = S (E₂ n a) :=
    (actualThinScreen_gradient_identities m wideInner wideOuter hm hη i o (z n) a.1 a.2).2
  have hWideRow₁ (n : ℕ) (a : GradSlot) := orderedGradientValue_component_L3 (E₁ n) (hWideMem n).1 a
  have hWideRow₂ (n : ℕ) (a : GradSlot) := orderedGradientValue_component_L3 (E₂ n) (hWideMem n).2 a
  have hThin₁ (n : ℕ) (a : GradSlot) := hScalar (E₁ n a) (hWideRow₁ n a).1
  have hThin₂ (n : ℕ) (a : GradSlot) := hScalar (E₂ n a) (hWideRow₂ n a).1
  have hSum (n : ℕ) (a : GradSlot) := complexL2_sum_L3 (C n a) (S (E₁ n a)) (hCompMem n a) (hThin₁ n a).1
  have hMem₁ (n : ℕ) (a : GradSlot) : MemLp (diff n a : E → ℂ) 3 volume := by rw [hId₁]; exact (hSum n a).1
  have hMem₂ (n : ℕ) (a : GradSlot) : MemLp (phase n a : E → ℂ) 3 volume := by rw [hId₂]; exact (hThin₂ n a).1
  refine ⟨fun n => ⟨(orderedGradientValue_L3_le_sum (diff n) (hMem₁ n)).1,
    (orderedGradientValue_L3_le_sum (phase n) (hMem₂ n)).1⟩, ?_⟩
  have hRows : ∀ ε > 0, ∀ᶠ n in atTop, ∀ a : GradSlot,
      (eLpNorm' (diff n a : E → ℂ) 3 volume).toReal ≤ A * R + ε ∧
        (eLpNorm' (phase n a : E → ℂ) 3 volume).toReal ≤ A * R + ε := by
    intro ε hε
    let d := (ε / 2) / (A + 1)
    have hd : 0 < d := by dsimp only [d]; positivity
    have hAd : A * d ≤ ε / 2 := by
      calc
        A * d ≤ (A + 1) * d := mul_le_mul_of_nonneg_right (by linarith) hd.le
        _ = ε / 2 := by dsimp only [d]; field_simp [(show A + 1 ≠ 0 by linarith)]
    apply eventually_all.2
    intro a
    filter_upwards [hWide d hd, (hZero a).eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))]
      with n hn hComp
    have hLeft := (hWideRow₁ n a).2.trans hn.1
    have hRight := (hWideRow₂ n a).2.trans hn.2
    rw [← complexL2_L3_norm_eq, ← complexL2_L3_norm_eq, hId₁, hId₂]
    rw [← complexL2_L3_norm_eq] at hComp
    constructor
    · refine (hSum n a).2.trans ?_
      have hThin := (hThin₁ n a).2.trans (mul_le_mul_of_nonneg_left hLeft hA)
      linarith only [hComp, hThin, hAd, mul_add A R d]
    · have hThin := (hThin₂ n a).2.trans (mul_le_mul_of_nonneg_left hRight hA)
      linarith only [hThin, hAd, hε, mul_add A R d]
  intro ε hε
  have hFinal₁ := orderedGradientValue_eventually_L3 diff (A * R) hMem₁
    (fun t ht => (hRows t ht).mono (fun _ hn a => (hn a).1)) ε hε
  have hFinal₂ := orderedGradientValue_eventually_L3 phase (A * R) hMem₂
    (fun t ht => (hRows t ht).mono (fun _ hn a => (hn a).2)) ε hε
  simpa only [mul_assoc] using hFinal₁.and hFinal₂

end Burnett.C02
