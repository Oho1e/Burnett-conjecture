import Burnett.Analysis.TransportPatches.WideCompatibleWindowNorm
import Burnett.Analysis.TransportPatches.WideProjectedGradientLp
import Burnett.Analysis.TransportPatches.PatchProjectedLpScale
import Burnett.Analysis.TransportPatches.FrozenErrorInterpolation

/-! Interpolate the two actual wide errors using C03 norms of their common input. -/
set_option autoImplicit false
set_option maxRecDepth 5300
set_option maxHeartbeats 7800000

noncomputable section

namespace Burnett.C02

open Set Metric Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol Burnett.V06
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix projectionMatrixDerivative projectionFullSchwartz)
open Burnett.C03 (ProjectedPatchLpBounds)
open scoped BigOperators ContDiff ENNReal Topology

private theorem finiteLp_eLpNorm_eq (p : ℝ) (h : 0 < p) (f : E → ℂ) :
    eLpNorm f (ENNReal.ofReal p) volume = eLpNorm' f p volume := by
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr h) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal h.le]

private theorem eLpNorm'_two_eq_norm (v : ComplexL2 E) :
    (eLpNorm' (v : E → ℂ) 2 volume).toReal = ‖v‖ := by
  rw [Lp.norm_def, eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)]
  norm_num

theorem orderedOriginalGradientL2_le_of_projectedPatchLp (z : ProjectionSchwartzMatrix)
    (P : Set E) (Cv Cg : ℝ) (hCg : 0 ≤ Cg) (h : ProjectedPatchLpBounds 2 z P Cv Cg) :
    orderedGradientL2Norm originalProjectedMatrixMultiplier z ≤
      8 * Cg * ((volume : Measure E) P).toReal ^ (1 / 2 : ℝ) := by
  let R := Cg * ((volume : Measure E) P).toReal ^ (1 / 2 : ℝ)
  have hR : 0 ≤ R := mul_nonneg hCg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hRow (b : Index) (k : OrderedPair) :
      ‖multiplierCoordinateDerivative originalProjectedMatrixMultiplier z b k‖ ≤ R := by
    let f := projectionMatrixDerivative b (projectionFullSchwartz z) k.1 k.2
    have hEntry := ((h k.1 k.2).2 b).1
    rw [originalProjectedMatrixMultiplier_derivative_eq_schwartz, Burnett.P01.projectionFullSchwartz_coordinateDerivative]
    change ‖f.toLp 2 volume‖ ≤ R
    rw [Lp.norm_def, eLpNorm_congr_ae (f.coeFn_toLp 2 volume)]
    simpa only [f, R, ENNReal.toReal_rpow, show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] using hEntry
  change orderedGradientL2Norm originalProjectedMatrixMultiplier z ≤ (8 * Cg) * _
  rw [mul_assoc]
  change orderedGradientL2Norm originalProjectedMatrixMultiplier z ≤ 8 * R
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hR)).1
  change ‖WithLp.toLp 2 (fun a : Index × OrderedPair =>
    multiplierCoordinateDerivative originalProjectedMatrixMultiplier z a.1 a.2)‖ ^ 2 ≤ _
  rw [multiplierCoordinateDerivative_norm_sq]
  calc
    _ ≤ ∑ _b : Index, ∑ _k : OrderedPair, R ^ 2 :=
      Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun k _ =>
        (sq_le_sq₀ (norm_nonneg _) hR).2 (hRow b k)))
    _ = (8 * R) ^ 2 := by
      change (∑ _b : Fin 4, ∑ _k : Fin 4 × Fin 4, R ^ 2) = _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

/-- C03 supplies Lᵖ of the first derivatives of the actual projected input.
Both errors then interpolate with their own L² bounds on the full space. -/
theorem exists_widePatchErrors_L3 (p : ℝ) (hp : 3 < p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (inner outer : ℝ) (m : ScreenMatrix)
      (hm : WideScreenFrequencySmooth inner outer m) (J : ℝ), 0 ≤ J →
      (∀ k i : OrderedPair, ∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1,
        ‖iteratedFDeriv ℝ n (fun η : E => (frozenScreenErrorAngular inner outer m hm).matrix η k i) ξ‖ ≤ J ∧
        ‖iteratedFDeriv ℝ n (fun η : E => (frozenPhaseErrorAngular inner outer m hm).matrix η k i) ξ‖ ≤ J) →
      ∀ (z : ℕ → ProjectionSchwartzMatrix) (P : Set E), IsCompact P →
      ∀ (C₂ Cₚ d : ℝ), 0 ≤ C₂ → 0 ≤ Cₚ → 0 ≤ d → ∀ (val : ℕ → ℝ),
      let T₁ := actualFrozenScreenErrorMultiplier inner outer m hm
      let T₂ := actualFrozenPhaseErrorMultiplier inner outer m hm
      let V := ((volume : Measure E) P).toReal
      (∀ ε > 0, ∀ᶠ n in atTop,
        orderedGradientL2Norm T₁ (z n) ≤ C₂ * d * V ^ (1 / 2 : ℝ) + ε ∧
        orderedGradientL2Norm T₂ (z n) ≤ C₂ * d * V ^ (1 / 2 : ℝ) + ε) →
      (∀ᶠ n in atTop, ProjectedPatchLpBounds p (z n) P (val n) Cₚ) →
      let R := C₂ ^ frozenErrorExponent p * (16 * (A * J) * Cₚ) ^ (1 - frozenErrorExponent p) *
        d ^ frozenErrorExponent p * V ^ (1 / 3 : ℝ)
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ b : Index, ∀ k : OrderedPair,
        (eLpNorm' (multiplierCoordinateDerivative T₁ (z n) b k : E → ℂ) 3 volume).toReal ≤ R + ε ∧
        (eLpNorm' (multiplierCoordinateDerivative T₂ (z n) b k : E → ℂ) 3 volume).toReal ≤ R + ε := by
  have hp₀ : 0 < p := by linarith
  obtain ⟨A, hA, hOp⟩ := exists_actualWide_projectedGradient_Lp p (by linarith)
  refine ⟨A, hA, ?_⟩
  intro inner outer m hm J hJ hJets z P hP C₂ Cₚ d hC₂ hCₚ hd val T₁ T₂ V hL₂ hLp R ε hε
  let vol := (volume : Measure E) P
  let power := vol ^ (1 / p)
  let Aₚ := 16 * (A * J) * Cₚ
  let g (n : ℕ) (b : Index) (i : OrderedPair) := projectionMatrixDerivative b (projectionFullSchwartz (z n)) i.1 i.2
  have hAJ : 0 ≤ A * J := mul_nonneg hA hJ
  have hAₚ : 0 ≤ Aₚ := mul_nonneg (mul_nonneg (by norm_num) hAJ) hCₚ
  have hPower : power < ⊤ := ENNReal.rpow_lt_top_of_nonneg (one_div_pos.mpr hp₀).le hP.measure_lt_top.ne
  have hInput (n : ℕ) (h : ProjectedPatchLpBounds p (z n) P (val n) Cₚ) (b : Index) (i : OrderedPair) :
      eLpNorm (g n b i : E → ℂ) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal Cₚ * power := by
    have hf := ((g n b i).memLp (ENNReal.ofReal p) volume).eLpNorm_lt_top
    have hF : ENNReal.ofReal Cₚ * power < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hPower
    apply (ENNReal.toReal_le_toReal hf.ne hF.ne).1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCₚ]
    exact ((h i.1 i.2).2 b).1
  have hRow (f : ℕ → ComplexL2 E) (b : Index)
      (hOp : ∀ n, MemLp (f n : E → ℂ) (ENNReal.ofReal p) volume ∧
        eLpNorm (f n : E → ℂ) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (A * J) *
          ∑ i : OrderedPair, eLpNorm (g n b i : E → ℂ) (ENNReal.ofReal p) volume)
      (hTwo : ∀ ε > 0, ∀ᶠ n in atTop,
        (eLpNorm' (f n : E → ℂ) 2 volume).toReal ≤ C₂ * d * V ^ (1 / 2 : ℝ) + ε) :
      ∀ᶠ n in atTop, (eLpNorm' (f n : E → ℂ) 3 volume).toReal ≤ R + ε := by
    have hFinite₂ (n : ℕ) : eLpNorm' (f n : E → ℂ) 2 volume < ⊤ := by
      rw [← finiteLp_eLpNorm_eq 2 (by norm_num), show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
      exact Lp.eLpNorm_lt_top (f n)
    have hFiniteₚ (n : ℕ) : eLpNorm' (f n : E → ℂ) p volume < ⊤ := by
      rw [← finiteLp_eLpNorm_eq p hp₀]
      exact (hOp n).1.eLpNorm_lt_top
    have hPbound : ∀ᶠ n in atTop, (eLpNorm' (f n : E → ℂ) p volume).toReal ≤ Aₚ * V ^ (1 / p) := by
      filter_upwards [hLp] with n hn
      have hSum : (∑ i : OrderedPair, eLpNorm (g n b i : E → ℂ) (ENNReal.ofReal p) volume) ≤
          16 * (ENNReal.ofReal Cₚ * power) := by
        calc
          _ ≤ ∑ _i : OrderedPair, (ENNReal.ofReal Cₚ * power) := Finset.sum_le_sum (fun i _ => hInput n hn b i)
          _ = _ := by
            simp only [Finset.sum_const, Finset.card_univ, show Fintype.card OrderedPair = 16 by decide, nsmul_eq_mul]
            norm_num
      have hNe : ENNReal.ofReal (A * J) * (16 * (ENNReal.ofReal Cₚ * power)) < ⊤ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top (by simp)
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hPower))
      rw [← finiteLp_eLpNorm_eq p hp₀]
      have hBound := ENNReal.toReal_mono hNe.ne ((hOp n).2.trans (mul_le_mul_left' hSum _))
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hAJ,
        ENNReal.toReal_ofReal hCₚ] at hBound
      simpa only [Aₚ, V, vol, power, show (16 : ℝ≥0∞).toReal = 16 by norm_num,
        ← ENNReal.toReal_rpow, mul_assoc, mul_left_comm, mul_comm] using hBound
    have hPupper (t : ℝ) (ht : 0 < t) : ∀ᶠ n in atTop,
        (eLpNorm' (f n : E → ℂ) p volume).toReal ≤ Aₚ * V ^ (1 / p) + t :=
      hPbound.mono (fun _ h => h.trans (le_add_of_nonneg_right ht.le))
    exact frozenError_eventually_window hp (fun n => (f n : E → ℂ))
      (fun n => Lp.aestronglyMeasurable (f n)) hFinite₂ hFiniteₚ C₂ Aₚ d V hC₂ hAₚ hd ENNReal.toReal_nonneg
      hTwo hPupper ε hε
  have hL2Row (T : ClassicalMatrixMultiplier OrderedPair) (b : Index) (k : OrderedPair)
      (h : ∀ t > 0, ∀ᶠ n in atTop, orderedGradientL2Norm T (z n) ≤ C₂ * d * V ^ (1 / 2 : ℝ) + t) :
      ∀ t > 0, ∀ᶠ n in atTop,
        (eLpNorm' (multiplierCoordinateDerivative T (z n) b k : E → ℂ) 2 volume).toReal ≤
          C₂ * d * V ^ (1 / 2 : ℝ) + t := by
    intro t ht
    filter_upwards [h t ht] with n hn
    rw [eLpNorm'_two_eq_norm]
    exact (PiLp.norm_apply_le (WithLp.toLp 2 (fun a : Index × OrderedPair =>
      multiplierCoordinateDerivative T (z n) a.1 a.2)) (b, k)).trans hn
  exact eventually_all.2 (fun b => eventually_all.2 (fun k =>
    (hRow (fun n => multiplierCoordinateDerivative T₁ (z n) b k) b
      (fun n => (hOp inner outer m hm J hJ hJets (z n) b k).1)
      (hL2Row T₁ b k (fun t ht => (hL₂ t ht).mono (fun _ h => h.1)))).and
    (hRow (fun n => multiplierCoordinateDerivative T₂ (z n) b k) b
      (fun n => (hOp inner outer m hm J hJ hJets (z n) b k).2)
      (hL2Row T₂ b k (fun t ht => (hL₂ t ht).mono (fun _ h => h.2))))))

end Burnett.C02
