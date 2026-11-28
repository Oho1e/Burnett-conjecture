import Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalCutoffErrorBounds

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.C01

open Filter MeasureTheory Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal Topology

/-- A fixed order-zero cutoff commutator contributes a vanishing cubic
error on the raw and localized fields with their uniform first-jet bounds. -/
theorem tendsto_principalVariation_cutoff_commutator_zero {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (A : ℝ≥0∞) (hA : A < ⊤)
    (hC : ∀ a b i j k, eLpNorm (C a b i j k : E → ℂ) ⊤ volume ≤ A)
    (z u : ℕ → J → SchwartzMap E ℂ)
    (Q : SchwartzMap E ℂ → E → ℂ) (K : ℝ≥0∞) (hK : K < ⊤) (hQ : SchwartzOrderZeroJetBound Q K K)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hLim : Tendsto ε atTop (𝓝 0))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hz : ∀ n i, eLpNorm (z n i : E → ℂ) (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (ε n))
    (hu : ∀ n i, eLpNorm (u n i : E → ℂ) (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (ε n))
    (hdz : ∀ n a i, eLpNorm (energyPartial a (z n i) : E → ℂ) (ENNReal.ofReal 3) volume ≤ M)
    (hdu : ∀ n a i, eLpNorm (energyPartial a (u n i) : E → ℂ) (ENNReal.ofReal 3) volume ≤ M) :
    let F (n : ℕ) := principalVariationDensity (fun a b i j k => C a b i j k)
      (u n) (fun i => Q (z n i))
    (∀ n, Integrable (F n)) ∧ Tendsto (fun n => ∫ x, F n x) atTop (𝓝 0) := by
  intro F
  let T := Index × Index × J × J × J
  let p := ENNReal.ofReal 3
  let Y (n : ℕ) := ENNReal.ofReal (ε n)
  let D (n : ℕ) := K * M + K * Y n
  have hValue (n : ℕ) (i : J) :
      MemLp (Q (z n i)) p volume ∧ eLpNorm (Q (z n i)) p volume ≤ K * Y n := by
    obtain ⟨hLp,hB,_,_⟩ := hQ (z n i)
    exact ⟨hLp,hB.trans (mul_le_mul_left' (hz n i) K)⟩
  have hDerivative (n : ℕ) (a : Index) (i : J) :
      MemLp (actualCoordinateJet (Q (z n i)) a) p volume ∧
        eLpNorm (actualCoordinateJet (Q (z n i)) a) p volume ≤ D n := by
    obtain ⟨_,_,_,hJet⟩ := hQ (z n i)
    exact ⟨(hJet a).1, (hJet a).2.trans
      (add_le_add (mul_le_mul_left' (hdz n a i) K) (mul_le_mul_left' (hz n i) K))⟩
  have est (n : ℕ) : Integrable (F n) ∧
      ‖∫ x, F n x‖ₑ ≤ (Fintype.card T : ℝ≥0∞) * A * ((K * Y n) * M^2 + 2 * Y n * D n * M) :=
    principalVariation_cutoff_error_integral_bound C (u n) (fun i => Q (z n i))
      A (Y n) M (K * Y n) (D n) hC (hu n) (hdu n) (hValue n) (hDerivative n)
  refine ⟨fun n => (est n).1, tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  let D₀ := K * M + K
  let L : ℝ≥0∞ := (Fintype.card T : ℝ≥0∞) * A * (K * M^2 + 2 * D₀ * M)
  have hD₀ : D₀ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hK hM,hK⟩
  have hL : L < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) hA)
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hK (ENNReal.pow_lt_top hM),
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) hD₀) hM⟩)
  have hTail : ∀ᶠ n in atTop, ‖∫ x, F n x‖ ≤ L.toReal * ε n := by
    filter_upwards [hLim.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with n hn
    have hY : Y n ≤ 1 := (ENNReal.ofReal_le_ofReal hn).trans_eq ENNReal.ofReal_one
    have hD : D n ≤ D₀ := by
      exact add_le_add_left ((mul_le_mul_left' hY K).trans_eq (mul_one K)) _
    have hNorm : ‖∫ x, F n x‖ₑ ≤ L * Y n := by
      calc
        _ ≤ (Fintype.card T : ℝ≥0∞) * A * ((K * Y n) * M^2 + 2 * Y n * D n * M) := (est n).2
        _ ≤ (Fintype.card T : ℝ≥0∞) * A * ((K * Y n) * M^2 + 2 * Y n * D₀ * M) := by gcongr
        _ = _ := by dsimp only [L]; ring
    have real := ENNReal.toReal_mono (ENNReal.mul_ne_top hL.ne ENNReal.ofReal_ne_top) hNorm
    simpa only [Y, toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hε n)] using real
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hTail ?_
  have hConst : Tendsto (fun _ : ℕ => L.toReal) atTop (𝓝 L.toReal) := tendsto_const_nhds
  simpa only [mul_zero] using hConst.mul hLim

end Burnett.C01
