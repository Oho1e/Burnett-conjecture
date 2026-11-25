import Burnett.Analysis.CubicEnergy.AngularCorrection.RegularizedFirstOrderPairBound
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualDensity
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A07

open Burnett.A06 Burnett.A02.FrequencySplit MeasureTheory Metric Set Filter
open scoped BigOperators ContDiff ENNReal ComplexConjugate

abbrev FirstOrderLp (p : ℝ≥0∞) := Lp ℂ p (volume : Measure E)

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem extendSchwartzLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (A : SchwartzMap E ℂ →ₗ[ℂ] F) {K : ℝ} (hK : 0 ≤ K)
    (bound : ∀ f, ‖A f‖ ≤ K * ‖f.toLp p volume‖) :
    ∃ T : FirstOrderLp p →L[ℂ] F, ‖T‖ ≤ K ∧ ∀ f, T (f.toLp p volume) = A f := by
  let inj := (SchwartzMap.toLpCLM ℂ ℂ p (volume : Measure E)).toLinearMap
  let V := LinearMap.range inj
  let e := LinearEquiv.ofInjective inj (SchwartzMap.injective_toLp p volume)
  let B := A.comp e.symm.toLinearMap
  have hB (v : V) : ‖B v‖ ≤ K * ‖v‖ := by
    obtain ⟨f, rfl⟩ := e.surjective v
    change ‖A (e.symm (e f))‖ ≤ K * ‖f.toLp p volume‖
    rw [LinearEquiv.symm_apply_apply]
    exact bound f
  let B' := B.mkContinuous K hB
  have hd : Dense (V : Set (FirstOrderLp p)) := CMBilinearDual.schwartz_toLp_denseRange p hp
  have hD : DenseRange V.subtypeL := hd.denseRange_val
  have hU := V.subtypeₗᵢ.isometry.isUniformInducing
  let T := B'.extend V.subtypeL hD hU
  have hT (v : V) : T v = B v := ContinuousLinearMap.extend_eq B' V.subtypeL hD hU v
  have hBound (u : FirstOrderLp p) : ‖T u‖ ≤ K * ‖u‖ := by
    refine hD.induction_on u ?_ ?_
    · exact isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)
    · intro v
      change ‖T v‖ ≤ K * ‖v‖
      rw [hT]
      exact hB v
  refine ⟨T, ContinuousLinearMap.opNorm_le_bound T hK hBound, ?_⟩
  intro f
  change T (e f : FirstOrderLp p) = A f
  rw [hT]
  change A (e.symm (e f)) = A f
  rw [LinearEquiv.symm_apply_apply]

private def radianSchwartzEval (p : E) : SchwartzMap E ℂ →ₗ[ℂ] ℂ where
  toFun f := SchwartzMap.fourierTransformCLM ℂ f (tau⁻¹ • p)
  map_add' f g := by rw [map_add, SchwartzMap.add_apply]
  map_smul' c f := by
    rw [map_smul (SchwartzMap.fourierTransformCLM ℂ) c f, SchwartzMap.smul_apply]
    rfl

private theorem radianSchwartzEval_eq (f : SchwartzMap E ℂ) (p : E) :
    radianSchwartzEval p f = radianFourier f p := by
  have hτ : tau ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
  change SchwartzMap.fourierTransformCLM ℂ f (tau⁻¹ • p) = _
  rw [SchwartzMap.fourierTransformCLM_apply, ← radianFourier_scaled, smul_smul,
    mul_inv_cancel₀ hτ, one_smul]

private theorem integrable_pairWeight (b : OrderOneSymbol ℂ) (f u w : SchwartzMap E ℂ) :
    Integrable (radianHighPairWeight b f u w) :=
  integrable_radianHighPairWeight_of_orderOne b b.measurable_symbol
    (orderOneWeightedSeminorm ℂ 0 b) (apply_nonneg _ _) b.norm_apply_le_weightedSeminorm_zero f u w

private theorem pair_add_low (b : OrderOneSymbol ℂ) (u w f g : SchwartzMap E ℂ) :
    radianHighPair b (f + g : SchwartzMap E ℂ) u w =
      radianHighPair b f u w + radianHighPair b g u w := by
  unfold radianHighPair
  rw [← smul_add, ← integral_add (integrable_pairWeight b f u w) (integrable_pairWeight b g u w)]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  simp only [radianHighPairWeight, ← radianSchwartzEval_eq, map_add]
  ring

private theorem pair_smul_low (b : OrderOneSymbol ℂ) (u w f : SchwartzMap E ℂ) (c : ℂ) :
    radianHighPair b (c • f : SchwartzMap E ℂ) u w = c * radianHighPair b f u w := by
  unfold radianHighPair
  have heq : radianHighPairWeight b (c • f : SchwartzMap E ℂ) u w =
      fun p => c * radianHighPairWeight b f u w p := by
    funext p
    simp only [radianHighPairWeight, ← radianSchwartzEval_eq, map_smul, smul_eq_mul]
    ring
  rw [heq, integral_const_mul]
  simp only [Complex.real_smul]
  ring

private theorem pair_add_test (b : OrderOneSymbol ℂ) (f u v w : SchwartzMap E ℂ) :
    radianHighPair b f u (v + w : SchwartzMap E ℂ) =
      radianHighPair b f u v + radianHighPair b f u w := by
  unfold radianHighPair
  rw [← smul_add, ← integral_add (integrable_pairWeight b f u v) (integrable_pairWeight b f u w)]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  simp only [radianHighPairWeight, ← radianSchwartzEval_eq, map_add]
  ring

private theorem pair_smul_test (b : OrderOneSymbol ℂ) (f u w : SchwartzMap E ℂ) (c : ℂ) :
    radianHighPair b f u (c • w : SchwartzMap E ℂ) = conj c * radianHighPair b f u w := by
  unfold radianHighPair
  have heq : radianHighPairWeight b f u (c • w : SchwartzMap E ℂ) =
      fun p => conj c * radianHighPairWeight b f u w p := by
    funext p
    simp only [radianHighPairWeight, ← radianSchwartzEval_eq, map_smul, smul_eq_mul, map_mul]
    ring
  rw [heq, integral_const_mul]
  simp only [Complex.real_smul]
  ring

private def conjugateTestPair (b : OrderOneSymbol ℂ) (f u : SchwartzMap E ℂ) :
    SchwartzMap E ℂ →ₗ[ℂ] ℂ where
  toFun w := conj (radianHighPair b f u w)
  map_add' v w := by rw [pair_add_test, map_add]
  map_smul' c w := by
    rw [pair_smul_test, map_mul, starRingEnd_self_apply]
    rfl

private theorem inner_eq_of_schwartz {x y : FirstOrderLp 2}
    (h : ∀ w : SchwartzMap E ℂ, inner ℂ (w.toLp 2 volume) x = inner ℂ (w.toLp 2 volume) y) :
    x = y := by
  apply ext_inner_left ℂ
  intro v
  exact (CMBilinearDual.schwartz_toLp_denseRange 2 (by norm_num)).induction_on v
    (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)) h

/-- The original sesquilinear Fourier form gives an actual `L⁴ → L²` map
with fixed high input, by density in the test and low slots. -/
theorem exists_radianHighPair_L4_to_L2 (b : OrderOneSymbol ℂ) (u : SchwartzMap E ℂ)
    {K : ℝ} (hK : 0 ≤ K)
    (bound : ∀ f w : SchwartzMap E ℂ,
      ‖radianHighPair b f u w‖ ≤ K * ‖f.toLp 4 volume‖ * ‖w.toLp 2 volume‖) :
    ∃ T : FirstOrderLp 4 →L[ℂ] FirstOrderLp 2, ‖T‖ ≤ K ∧
      ∀ f w : SchwartzMap E ℂ, inner ℂ (w.toLp 2 volume) (T (f.toLp 4 volume)) =
        radianHighPair b f u w := by
  have dual (f : SchwartzMap E ℂ) : ∃ D : StrongDual ℂ (FirstOrderLp 2),
      ‖D‖ ≤ K * ‖f.toLp 4 volume‖ ∧ ∀ w : SchwartzMap E ℂ,
        D (w.toLp 2 volume) = conj (radianHighPair b f u w) :=
    extendSchwartzLp (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (conjugateTestPair b f u)
      (mul_nonneg hK (norm_nonneg _)) (fun w => by simpa [conjugateTestPair] using bound f w)
  choose D hD pairD using dual
  let y (f : SchwartzMap E ℂ) := (InnerProductSpace.toDual ℂ (FirstOrderLp 2)).symm (D f)
  have hy (f w : SchwartzMap E ℂ) : inner ℂ (w.toLp 2 volume) (y f) = radianHighPair b f u w := by
    rw [← inner_conj_symm]
    change conj (inner ℂ (y f) (w.toLp 2 volume)) = _
    dsimp only [y]
    rw [InnerProductSpace.toDual_symm_apply, pairD, starRingEnd_self_apply]
  let A : SchwartzMap E ℂ →ₗ[ℂ] FirstOrderLp 2 :=
    { toFun := y
      map_add' := fun f g => by
        apply inner_eq_of_schwartz
        intro w
        change inner ℂ (w.toLp 2 volume) (y (f + g)) = inner ℂ (w.toLp 2 volume) (y f + y g)
        rw [hy (f + g) w, inner_add_right, hy f w, hy g w]
        exact pair_add_low b u w f g
      map_smul' := fun c f => by
        apply inner_eq_of_schwartz
        intro w
        change inner ℂ (w.toLp 2 volume) (y (c • f)) = inner ℂ (w.toLp 2 volume) (c • y f)
        rw [hy (c • f) w, inner_smul_right, hy f w]
        exact pair_smul_low b u w f c }
  obtain ⟨T,hT,heq⟩ := extendSchwartzLp (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) A hK (fun f => by
    change ‖y f‖ ≤ K * ‖f.toLp 4 volume‖
    dsimp only [y]
    rw [LinearIsometryEquiv.norm_map]
    exact hD f)
  exact ⟨T,hT,fun f w => by rw [heq]; exact hy f w⟩

def highDerivativeLp4Sum (u : SchwartzMap E ℂ) : ℝ :=
  ∑ j : Fin 4, ‖(coordinateDerivative j u).toLp 4 volume‖

theorem highDerivativeLp4Sum_nonneg (u : SchwartzMap E ℂ) : 0 ≤ highDerivativeLp4Sum u :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- The Cartesian coefficient estimate after replacing the low Schwartz slot
by the whole `L⁴` space. The fixed infrared cutoff stays in the high symbol. -/
theorem exists_regularizedLowCartesian_L4_to_L2
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set Joint}, IsOpen V →
      closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V →
      ∀ (c : Joint → ℂ) (B : ℝ), 0 ≤ B → ContDiffOn ℝ ∞ c V →
      (∀ n ≤ 15, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1,
        ‖iteratedFDeriv ℝ n c z‖ ≤ B) →
      ∀ u : SchwartzMap E ℂ, ∃ T : FirstOrderLp 4 →L[ℂ] FirstOrderLp 2,
        ‖T‖ ≤ C * B * highDerivativeLp4Sum u ∧
        ∀ f w : SchwartzMap E ℂ, inner ℂ (w.toLp 2 volume) (T (f.toLp 4 volume)) =
          radianHighPair (regularizedLowCartesianSymbol η χ c) f u w := by
  obtain ⟨C,hC,pair⟩ := exists_regularizedLowCartesian_highPair_firstOrderBound
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  refine ⟨C.toReal,ENNReal.toReal_nonneg,?_⟩
  intro V hV hContains c B hB hc hjet u
  let b : OrderOneSymbol ℂ := ⟨regularizedLowCartesianSymbol η χ c,
    regularizedLowCartesianSymbol_mem_orderOneSymbolSubmodule η χ c hr hρ hR
      hη hzero hone hχ hcut hV hContains hc⟩
  have K0 : 0 ≤ C.toReal * B * highDerivativeLp4Sum u :=
    mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hB) (highDerivativeLp4Sum_nonneg u)
  apply exists_radianHighPair_L4_to_L2 b u K0
  intro f w
  have h := (pair hV hContains c B hB hc hjet f u w).1
  rw [show ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) by norm_num,
    show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] at h
  have hv (j : Fin 4) : eLpNorm (coordinateDerivative j u : E → ℂ) 4 volume ≠ ⊤ :=
    ((coordinateDerivative j u).memLp 4 volume).2.ne
  have hfin : C * ENNReal.ofReal B * eLpNorm (f : E → ℂ) 4 volume *
      (∑ j : Fin 4, eLpNorm (coordinateDerivative j u : E → ℂ) 4 volume) *
        eLpNorm (w : E → ℂ) 2 volume ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top hC.ne ENNReal.ofReal_ne_top) (f.memLp 4 volume).2.ne)
    (ENNReal.sum_ne_top.mpr (fun j _ => hv j))) (w.memLp 2 volume).2.ne
  have h' := ENNReal.toReal_mono hfin h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB,
    ENNReal.toReal_sum (fun j _ => hv j), ← SchwartzMap.norm_toLp] at h'
  simpa only [highDerivativeLp4Sum, mul_assoc, mul_left_comm, mul_comm] using h'

end Burnett.A07
