import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator
import Burnett.Analysis.CubicEnergy.AngularCorrection.CorrectionAngularFullBounds
import Burnett.Analysis.CubicEnergy.AngularCorrection.CorrectionLipschitzDensity
import Burnett.Analysis.CubicEnergy.AngularCorrection.CorrectionLipschitzFourierLimit
import Burnett.Analysis.CubicEnergy.AngularCorrection.CorrectionSymbolRepresentative

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

namespace Burnett.A08

open Filter MeasureTheory Burnett.A08 Burnett.A07 Burnett.A06 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped ComplexConjugate ENNReal NNReal Topology

open private inner_coefficientCommutatorOutput
  from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator
open private extendSchwartzLp
  from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2

private theorem existsLp2_of_tested_limit
    (q : ℕ → LP2) (l : Test → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hLim : ∀ w, Tendsto (fun n => inner ℂ (q n) (w.toLp 2 volume)) atTop (𝓝 (l w)))
    (hNorm : ∀ w, ‖l w‖ ≤ K * ‖w.toLp 2 volume‖) :
    ∃ y : LP2, ‖y‖ ≤ K ∧ ∀ w : Test, inner ℂ y (w.toLp 2 volume) = l w := by
  let a (n : ℕ) : Test →ₗ[ℂ] ℂ :=
    (innerSL ℂ (q n)).toLinearMap.comp (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
  have ha (w : Test) : Tendsto (fun n => a n w) atTop (𝓝 (l w)) := hLim w
  let A : Test →ₗ[ℂ] ℂ :=
    { toFun := l
      map_add' := fun f g => tendsto_nhds_unique (ha (f+g))
        (by simpa only [map_add] using (ha f).add (ha g))
      map_smul' := fun c f => tendsto_nhds_unique (ha (c • f))
        (by simpa only [map_smul, RingHom.id_apply] using (ha f).const_smul c) }
  obtain ⟨U, hU, hApply⟩ := extendSchwartzLp (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) A hK hNorm
  let y := (InnerProductSpace.toDual ℂ LP2).symm U
  refine ⟨y, by simpa only [y, LinearIsometryEquiv.norm_map] using hU, ?_⟩
  intro w
  rw [InnerProductSpace.toDual_symm_apply, hApply]
  rfl

private theorem realSchwartzRoughOutput_pair
    (b : Joint → ℂ) (H : E → ℂ) (T : Test → LP2)
    (hT : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (T u) = radianHighPair b H u w)
    (d : SchwartzMap E ℝ) (v w : Test) :
    inner ℂ (w.toLp 2 volume) (coefficientCommutatorOutput d T v) =
      -radianHighCommutatorPair b d H v w := by
  have mul_eq (u : Test) : (realSchwartzMultiply d u : E → ℂ) =
      fun x => (d x : ℂ) * u x := funext (realSchwartzMultiply_apply d u)
  rw [inner_coefficientCommutatorOutput, hT, hT, mul_eq, mul_eq, radianHighCommutatorPair, neg_sub]

/-- The original two operator commutators on the high slot extend from
Schwartz coefficients to any globally Lipschitz real coefficient. Both
L² outputs realize the distributional Fourier pairings with the actual
symbol and its actual high adjoint. -/
theorem exists_full_globalLipschitz_rough_outputs :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ {η χ : ℝ → ℝ} {F : Joint × RotationSpace → ℂ} {M C₀ C₁ : ℝ}
      (_ : OriginalAngularCutoff η χ F M C₀ C₁)
      {b : Joint → ℂ} {B : ℝ}, Measurable b → 0 ≤ B →
      (∀ p, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖)) →
      b =ᵐ[volume] originalRegularizedAngularSymbol η χ F →
      ∀ (d : E → ℝ) (L : ℝ≥0), LipschitzWith L d → ∀ H v : Test,
      let B₀ := 2 * (C₁ * M * ((C*L : ℝ≥0) : ℝ) * ‖H.toLp 4 volume‖) * ‖v.toLp 4 volume‖
      ∃ U V : LP2, ‖U‖ ≤ B₀ ∧ ‖V‖ ≤ B₀ ∧ ∀ w : Test,
        inner ℂ (w.toLp 2 volume) U =
          -radianHighCommutatorPair (originalRegularizedAngularSymbol η χ F) d H v w ∧
        inner ℂ (w.toLp 2 volume) V =
          -radianHighCommutatorPair (highAdjointSymbol (originalRegularizedAngularSymbol η χ F))
            d (fun x => conj (H x)) v w := by
  obtain ⟨C,hC,approx⟩ := exists_realSchwartz_normalized_Lipschitz_approximation
  refine ⟨C,hC,?_⟩
  intro η χ F M C₀ C₁ P b B hb hB hsize hRep d L hd H v B₀
  obtain ⟨D,hDzero,hDlip,hDlim⟩ := approx d L hd
  let a := originalRegularizedAngularSymbol η χ F
  have hC₁ := P.nonnegRough
  have hM := P.nonnegM
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
  have hLimit (u w : Test) :
      Tendsto (fun n => radianHighCommutatorPair a (D n) H u w) atTop
        (𝓝 (radianHighCommutatorPair a d H u w)) := by
    have h := tendsto_radianHighCommutatorPair_normalizedCoefficient
      b hb B hB hsize (fun n x => D n x) (fun x => d x-d 0) (C*L) hDlip hDzero hDlim H u w
    rw [radianHighCommutatorPair_sub_value_at_zero b hb B hB hsize d L hd H u w] at h
    simpa only [radianHighCommutatorPair_congr_ae_symbol hRep] using h
  let U' (n : ℕ) := coefficientCommutatorOutput (D n) (P.fullForward H) v
  let V' (n : ℕ) := coefficientCommutatorOutput (D n) (P.fullAdjoint H) v
  let targetU (w : Test) := -conj (radianHighCommutatorPair a d H v w)
  let targetV (w : Test) := radianHighCommutatorPair a d H w v
  have hTestU (n : ℕ) (w : Test) :
      inner ℂ (U' n) (w.toLp 2 volume) = -conj (radianHighCommutatorPair a (D n) H v w) := by
    rw [← inner_conj_symm]
    rw [show inner ℂ (w.toLp 2 volume) (U' n) = _ from
      realSchwartzRoughOutput_pair a H (P.fullForward H) (fun u w => (P.fullPairs H u w).1) (D n) v w, map_neg]
  have hTestV (n : ℕ) (w : Test) :
      inner ℂ (V' n) (w.toLp 2 volume) = radianHighCommutatorPair a (D n) H w v := by
    rw [← inner_conj_symm]
    rw [show inner ℂ (w.toLp 2 volume) (V' n) = _ from
      realSchwartzRoughOutput_pair (highAdjointSymbol a) (fun x => conj (H x)) (P.fullAdjoint H)
        (fun u w => (P.fullPairs H u w).2) (D n) v w]
    rw [radianHighCommutatorPair_highAdjoint, neg_neg, starRingEnd_self_apply]
  have hLimU (w : Test) : Tendsto (fun n => inner ℂ (U' n) (w.toLp 2 volume)) atTop (𝓝 (targetU w)) :=
    ((Complex.continuous_conj.continuousAt.tendsto.comp (hLimit v w)).neg).congr (fun n => (hTestU n w).symm)
  have hLimV (w : Test) : Tendsto (fun n => inner ℂ (V' n) (w.toLp 2 volume)) atTop (𝓝 (targetV w)) :=
    (hLimit w v).congr (fun n => (hTestV n w).symm)
  have normU (w : Test) : ‖targetU w‖ ≤ B₀ * ‖w.toLp 2 volume‖ := by
    simp only [targetU, norm_neg, Complex.norm_conj]
    exact le_of_tendsto' (hLimit v w).norm
      (fun n => (P.full_realSchwartz_rough_bounds (D n) (C*L) (hDlip n) H v w).1)
  have normV (w : Test) : ‖targetV w‖ ≤ B₀ * ‖w.toLp 2 volume‖ := by
    exact le_of_tendsto' (hLimit w v).norm (fun n => by
      simpa only [B₀, mul_assoc, mul_comm, mul_left_comm] using
        (P.full_realSchwartz_rough_bounds (D n) (C*L) (hDlip n) H w v).2)
  obtain ⟨U,hU,testU⟩ := existsLp2_of_tested_limit U' targetU B₀ hB₀ hLimU normU
  obtain ⟨V,hV,testV⟩ := existsLp2_of_tested_limit V' targetV B₀ hB₀ hLimV normV
  refine ⟨U,V,hU,hV,fun w => ⟨?_,?_⟩⟩
  · rw [← inner_conj_symm, testU]
    change conj (-conj (radianHighCommutatorPair a d H v w)) = _
    rw [map_neg, starRingEnd_self_apply]
  · rw [← inner_conj_symm, testV, radianHighCommutatorPair_highAdjoint, neg_neg]

end Burnett.A08
