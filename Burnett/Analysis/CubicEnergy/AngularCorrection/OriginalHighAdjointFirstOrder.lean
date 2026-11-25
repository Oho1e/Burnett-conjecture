import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularSecondExponent
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularDerivativeCommutator

set_option autoImplicit false
set_option maxHeartbeats 9000000

noncomputable section

namespace Burnett.A07

open Burnett.A06 Burnett.A02.FrequencySplit Burnett.Fourier MeasureTheory Metric Set
open scoped BigOperators ComplexConjugate ContDiff ENNReal

open private exists_actualHarmonicLp4_multiplier from Burnett.Analysis.CubicEnergy.AngularCorrection.ActualAngularFirstOrderBound
open private extendSchwartzLp from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
open private radianHighInputLinear from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularSecondExponent

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem norm_le_of_firstOrderMass
    (f u w : SchwartzMap E ℂ) (z : ℂ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    {B : ℝ} (hB : 0 ≤ B)
    (h : ‖z‖ₑ ≤ C * ENNReal.ofReal B * eLpNorm (f : E → ℂ) (ENNReal.ofReal 4) volume *
      (∑ j : Fin 4, eLpNorm (coordinateDerivative j u : E → ℂ) (ENNReal.ofReal 4) volume) *
        eLpNorm (w : E → ℂ) (ENNReal.ofReal 2) volume) :
    ‖z‖ ≤ (C.toReal * B * highDerivativeLp4Sum u * ‖w.toLp 2 volume‖) * ‖f.toLp 4 volume‖ := by
  simp only [ENNReal.ofReal_ofNat] at h
  have finite (j : Fin 4) : eLpNorm (coordinateDerivative j u : E → ℂ) 4 volume ≠ ⊤ :=
    ((coordinateDerivative j u).memLp 4 volume).2.ne
  have boundFinite : C * ENNReal.ofReal B * eLpNorm (f : E → ℂ) 4 volume *
      (∑ j : Fin 4, eLpNorm (coordinateDerivative j u : E → ℂ) 4 volume) *
        eLpNorm (w : E → ℂ) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (f.memLp 4 volume).2.ne)
      (ENNReal.sum_ne_top.mpr fun j _ => finite j)) (w.memLp 2 volume).2.ne
  have estimate := ENNReal.toReal_mono boundFinite h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB,
    ENNReal.toReal_sum (fun j _ => finite j), ← SchwartzMap.norm_toLp] at estimate
  simpa only [highDerivativeLp4Sum, mul_assoc, mul_left_comm, mul_comm] using estimate

private theorem exists_originalAngular_highAdjoint_representation
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)},
      IsOpen W → Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ 27, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      ∀ H u : SchwartzMap E ℂ, ∃ z : FirstOrderLp 2,
        ‖z‖ ≤ C * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u ∧
        ∀ w : SchwartzMap E ℂ, inner ℂ (w.toLp 2 volume) z =
          conj (radianHighPair (originalRegularizedAngularSymbol η χ F) H w u) := by
  obtain ⟨Cb, hCb, modeBound⟩ := exists_regularizedLowCartesian_highPair_firstOrderBound
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  obtain ⟨_, _, cartesian⟩ := exists_regularizedLowCartesian_L4_to_L2
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  obtain ⟨Cc, hCc, coefficient⟩ := exists_smoothComplexAngularCoefficient_jet15 (E := Joint)
  obtain ⟨Cm, hCm, harmonics⟩ := exists_actualHarmonicLp4_multiplier
  choose m Y hm hYnorm hY using harmonics
  let C := Cb.toReal * Cc * Cm
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hCc) hCm
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro F W hW hContains hF M hM hjet H u
  have hQ : IsCompact (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) :=
    (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  obtain ⟨V, hV, hQV, jet⟩ := coefficient hW hQ hContains hF M hM hjet
  let c (i : HarmonicMode) := jointSphereHarmonicCoefficientComplex F i
  let J (i : HarmonicMode) := Cc * (((i.1 : ℝ) + 1)^12)⁻¹ * M
  have hJ (i : HarmonicMode) : 0 ≤ J i := by dsimp [J]; positivity
  let b (i : HarmonicMode) : OrderOneSymbol ℂ :=
    ⟨regularizedLowCartesianSymbol η χ (c i),
      regularizedLowCartesianSymbol_mem_orderOneSymbolSubmodule η χ _ hr hρ hR hη hzero hone
        hχ hcut hV hQV (jet i).1⟩
  let mode (i : HarmonicMode) := angularModeSymbol η χ F i
  have integrable (i : HarmonicMode) (w : SchwartzMap E ℂ) :
      Integrable (radianHighPairWeight (mode i) H w u) := by
    have hAngular : Measurable (sphereHarmonicMultiplierSymbol i.1 i.2 : E → ℝ) :=
      measurable_of_continuousOn_compl_singleton 0 (sphereHarmonicRadialSymbol_contDiffOn _ _).continuousOn
    have hMode : Measurable (mode i) :=
      (Complex.continuous_ofReal.measurable.comp (hAngular.comp measurable_fst)).mul (b i).measurable_symbol
    apply integrable_radianHighPairWeight_of_orderOne (mode i) hMode
      ((m i).bound * orderOneWeightedSeminorm ℂ 0 (b i))
      (mul_nonneg (m i).bound_nonneg (apply_nonneg _ _))
    intro p
    change ‖(sphereHarmonicMultiplierSymbol i.1 i.2 p.1 : ℂ) * (b i : Joint → ℂ) p‖ ≤ _
    rw [norm_mul, ← hm i p.1, mul_assoc]
    exact mul_le_mul ((m i).norm_le _) ((b i).norm_apply_le_weightedSeminorm_zero p)
      (norm_nonneg _) (m i).bound_nonneg
  let Aᵢ (i : HarmonicMode) := radianHighInputLinear (mode i) H u (integrable i)
  let pair (w : SchwartzMap E ℂ) := radianHighPair (originalRegularizedAngularSymbol η χ F) H w u
  have series (w : SchwartzMap E ℂ) : HasSum (fun i => Aᵢ i w) (pair w) :=
    originalRegularizedAngularPair_hasSum_of_smoothProfile
      η χ hr hρ hR hη hzero hone hχ hcut hW hContains hF hM hjet H w u
  let A : SchwartzMap E ℂ →ₗ[ℂ] ℂ :=
    { toFun := pair
      map_add' := fun v w =>
        (series (v + w)).unique (by simpa only [map_add] using (series v).add (series w))
      map_smul' := fun a w =>
        (series (a • w)).unique (by simpa only [map_smul, RingHom.id_apply] using (series w).const_smul a) }
  let H₄ := H.toLp 4 volume
  have testBound (w : SchwartzMap E ℂ) :
      ‖A w‖ ≤ (2 * C * M * ‖H₄‖ * highDerivativeLp4Sum u) * ‖w.toLp 2 volume‖ := by
    let U := C * M * ‖H₄‖ * highDerivativeLp4Sum u * ‖w.toLp 2 volume‖
    have hU : 0 ≤ U :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hM) (norm_nonneg _))
        (highDerivativeLp4Sum_nonneg u)) (norm_nonneg _)
    have majorant (i : HarmonicMode) : ‖Aᵢ i w‖ ≤ U / ((i.1 : ℝ) + 1)^5 := by
      obtain ⟨B, _, hB⟩ := cartesian hV hQV (c i) (J i) (hJ i) (jet i).1 (jet i).2 w
      let D := Cb.toReal * J i * highDerivativeLp4Sum u * ‖w.toLp 2 volume‖
      have hD : 0 ≤ D := mul_nonneg
        (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (hJ i)) (highDerivativeLp4Sum_nonneg u))
        (norm_nonneg _)
      have bound (f : FirstOrderLp 4) : ‖inner ℂ (u.toLp 2 volume) (B f)‖ ≤ D * ‖f‖ := by
        refine (CMBilinearDual.schwartz_toLp_denseRange 4 (by norm_num)).induction_on f ?_ ?_
        · exact isClosed_le (continuous_const.inner B.continuous).norm (continuous_const.mul continuous_norm)
        · intro f
          rw [hB, ← Complex.norm_conj, ← radianHighPair_highAdjoint]
          exact norm_le_of_firstOrderMass f u w _ hCb.ne (hJ i)
            (modeBound hV hQV (c i) (J i) (hJ i) (jet i).1 (jet i).2 f u w).2
      have identified : inner ℂ (u.toLp 2 volume) (B (Y i H₄)) = Aᵢ i w :=
        physicalAngularMultiplier_pair_eq (b i) w H u i (m i) (hm i) (Y i)
          (hY i H (H.memLp 2 volume) (H.memLp 4 volume)) B hB
      have hi : 0 < (i.1 : ℝ) + 1 := by positivity
      calc
        _ ≤ D * ‖Y i H₄‖ := identified ▸ bound (Y i H₄)
        _ ≤ D * (Cm * ((i.1 : ℝ) + 1)^7 * ‖H₄‖) :=
          mul_le_mul_of_nonneg_left
            (((Y i).le_opNorm H₄).trans (mul_le_mul_of_nonneg_right (hYnorm i) (norm_nonneg _))) hD
        _ = _ := by
          dsimp [D, U, C, J]
          field_simp [hi.ne']
    change ‖pair w‖ ≤ _
    rw [← (series w).tsum_eq]
    exact (harmonic_series_estimate _ hU majorant).fullBound.trans_eq (by dsimp [U]; ring)
  have hK : 0 ≤ 2 * C * M * ‖H₄‖ * highDerivativeLp4Sum u :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) hM) (norm_nonneg _))
      (highDerivativeLp4Sum_nonneg u)
  obtain ⟨D, hD, agrees⟩ := extendSchwartzLp (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) A hK testBound
  let z := (InnerProductSpace.toDual ℂ (FirstOrderLp 2)).symm D
  refine ⟨z, by simpa only [z, LinearIsometryEquiv.norm_map] using hD, ?_⟩
  intro w
  rw [← inner_conj_symm]
  change conj (inner ℂ ((InnerProductSpace.toDual ℂ (FirstOrderLp 2)).symm D) (w.toLp 2 volume)) = conj (A w)
  rw [InnerProductSpace.toDual_symm_apply, agrees]

/-- The first-order bound for the actual high adjoint on fixed-index Schwartz
fields. Its differentiated-low output represents the adjoint of the derivative commutator. -/
theorem exists_originalAngular_highAdjoint_firstOrder_and_coordinate_commutator
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)},
      IsOpen W → Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ 27, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      ∃ (T : SchwartzMap E ℂ → (FirstOrderLp 4 →L[ℂ] FirstOrderLp 2))
        (S : SchwartzMap E ℂ → SchwartzMap E ℂ → FirstOrderLp 2),
        (∀ u : SchwartzMap E ℂ, ∀ H : FirstOrderLp 4, ‖T u H‖ ≤ C * M * ‖H‖ * highDerivativeLp4Sum u) ∧
        (∀ H u : SchwartzMap E ℂ, ‖S H u‖ ≤ C * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u) ∧
        (∀ H u w : SchwartzMap E ℂ,
          inner ℂ (w.toLp 2 volume) (T u (H.toLp 4 volume)) =
            radianHighPair (originalRegularizedAngularSymbol η χ F) H u w ∧
          inner ℂ (w.toLp 2 volume) (S H u) =
            radianHighPair (highAdjointSymbol (originalRegularizedAngularSymbol η χ F)) (fun x => conj (H x)) u w ∧
          inner ℂ (w.toLp 2 volume) (S H u) = conj (inner ℂ (u.toLp 2 volume) (T w (H.toLp 4 volume)))) ∧
        ∀ (a : Fin 4) (H u w : SchwartzMap E ℂ),
          -inner ℂ ((coordinateDerivative a w).toLp 2 volume) (S H u) -
            inner ℂ (w.toLp 2 volume) (S H (coordinateDerivative a u)) =
              inner ℂ (w.toLp 2 volume) (S (coordinateDerivative a H) u) := by
  obtain ⟨C₁, hC₁, forward⟩ := exists_originalAngular_coordinateDerivative_commutator
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  obtain ⟨C₂, _, adjoint⟩ := exists_originalAngular_highAdjoint_representation
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  refine ⟨max C₁ C₂, hC₁.trans (le_max_left _ _), ?_⟩
  intro F W hW hQ hF M hM hjet
  obtain ⟨T, normT, pairT, derivative⟩ := forward hW hQ hF M hM hjet
  choose S normS pairS using adjoint hW hQ hF M hM hjet
  have dual (H u w : SchwartzMap E ℂ) :
      inner ℂ (w.toLp 2 volume) (S H u) = conj (inner ℂ (u.toLp 2 volume) (T w (H.toLp 4 volume))) := by
    rw [pairS, pairT]
  refine ⟨T, S, ?_, ?_, ?_, ?_⟩
  · intro u H
    exact (normT u H).trans <| mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM) (norm_nonneg _))
      (highDerivativeLp4Sum_nonneg u)
  · intro H u
    exact (normS H u).trans <| mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hM) (norm_nonneg _))
      (highDerivativeLp4Sum_nonneg u)
  · intro H u w
    exact ⟨pairT H u w, (pairS H u w).trans (radianHighPair_highAdjoint _ H w u).symm, dual H u w⟩
  · intro a H u w
    rw [dual H u (coordinateDerivative a w), dual H (coordinateDerivative a u) w, dual (coordinateDerivative a H) u w]
    have eq := congrArg (conj : ℂ → ℂ) (derivative a H w u)
    simp only [map_sub, map_neg] at eq
    simpa only [sub_eq_add_neg, add_comm] using eq

end Burnett.A07
