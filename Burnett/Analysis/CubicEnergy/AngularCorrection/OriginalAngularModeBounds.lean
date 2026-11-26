import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalUpperCutoffWeakRecovery

set_option autoImplicit false
set_option maxHeartbeats 12000000

noncomputable section

namespace Burnett.A08

open Burnett.A07 Burnett.A06 Burnett.A02.FrequencySplit Burnett.Fourier MeasureTheory Metric Set
open scoped BigOperators ComplexConjugate ContDiff ENNReal NNReal

open private exists_actualHarmonicLp4_multiplier from Burnett.Analysis.CubicEnergy.AngularCorrection.ActualAngularFirstOrderBound
open private extendSchwartzLp from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
open private radianHighInputLinear norm_le_of_triLpMass_424 from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularSecondExponent
open private norm_le_of_triLpMass_442 from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularRoughCommutator
open private norm_le_of_firstOrderMass from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalHighAdjointFirstOrder

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2
private abbrev LP4 := FirstOrderLp 4

/-- Estimates on one actual spherical mode before summing the angular series.
The forward and dual representatives and the two rough estimates concern
the same mode, including the low angular multiplier and the original cutoff. -/
structure OriginalAngularModeBounds
    (η χ : ℝ → ℝ) (F : Joint × RotationSpace → ℂ) (M C₀ C₁ : ℝ)
    (T S : HarmonicMode → Test → Test → LP2) : Prop where
  forwardPair (i : HarmonicMode) (H u w : Test) :
    inner ℂ (w.toLp 2 volume) (T i H u) = radianHighPair (angularModeSymbol η χ F i) H u w
  adjointPair (i : HarmonicMode) (H u w : Test) :
    inner ℂ (w.toLp 2 volume) (S i H u) =
      radianHighPair (highAdjointSymbol (angularModeSymbol η χ F i)) (fun x => conj (H x)) u w
  forwardNorm (i : HarmonicMode) (H u : Test) :
    ‖T i H u‖ ≤ C₀ * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u / ((i.1 : ℝ) + 1)^5
  adjointNorm (i : HarmonicMode) (H u : Test) :
    ‖S i H u‖ ≤ C₀ * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u / ((i.1 : ℝ) + 1)^5
  derivativePair (i : HarmonicMode) (a : Fin 4) (H u w : Test) :
    -radianHighPair (angularModeSymbol η χ F i) H u (coordinateDerivative a w) -
      radianHighPair (angularModeSymbol η χ F i) H (coordinateDerivative a u) w =
        radianHighPair (angularModeSymbol η χ F i) (coordinateDerivative a H) u w
  roughForward (i : HarmonicMode) (d : SchwartzMap E ℝ) (ℓ : ℝ≥0) (lip : LipschitzWith ℓ d) (H u w : Test) :
    ‖radianHighCommutatorPair (angularModeSymbol η χ F i) d H u w‖ ≤
      C₁ * M * (ℓ : ℝ) * ‖H.toLp 4 volume‖ * ‖u.toLp 4 volume‖ * ‖w.toLp 2 volume‖ / ((i.1 : ℝ) + 1)^5
  roughAdjoint (i : HarmonicMode) (d : SchwartzMap E ℝ) (ℓ : ℝ≥0) (lip : LipschitzWith ℓ d) (H u w : Test) :
    ‖radianHighCommutatorPair (angularModeSymbol η χ F i) d H u w‖ ≤
      C₁ * M * (ℓ : ℝ) * ‖H.toLp 4 volume‖ * ‖u.toLp 2 volume‖ * ‖w.toLp 4 volume‖ / ((i.1 : ℝ) + 1)^5

theorem exists_originalAngularMode_bounds
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (C₀ C₁ : ℝ), 27 ≤ K ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}, IsOpen W →
      Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      ∃ T S : HarmonicMode → Test → Test → LP2, OriginalAngularModeBounds η χ F M C₀ C₁ T S := by
  have hρ₁ : ρ < 1 := hsmall.trans (by norm_num)
  obtain ⟨CF, hCF, cartesian⟩ := exists_regularizedLowCartesian_L4_to_L2
    η χ hr hρ hρ₁ hR hη hzero hone hχ hcut
  obtain ⟨CS, hCS, adjoint⟩ := exists_regularizedLowCartesian_highPair_firstOrderBound
    η χ hr hρ hρ₁ hR hη hzero hone hχ hcut
  obtain ⟨K, CR, hCR, rough⟩ := exists_regularizedLowCartesian_highSlot_common_angularJetBound
    η χ hρ hsmall hr hR hη hzero hone hχ hcut
  obtain ⟨Cc, hCc, coefficient⟩ := exists_jointSphereHarmonicCoefficientComplex_on_open_neighborhood (E := Joint)
  obtain ⟨_, _, smoothCoefficient⟩ := exists_smoothComplexAngularCoefficient_jet15 (E := Joint)
  obtain ⟨Cm, hCm, harmonics⟩ := exists_actualHarmonicLp4_multiplier
  choose m Y hm normY hY using harmonics
  let C₀ := max CF CS.toReal * Cc * Cm
  let C₁ := CR * Cc * Cm
  have hC₀ : 0 ≤ C₀ := mul_nonneg (mul_nonneg (hCF.trans (le_max_left _ _)) hCc) hCm
  have hC₁ : 0 ≤ C₁ := mul_nonneg (mul_nonneg hCR hCc) hCm
  have h27 : 27 ≤ max K 15 + 12 := by have h := Nat.le_max_right K 15; omega
  refine ⟨max K 15 + 12, C₀, C₁, h27, hC₀, hC₁, ?_⟩
  intro F W hW hQW hF M hM hjet
  let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
  have compactQ : IsCompact Q := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have jet27 (n : ℕ) (hn : n ≤ 27) := hjet n (hn.trans h27)
  obtain ⟨V₀, hV₀, hQV₀, smooth⟩ := smoothCoefficient hW compactQ hQW hF M hM jet27
  obtain ⟨V₁, hV₁, hQV₁, jet⟩ := coefficient hW compactQ hQW (max K 15)
    (hF.of_le (WithTop.coe_le_coe.mpr le_top)) M hM (fun n hn => hjet n hn)
  let V := V₀ ∩ V₁
  have hV : IsOpen V := hV₀.inter hV₁
  have hQV : Q ⊆ V := fun p hp => ⟨hQV₀ hp, hQV₁ hp⟩
  let c (i : HarmonicMode) := jointSphereHarmonicCoefficientComplex F i
  have hc (i : HarmonicMode) : ContDiffOn ℝ ∞ (c i) V := (smooth i).1.mono inter_subset_left
  let J (i : HarmonicMode) := Cc * (((i.1 : ℝ) + 1)^12)⁻¹ * M
  have hJ (i : HarmonicMode) : 0 ≤ J i := by dsimp [J]; positivity
  have jets15 (i : HarmonicMode) (n : ℕ) (hn : n ≤ 15) :=
    (jet i).2 n (hn.trans (Nat.le_max_right K 15))
  let b (i : HarmonicMode) : OrderOneSymbol ℂ :=
    ⟨regularizedLowCartesianSymbol η χ (c i),
      regularizedLowCartesianSymbol_mem_orderOneSymbolSubmodule η χ _ hr hρ hR hη hzero hone
        hχ hcut hV hQV (hc i)⟩
  let mode (i : HarmonicMode) := angularModeSymbol η χ F i
  have measurableMode (i : HarmonicMode) : Measurable (mode i) := by
    have hAngular : Measurable (sphereHarmonicMultiplierSymbol i.1 i.2 : E → ℝ) :=
      measurable_of_continuousOn_compl_singleton 0 (sphereHarmonicRadialSymbol_contDiffOn _ _).continuousOn
    exact (Complex.continuous_ofReal.measurable.comp (hAngular.comp measurable_fst)).mul (b i).measurable_symbol
  let G (i : HarmonicMode) := (m i).bound * orderOneWeightedSeminorm ℂ 0 (b i)
  have hG (i : HarmonicMode) : 0 ≤ G i := mul_nonneg (m i).bound_nonneg (apply_nonneg _ _)
  have modeOrder (i : HarmonicMode) (p : Joint) : ‖mode i p‖ ≤ G i * (1 + ‖p.1‖ + ‖p.2‖) := by
    change ‖(sphereHarmonicMultiplierSymbol i.1 i.2 p.1 : ℂ) * (b i : Joint → ℂ) p‖ ≤ _
    rw [norm_mul, ← hm i p.1, mul_assoc]
    exact mul_le_mul ((m i).norm_le _) ((b i).norm_apply_le_weightedSeminorm_zero p)
      (norm_nonneg _) (m i).bound_nonneg
  have build (i : HarmonicMode) (u : Test) :=
    cartesian hV hQV (c i) (J i) (hJ i) (hc i) (jets15 i) u
  choose B normB pairB using build
  let T (i : HarmonicMode) (H u : Test) := B i u (Y i (H.toLp 4 volume))
  have pairT (i : HarmonicMode) (H u w : Test) :
      inner ℂ (w.toLp 2 volume) (T i H u) = radianHighPair (mode i) H u w :=
    physicalAngularMultiplier_pair_eq (b i) u H w i (m i) (hm i) (Y i)
      (hY i H (H.memLp 2 volume) (H.memLp 4 volume)) (B i u) (pairB i u)
  have normTop (i : HarmonicMode) (H : Test) :
      ‖Y i (H.toLp 4 volume)‖ ≤ Cm * ((i.1 : ℝ) + 1)^7 * ‖H.toLp 4 volume‖ :=
    ((Y i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (normY i) (norm_nonneg _))
  have scale (i : HarmonicMode) (C D N : ℝ) :
      (C * J i * D) * (Cm * ((i.1 : ℝ) + 1)^7 * N) =
        C * Cc * Cm * M * N * D / ((i.1 : ℝ) + 1)^5 := by
    have hi : 0 < (i.1 : ℝ) + 1 := by positivity
    dsimp [J]
    field_simp [hi.ne']
  have normT (i : HarmonicMode) (H u : Test) :
      ‖T i H u‖ ≤ C₀ * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u / ((i.1 : ℝ) + 1)^5 := by
    let D := highDerivativeLp4Sum u
    have hD : 0 ≤ D := highDerivativeLp4Sum_nonneg u
    calc
      _ ≤ (CF * J i * D) * ‖Y i (H.toLp 4 volume)‖ :=
        ((B i u).le_opNorm _).trans (mul_le_mul_of_nonneg_right (normB i u) (norm_nonneg _))
      _ ≤ (max CF CS.toReal * J i * D) * (Cm * ((i.1 : ℝ) + 1)^7 * ‖H.toLp 4 volume‖) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (hJ i)) hD)
          (normTop i H) (norm_nonneg _) (by positivity)
      _ = _ := scale i _ D _
  have buildS (i : HarmonicMode) (H u : Test) :
      ∃ z : LP2, ‖z‖ ≤ C₀ * M * ‖H.toLp 4 volume‖ * highDerivativeLp4Sum u / ((i.1 : ℝ) + 1)^5 ∧
        ∀ w : Test, inner ℂ (w.toLp 2 volume) z = conj (radianHighPair (mode i) H w u) := by
    let A := radianHighInputLinear (mode i) H u fun w =>
      integrable_radianHighPairWeight_of_orderOne (mode i) (measurableMode i) (G i) (hG i) (modeOrder i) H w u
    let D := highDerivativeLp4Sum u
    let U := C₀ * M * ‖H.toLp 4 volume‖ * D / ((i.1 : ℝ) + 1)^5
    have hD : 0 ≤ D := highDerivativeLp4Sum_nonneg u
    have hU : 0 ≤ U := by dsimp [U]; positivity
    have testBound (w : Test) : ‖A w‖ ≤ U * ‖w.toLp 2 volume‖ := by
      let C := CS.toReal * J i * D * ‖w.toLp 2 volume‖
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have onLp (f : LP4) : ‖inner ℂ (u.toLp 2 volume) (B i w f)‖ ≤ C * ‖f‖ := by
        refine (CMBilinearDual.schwartz_toLp_denseRange 4 (by norm_num)).induction_on f
          (isClosed_le (continuous_const.inner (B i w).continuous).norm (continuous_const.mul continuous_norm)) ?_
        intro f
        rw [pairB, ← Complex.norm_conj, ← radianHighPair_highAdjoint]
        exact norm_le_of_firstOrderMass f u w _ hCS.ne (hJ i)
          (adjoint hV hQV (c i) (J i) (hJ i) (hc i) (jets15 i) f u w).2
      change ‖radianHighPair (mode i) H w u‖ ≤ _
      rw [← pairT i H w u]
      calc
        _ ≤ C * ‖Y i (H.toLp 4 volume)‖ := onLp _
        _ ≤ C * (Cm * ((i.1 : ℝ) + 1)^7 * ‖H.toLp 4 volume‖) :=
          mul_le_mul_of_nonneg_left (normTop i H) hC
        _ = (CS.toReal * J i * D) *
            (Cm * ((i.1 : ℝ) + 1)^7 * ‖H.toLp 4 volume‖) * ‖w.toLp 2 volume‖ := by
          dsimp only [C]
          ring
        _ ≤ (max CF CS.toReal * J i * D) *
            (Cm * ((i.1 : ℝ) + 1)^7 * ‖H.toLp 4 volume‖) * ‖w.toLp 2 volume‖ := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (hJ i)) hD)
            (by positivity)) (norm_nonneg _)
        _ = _ := by simp only [scale, U, C₀]
    obtain ⟨Ddual, hDdual, agrees⟩ := extendSchwartzLp (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) A hU testBound
    let z := (InnerProductSpace.toDual ℂ LP2).symm Ddual
    refine ⟨z, by simpa only [z, LinearIsometryEquiv.norm_map] using hDdual, ?_⟩
    intro w
    rw [← inner_conj_symm]
    change conj (inner ℂ ((InnerProductSpace.toDual ℂ LP2).symm Ddual) (w.toLp 2 volume)) = conj (A w)
    rw [InnerProductSpace.toDual_symm_apply, agrees]
  choose S normS pairS using buildS
  have roughBound (hslot : Bool) (i : HarmonicMode) (d : SchwartzMap E ℝ) (ℓ : ℝ≥0)
      (lip : LipschitzWith ℓ d) (H u w : Test) :
      ‖radianHighCommutatorPair (mode i) d H u w‖ ≤
        C₁ * M * (ℓ : ℝ) * ‖H.toLp 4 volume‖ *
          (if hslot then ‖u.toLp 2 volume‖ * ‖w.toLp 4 volume‖ else ‖u.toLp 4 volume‖ * ‖w.toLp 2 volume‖) /
          ((i.1 : ℝ) + 1)^5 := by
    let du := realSchwartzMultiply d u
    let dw := realSchwartzMultiply d w
    let D := if hslot then ‖u.toLp 2 volume‖ * ‖w.toLp 4 volume‖ else ‖u.toLp 4 volume‖ * ‖w.toLp 2 volume‖
    let C := CR * J i * ((ℓ : ℝ) * D)
    have hD : 0 ≤ D := by cases hslot <;> dsimp [D] <;> positivity
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    let test (f : LP4) := inner ℂ (w.toLp 2 volume) (B i du f) - inner ℂ (dw.toLp 2 volume) (B i u f)
    have onLp (f : LP4) : ‖test f‖ ≤ C * ‖f‖ := by
      refine (CMBilinearDual.schwartz_toLp_denseRange 4 (by norm_num)).induction_on f
        (isClosed_le ((continuous_const.inner (B i du).continuous).sub
          (continuous_const.inner (B i u).continuous)).norm (continuous_const.mul continuous_norm)) ?_
      intro f
      change ‖inner ℂ (w.toLp 2 volume) (B i du (f.toLp 4 volume)) -
        inner ℂ (dw.toLp 2 volume) (B i u (f.toLp 4 volume))‖ ≤ _
      rw [pairB, pairB]
      have multiply (v : Test) : (fun x => v x * (d x : ℂ)) = (realSchwartzMultiply d v : E → ℂ) := by
        funext x
        rw [realSchwartzMultiply_apply, mul_comm]
      have estimate := rough hslot hV hQV (c i) (J i) (hJ i) (hc i)
        (fun n hn => (jet i).2 n (hn.trans (Nat.le_max_left K 15))) d ℓ lip f u w
      cases hslot
      · have h := norm_le_of_triLpMass_442 f u w _ (mul_nonneg hCR (hJ i)) ℓ estimate
        simpa only [C, D, du, dw, radianHighCommutatorPair, multiply, Bool.false_eq_true, if_false,
          mul_assoc, mul_comm, mul_left_comm] using h
      · have h := norm_le_of_triLpMass_424 f u w _ (mul_nonneg hCR (hJ i)) ℓ estimate
        simpa only [C, D, du, dw, radianHighCommutatorPair, multiply, if_true,
          mul_assoc, mul_comm, mul_left_comm] using h
    have identify : test (Y i (H.toLp 4 volume)) = radianHighCommutatorPair (mode i) d H u w := by
      change inner ℂ (w.toLp 2 volume) (T i H du) - inner ℂ (dw.toLp 2 volume) (T i H u) = _
      rw [pairT i H du w, pairT i H u dw]
      rfl
    rw [← identify]
    calc
      _ ≤ C * ‖Y i (H.toLp 4 volume)‖ := onLp _
      _ ≤ C * (Cm * ((i.1 : ℝ) + 1)^7 * ‖H.toLp 4 volume‖) := mul_le_mul_of_nonneg_left (normTop i H) hC
      _ = _ := by rw [show C = CR * J i * ((ℓ : ℝ) * D) from rfl, scale]; dsimp only [C₁, D]; ring
  refine ⟨T, S, pairT, ?_, normT, normS, ?_, ?_, ?_⟩
  · intro i H u w
    rw [pairS, radianHighPair_highAdjoint]
  · intro i a H u w
    exact radianHighPair_coordinateDerivative_commutator a (mode i) (measurableMode i) (G i) (hG i)
      (modeOrder i) H u w
  · intro i d ℓ lip H u w
    simpa only [Bool.false_eq_true, if_false, mul_assoc] using roughBound false i d ℓ lip H u w
  · intro i d ℓ lip H u w
    simpa only [if_true, mul_assoc] using roughBound true i d ℓ lip H u w

end Burnett.A08
