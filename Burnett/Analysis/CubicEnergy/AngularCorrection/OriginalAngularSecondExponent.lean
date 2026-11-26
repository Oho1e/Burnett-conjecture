import Burnett.Analysis.CubicEnergy.AngularCorrection.SchwartzHighSlotCommutator
import Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderOriginalAngularPairing
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CartesianHighSlotAngularJets

set_option autoImplicit false
set_option maxHeartbeats 10000000

noncomputable section

namespace Burnett.A07

open Burnett.A06 Burnett.A02.FrequencySplit Burnett.Fourier MeasureTheory Metric Set Filter
open scoped BigOperators ComplexConjugate ContDiff ENNReal NNReal

open private exists_actualHarmonicLp4_multiplier from Burnett.Analysis.CubicEnergy.AngularCorrection.ActualAngularFirstOrderBound
open private radianSchwartzEval radianSchwartzEval_eq from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private def radianHighInputLinear (b : Joint → ℂ) (f w : SchwartzMap E ℂ)
    (integrable : ∀ u : SchwartzMap E ℂ, Integrable (radianHighPairWeight b f u w)) :
    SchwartzMap E ℂ →ₗ[ℂ] ℂ where
  toFun u := radianHighPair b f u w
  map_add' u v := by
    unfold radianHighPair
    rw [← smul_add, ← integral_add (integrable u) (integrable v)]
    congr 1
    apply integral_congr_ae
    filter_upwards with p
    simp only [radianHighPairWeight, ← radianSchwartzEval_eq, map_add]
    ring
  map_smul' c u := by
    unfold radianHighPair
    have eq : radianHighPairWeight b f (c • u : SchwartzMap E ℂ) w =
        fun p => c * radianHighPairWeight b f u w p := by
      funext p
      simp only [radianHighPairWeight, ← radianSchwartzEval_eq, map_smul, smul_eq_mul]
      ring
    rw [eq, integral_const_mul]
    simp only [Complex.real_smul, RingHom.id_apply, smul_eq_mul]
    ring

private def realSchwartzMultiplyLinear (d : SchwartzMap E ℝ) : SchwartzMap E ℂ →ₗ[ℂ] SchwartzMap E ℂ where
  toFun := realSchwartzMultiply d
  map_add' u v := by
    ext x
    simp only [SchwartzMap.add_apply, realSchwartzMultiply_apply, mul_add]
  map_smul' c u := by
    ext x
    simp only [SchwartzMap.smul_apply, realSchwartzMultiply_apply, smul_eq_mul, RingHom.id_apply]
    ring

private theorem norm_le_of_triLpMass_424 (f u w : SchwartzMap E ℂ) (z : ℂ)
    {A : ℝ} (hA : 0 ≤ A) (L : ℝ≥0)
    (h : ‖z‖ₑ ≤ (L : ℝ≥0∞) * ENNReal.ofReal A * triLpMass f u w 4 2 4) :
    ‖z‖ ≤ ((L : ℝ) * A * ‖u.toLp 2 volume‖ * ‖w.toLp 4 volume‖) * ‖f.toLp 4 volume‖ := by
  simp only [triLpMass, ENNReal.ofReal_ofNat, ← mul_assoc] at h
  have finite : (L : ℝ≥0∞) * ENNReal.ofReal A * eLpNorm (f : E → ℂ) 4 volume *
      eLpNorm (u : E → ℂ) 2 volume * eLpNorm (w : E → ℂ) 4 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) (f.memLp 4 volume).2.ne)
      (u.memLp 2 volume).2.ne) (w.memLp 4 volume).2.ne
  have result := ENNReal.toReal_mono finite h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ← SchwartzMap.norm_toLp] at result
  simpa only [mul_assoc, mul_comm, mul_left_comm] using result

/-- The original high commutator pairing is linear in its high input and
bounded using the (4,2,4) placement on the same unexpanded symbol. -/
theorem exists_originalAngular_roughSecondExponent
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (C : ℝ), 27 ≤ K ∧ 0 ≤ C ∧
      ∀ {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)},
      IsOpen W → Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ W → ContDiffOn ℝ ∞ F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3, ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      ∀ (d : SchwartzMap E ℝ) (L : ℝ≥0), LipschitzWith L d → ∀ H w : SchwartzMap E ℂ,
        ∃ A : SchwartzMap E ℂ →ₗ[ℂ] ℂ,
          (∀ u, A u = radianHighCommutatorPair (originalRegularizedAngularSymbol η χ F) d H u w) ∧
          ∀ u, ‖A u‖ ≤ (C * M * (L : ℝ) * ‖H.toLp 4 volume‖ * ‖w.toLp 4 volume‖) * ‖u.toLp 2 volume‖ := by
  have hρ₁ : ρ < 1 := hsmall.trans (by norm_num)
  obtain ⟨K, Cb, hCb, commBound⟩ := exists_regularizedLowCartesian_highSlot_common_angularJetBound
    η χ hρ hsmall hr hR hη hzero hone hχ hcut
  obtain ⟨_, _, cartesian⟩ := exists_regularizedLowCartesian_L4_to_L2
    η χ hr hρ hρ₁ hR hη hzero hone hχ hcut
  obtain ⟨Cc, hCc, coefficient⟩ := exists_jointSphereHarmonicCoefficientComplex_on_open_neighborhood (E := Joint)
  obtain ⟨_, _, smoothCoefficient⟩ := exists_smoothComplexAngularCoefficient_jet15 (E := Joint)
  obtain ⟨Cm, hCm, harmonics⟩ := exists_actualHarmonicLp4_multiplier
  choose m Y hm hYnorm hY using harmonics
  let C := Cb * Cc * Cm
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hCb hCc) hCm
  have h27 : 27 ≤ max K 15 + 12 := by have h := Nat.le_max_right K 15; omega
  refine ⟨max K 15 + 12, 2 * C, h27, mul_nonneg (by norm_num) hC, ?_⟩
  intro F W hW hContains hF M hM hjet d L hL H w
  let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have jet27 (n : ℕ) (hn : n ≤ 27) (p : Joint) (hp : p ∈ Q) (x : RoundSphere3) :
      ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M := hjet n (hn.trans h27) p hp x
  obtain ⟨V₀, hV₀, hQV₀, smooth⟩ := smoothCoefficient hW hQ hContains hF M hM jet27
  obtain ⟨V₁, hV₁, hQV₁, jet⟩ := coefficient hW hQ hContains (max K 15)
    (hF.of_le (WithTop.coe_le_coe.mpr le_top)) M hM
    (fun n hn p hp x => hjet n hn p hp x)
  let V := V₀ ∩ V₁
  have hV : IsOpen V := hV₀.inter hV₁
  have hQV : Q ⊆ V := fun _ hp => ⟨hQV₀ hp, hQV₁ hp⟩
  let c (i : HarmonicMode) := jointSphereHarmonicCoefficientComplex F i
  have hc (i : HarmonicMode) : ContDiffOn ℝ ∞ (c i) V := (smooth i).1.mono inter_subset_left
  let J (i : HarmonicMode) := Cc * (((i.1 : ℝ) + 1)^12)⁻¹ * M
  have hJ (i : HarmonicMode) : 0 ≤ J i := by dsimp [J]; positivity
  let b (i : HarmonicMode) : OrderOneSymbol ℂ :=
    ⟨regularizedLowCartesianSymbol η χ (c i),
      regularizedLowCartesianSymbol_mem_orderOneSymbolSubmodule η χ _ hr hρ hR hη hzero hone
        hχ hcut hV hQV (hc i)⟩
  let mode (i : HarmonicMode) := angularModeSymbol η χ F i
  have integrable (i : HarmonicMode) (u v : SchwartzMap E ℂ) :
      Integrable (radianHighPairWeight (mode i) H u v) := by
    have hAngular : Measurable (sphereHarmonicMultiplierSymbol i.1 i.2 : E → ℝ) :=
      measurable_of_continuousOn_compl_singleton 0 (sphereHarmonicRadialSymbol_contDiffOn _ _).continuousOn
    have hMode : Measurable (mode i) :=
      (Complex.continuous_ofReal.measurable.comp (hAngular.comp measurable_fst)).mul (b i).measurable_symbol
    apply integrable_radianHighPairWeight_of_orderOne (mode i) hMode
      ((m i).bound * orderOneWeightedSeminorm ℂ 0 (b i)) (mul_nonneg (m i).bound_nonneg (apply_nonneg _ _))
    intro p
    change ‖(sphereHarmonicMultiplierSymbol i.1 i.2 p.1 : ℂ) * (b i : Joint → ℂ) p‖ ≤ _
    rw [norm_mul, ← hm i p.1, mul_assoc]
    exact mul_le_mul ((m i).norm_le _) ((b i).norm_apply_le_weightedSeminorm_zero p)
      (norm_nonneg _) (m i).bound_nonneg
  let dw := realSchwartzMultiply d w
  let Aᵢ (i : HarmonicMode) :=
    (radianHighInputLinear (mode i) H w (fun u => integrable i u w)).comp (realSchwartzMultiplyLinear d) -
      radianHighInputLinear (mode i) H dw (fun u => integrable i u dw)
  have hAᵢ (i : HarmonicMode) (u : SchwartzMap E ℂ) :
      Aᵢ i u = radianHighCommutatorPair (mode i) d H u w := rfl
  have pairSum := originalRegularizedAngularPair_hasSum_of_smoothProfile
    η χ hr hρ hR hη hzero hone hχ hcut hW hContains hF hM jet27
  let pair (u : SchwartzMap E ℂ) := radianHighCommutatorPair (originalRegularizedAngularSymbol η χ F) d H u w
  have series (u : SchwartzMap E ℂ) : HasSum (fun i => Aᵢ i u) (pair u) :=
    (pairSum H (realSchwartzMultiply d u) w).sub (pairSum H u dw)
  let A : SchwartzMap E ℂ →ₗ[ℂ] ℂ :=
    { toFun := pair
      map_add' := fun u v =>
        (series (u + v)).unique (by simpa only [map_add] using (series u).add (series v))
      map_smul' := fun a u =>
        (series (a • u)).unique (by simpa only [map_smul, RingHom.id_apply] using (series u).const_smul a) }
  refine ⟨A, fun _ => rfl, ?_⟩
  intro u
  let du := realSchwartzMultiply d u
  let H₄ := H.toLp 4 volume
  let U := C * M * (L : ℝ) * ‖H₄‖ * ‖w.toLp 4 volume‖ * ‖u.toLp 2 volume‖
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have majorant (i : HarmonicMode) : ‖Aᵢ i u‖ ≤ U / ((i.1 : ℝ) + 1)^5 := by
    have jets15 := fun n (hn : n ≤ 15) => (jet i).2 n (hn.trans (Nat.le_max_right K 15))
    obtain ⟨B, _, hB⟩ := cartesian hV hQV (c i) (J i) (hJ i) (hc i) jets15 u
    obtain ⟨Bd, _, hBd⟩ := cartesian hV hQV (c i) (J i) (hJ i) (hc i) jets15 du
    let test (f : FirstOrderLp 4) :=
      inner ℂ (w.toLp 2 volume) (Bd f) - inner ℂ (dw.toLp 2 volume) (B f)
    let D := (L : ℝ) * (Cb * J i) * ‖u.toLp 2 volume‖ * ‖w.toLp 4 volume‖
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hTest (f : FirstOrderLp 4) : ‖test f‖ ≤ D * ‖f‖ := by
      refine (CMBilinearDual.schwartz_toLp_denseRange 4 (by norm_num)).induction_on f ?_ ?_
      · exact isClosed_le
          ((continuous_const.inner Bd.continuous).sub (continuous_const.inner B.continuous)).norm
          (continuous_const.mul continuous_norm)
      · intro f
        change ‖inner ℂ (w.toLp 2 volume) (Bd (f.toLp 4 volume)) -
          inner ℂ (dw.toLp 2 volume) (B (f.toLp 4 volume))‖ ≤ _
        rw [hBd, hB]
        apply norm_le_of_triLpMass_424 f u w _ (mul_nonneg hCb (hJ i)) L
        exact commBound true hV hQV (c i) (J i) (hJ i) (hc i)
          (fun n hn => (jet i).2 n (hn.trans (Nat.le_max_left K 15))) d L hL f u w
    have identify : test (Y i H₄) = Aᵢ i u := by
      have compatibility := hY i H (H.memLp 2 volume) (H.memLp 4 volume)
      have first := physicalAngularMultiplier_pair_eq (b i) du H w i (m i) (hm i) (Y i) compatibility Bd hBd
      have second := physicalAngularMultiplier_pair_eq (b i) u H dw i (m i) (hm i) (Y i) compatibility B hB
      change inner ℂ (w.toLp 2 volume) (Bd (Y i H₄)) -
        inner ℂ (dw.toLp 2 volume) (B (Y i H₄)) = Aᵢ i u
      rw [first, second, hAᵢ]
      rfl
    have hi : 0 < (i.1 : ℝ) + 1 := by positivity
    calc
      _ ≤ D * ‖Y i H₄‖ := identify ▸ hTest (Y i H₄)
      _ ≤ D * (Cm * ((i.1 : ℝ) + 1)^7 * ‖H₄‖) :=
        mul_le_mul_of_nonneg_left
          (((Y i).le_opNorm H₄).trans (mul_le_mul_of_nonneg_right (hYnorm i) (norm_nonneg _))) hD
      _ = _ := by
        dsimp [D, U, C, J]
        field_simp [hi.ne']
  change ‖pair u‖ ≤ _
  rw [← (series u).tsum_eq]
  exact (harmonic_series_estimate _ hU majorant).fullBound.trans_eq (by dsimp [U, C]; ring)

end Burnett.A07
