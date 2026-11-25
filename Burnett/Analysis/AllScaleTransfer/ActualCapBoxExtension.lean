import Burnett.Analysis.AllScaleTransfer.FixedChartGapExtension
import Burnett.Analysis.AllScaleTransfer.ActualCapRadialSeminorm
import Burnett.Analysis.AllScaleTransfer.LowRatioBounds

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff

abbrev AngleProjection := Frequency →L[ℝ] EuclideanSpace ℝ (Fin 3)

/-- Signed-chart coordinates are taken on the genuine unit directions of
both normalized frequencies. Each projection is fixed on its chart. -/
def normalizedPairAngles (u v : AngleProjection) (pq : FrequencyPair) : LowRatio.Angles :=
  (u (‖pq.1‖⁻¹ • pq.1), v (‖pq.2‖⁻¹ • pq.2))

theorem normalizedPairAngles_contDiffOn (u v : AngleProjection) {V : Set FrequencyPair}
    (hV : ∀ pq ∈ V, pq.1 ≠ 0 ∧ pq.2 ≠ 0) :
    ContDiffOn ℝ ∞ (normalizedPairAngles u v) V := by
  have sp : ContDiffOn ℝ ∞ (fun pq : FrequencyPair => ‖pq.1‖) V :=
    contDiff_fst.contDiffOn.norm ℝ (fun pq hpq => (hV pq hpq).1)
  have sq : ContDiffOn ℝ ∞ (fun pq : FrequencyPair => ‖pq.2‖) V :=
    contDiff_snd.contDiffOn.norm ℝ (fun pq hpq => (hV pq hpq).2)
  exact (u.contDiff.comp_contDiffOn
    ((sp.inv (fun pq hpq => norm_ne_zero_iff.mpr (hV pq hpq).1)).smul contDiff_fst.contDiffOn)).prodMk
    (v.contDiff.comp_contDiffOn
      ((sq.inv (fun pq hpq => norm_ne_zero_iff.mpr (hV pq hpq).2)).smul contDiff_snd.contDiffOn))

/-- Fixed enlarged cone and normalized closed radial annulus. An open chart
neighborhood contained here supplies the jets used by the fixed cutoff. -/
def fixedConeAnnulus (lo hi axial : ℝ) : Set Frequency :=
  radialJetAnnulus lo hi ∩ {p | axial * ‖p‖ ≤ |(frequencyCoordinates p).1|}

/-- Fixed margins between the original and enlarged annuli give an open
neighborhood of the compact block within the same angular chart. -/
theorem exists_fixed_cone_chart_neighborhood
    {lo hi axial lo₀ hi₀ axial₀ : ℝ}
    (hlo : 0 < lo) (hl : lo < lo₀) (hu : hi₀ < hi) (hc : axial < axial₀)
    {K : Set FrequencyPair}
    (hK : K ⊆ fixedConeAnnulus lo₀ hi₀ axial₀ ×ˢ fixedConeAnnulus lo₀ hi₀ axial₀)
    {U : Set LowRatio.Angles} (hU : IsOpen U) (u v : AngleProjection)
    (hAngular : MapsTo (normalizedPairAngles u v) K U) :
    ∃ V : Set FrequencyPair, IsOpen V ∧ K ⊆ V ∧
      V ⊆ fixedConeAnnulus lo hi axial ×ˢ fixedConeAnnulus lo hi axial ∧
      MapsTo (normalizedPairAngles u v) V U := by
  let W : Set Frequency := {p | (lo < ‖p‖ ∧ ‖p‖ < hi) ∧
    axial * ‖p‖ < |(frequencyCoordinates p).1|}
  have hW : IsOpen W :=
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).inter
      (isOpen_lt (continuous_const.mul continuous_norm) frequencyCoordinates.continuous.fst.abs)
  have bigger (p : Frequency) (hp : p ∈ fixedConeAnnulus lo₀ hi₀ axial₀) : p ∈ W := by
    have hPos : 0 < ‖p‖ := (hlo.trans hl).trans_le hp.1.1
    exact ⟨⟨hl.trans_le hp.1.1, hp.1.2.trans_lt hu⟩,
      (mul_lt_mul_of_pos_right hc hPos).trans_le hp.2⟩
  have covers : K ⊆ W ×ˢ W := fun pq hpq => ⟨bigger pq.1 (hK hpq).1, bigger pq.2 (hK hpq).2⟩
  have smaller (p : Frequency) (hp : p ∈ W) : p ∈ fixedConeAnnulus lo hi axial :=
    ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2.le⟩
  have smooth := normalizedPairAngles_contDiffOn u v (V := W ×ˢ W)
    (fun pq hpq => ⟨norm_pos_iff.mp (hlo.trans hpq.1.1.1), norm_pos_iff.mp (hlo.trans hpq.2.1.1)⟩)
  exact ⟨(W ×ˢ W) ∩ (normalizedPairAngles u v) ⁻¹' U,
    smooth.continuousOn.isOpen_inter_preimage (hW.prod hW) hU,
    fun _ hpq => ⟨covers hpq, hAngular hpq⟩,
    fun pq hpq => ⟨smaller pq.1 hpq.1.1, smaller pq.2 hpq.1.2⟩,
    fun _ hpq => hpq.2⟩

/-- Assemble the annular extension from the original finite-order remainder,
the actual cap frequency map and a fixed compact chart block. The same box
extension supplies the actual Fourier coefficients and physical-frequency
reconstruction. -/
theorem exists_actual_cap_box_series_from_remainder
    (B tube outer enlarged axial lo hi : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    (hAxial : 0 < axial) (hlo : 0 < lo)
    {K V : Set FrequencyPair} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (hCone : V ⊆ fixedConeAnnulus lo hi axial ×ˢ fixedConeAnnulus lo hi axial)
    {U : Set LowRatio.Angles} (hU : IsOpen U) (u v : AngleProjection)
    (hAngular : MapsTo (normalizedPairAngles u v) V U)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (χ₀ : ℝ → ℝ) (sχ₀ : ContDiff ℝ ∞ χ₀) (oneχ₀ : χ₀ 0 = 1) :
    ∃ (S P Cext C : ℝ) (χ : BoxSpace → ℝ) (s₀ : ℕ),
      0 < S ∧ S < P ∧ 0 ≤ Cext ∧ 0 ≤ C ∧ ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ ball (0 : BoxSpace) P ∧
      (∀ z ∈ closedBall (0 : BoxSpace) S, χ z = 1) ∧
      ∀ (m : Form) (w : Vec) (F : NullCapChart m w),
        ‖w‖ = 1 → ‖F.toFrequency.toContinuousLinearMap‖ ≤ B →
        ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → 4 * B * (5 * δ) ≤ 1 →
        ∀ (M : LowRatio.Point → ℂ) (A₁₀₀ : ℝ), 0 ≤ A₁₀₀ →
          ContDiffOn ℝ 100 M (LowRatio.Window U a b) →
          (∀ n ≤ 100, ∀ z ∈ LowRatio.Window U a b, ‖iteratedFDeriv ℝ n M z‖ ≤ A₁₀₀) →
          let A := capFrequencyEquiv F hδ.ne'
          let angular := normalizedPairAngles u v ∘ boxToPair
          ∃ g : ℕ → BoxSpace → ℂ,
            (∀ s, ContDiff ℝ 99 (g s)) ∧
            (∀ s n, n ≤ 40 → ∀ z, ‖iteratedFDeriv ℝ n (g s) z‖ ≤
              (Cext * A₁₀₀) * radialGapDecay s) ∧
            (∀ s, s₀ ≤ s → ∀ ζ υ : Frequency, (ζ, υ) ∈ K →
              g s (joinedInputs ζ υ) = normalizedGapRemainder A angular M χ₀ s (joinedInputs ζ υ)) ∧
            ∀ s,
              let c (ab : FourierModePair) :=
                boxCubeFourierCoefficient P (modeIndex ab) (fun z => χ z • g s z)
              (∀ ab, ‖c ab‖ ≤ (C * A₁₀₀) * radialGapDecay s * modePairDecay ab) ∧
              (s₀ ≤ s → ∀ (ζ υ : Frequency), (ζ, υ) ∈ K → ∀ j : ℤ,
                let z := joinedInputs ζ υ
                let ρ := ‖A (((2 : ℝ)^(j - (s : ℤ))) • ζ)‖ / ‖A (((2 : ℝ)^j) • υ)‖
                Summable (fun ab => ‖c ab * separatedBoxMode P ab z‖) ∧
                HasSum (fun ab => c ab * separatedBoxMode P ab z)
                  (ρ • LowRatio.remainder M χ₀ (angular z, ρ))) := by
  have nonzero (pq : FrequencyPair) (hpq : pq ∈ V) : pq.1 ≠ 0 ∧ pq.2 ≠ 0 :=
    ⟨norm_pos_iff.mp (hlo.trans_le (hCone hpq).1.1.1),
      norm_pos_iff.mp (hlo.trans_le (hCone hpq).2.1.1)⟩
  obtain ⟨J, hJ, capBudget⟩ := exists_uniform_capFrequency_radial_seminorms
    B tube outer enlarged axial lo hi hB hTube hOut hOE hAxial hlo 40
  let ang := normalizedPairAngles u v
  obtain ⟨β, Cg, s₀, _, _, _, _, hCg, mkGap⟩ := exists_fixed_chart_gap_extension
    hK hV hKV hU ang (normalizedPairAngles_contDiffOn u v nonzero) hAngular J hJ.le ha hb
  obtain ⟨Cr, hCr, mkRemainder⟩ := LowRatio.exists_remainder_budget χ₀ sχ₀ oneχ₀ ha hb
  obtain ⟨R, hR⟩ := hK.bddAbove_image (boxToPair.symm.continuous.norm.continuousOn)
  let S := max R 1
  let P := S + 1
  have hS : 0 < S := zero_lt_one.trans_le (le_max_right _ _)
  have hSP : S < P := by dsimp [P]; linarith
  have hBall (ζ υ : Frequency) (hz : (ζ, υ) ∈ K) : joinedInputs ζ υ ∈ closedBall (0 : BoxSpace) S := by
    have hEq : boxToPair.symm (ζ, υ) = joinedInputs ζ υ := by
      rw [← boxToPair_joined, ContinuousLinearEquiv.symm_apply_apply]
    rw [← hEq, mem_closedBall_zero_iff]
    exact (hR (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  obtain ⟨χ, Cbox, hχ, tχ, oneχ, hCbox, hBox⟩ := exists_actual_gap_box_series S P hS hSP
  let D := max 1 ‖boxToPair.toContinuousLinearMap‖
  have hD : 1 ≤ D := le_max_left _ _
  let Cext := Cg * Cr * D^40
  have hCext : 0 ≤ Cext := by dsimp [Cext]; positivity
  let C := Cbox * Cext
  have hC : 0 ≤ C := mul_nonneg hCbox hCext
  refine ⟨S, P, Cext, C, χ, s₀, hS, hSP, hCext, hC, hχ, tχ, oneχ, ?_⟩
  intro m w F hw hF hiF δ hδ hδone small M A₁₀₀ hA₁₀₀ sM bM A angular
  let r := physicalRadialRatio A.toContinuousLinearMap
  have rn (pq : FrequencyPair) (_ : pq ∈ V) : 0 ≤ r pq := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have sr : ContDiffOn ℝ ∞ r V := by
    intro pq hpq
    have nonzeroA (q : Frequency) (hq : q ≠ 0) : A.toContinuousLinearMap q ≠ 0 :=
      fun h => hq (A.injective (h.trans A.map_zero.symm))
    exact (physicalRadialRatio_contDiffAt _ (nonzeroA pq.1 (nonzero pq hpq).1)
      (nonzeroA pq.2 (nonzero pq hpq).2)).contDiffWithinAt
  obtain ⟨_, bRatio⟩ := capBudget m w F hw hF hiF δ hδ hδone small
  have br (n : ℕ) (hn : n ≤ 40) (pq : FrequencyPair) (hpq : pq ∈ V) :
      ‖iteratedFDeriv ℝ n r pq‖ ≤ J := by
    have hp := (hCone hpq).1
    have hq := (hCone hpq).2
    exact (bRatio n hn pq.1 ⟨hp.1, Or.inl hp.2⟩ pq.2 ⟨hq.1, Or.inl hq.2⟩).1
  obtain ⟨sR, bR⟩ := mkRemainder hU M A₁₀₀ hA₁₀₀ sM bM
  obtain ⟨gPair, sg, bg, eg⟩ := mkGap r (LowRatio.remainder M χ₀) (Cr * A₁₀₀)
    (mul_nonneg hCr hA₁₀₀) sr rn br sR
    (fun n hn z hz => bR n (hn.trans (by decide : 40 ≤ 99)) z hz)
  let g (s : ℕ) := gPair s ∘ boxToPair
  have sG (s : ℕ) : ContDiff ℝ 99 (g s) := (sg s).1.comp boxToPair.contDiff
  have bG (s n : ℕ) (hn : n ≤ 40) (z : BoxSpace) :
      ‖iteratedFDeriv ℝ n (g s) z‖ ≤ (Cext * A₁₀₀) * radialGapDecay s := by
    have hn' : (n : WithTop ℕ∞) ≤ 99 := by exact_mod_cast (hn.trans (by decide : 40 ≤ 99))
    have hnonneg : 0 ≤ radialGapDecay s := by unfold radialGapDecay; positivity
    change ‖iteratedFDeriv ℝ n (gPair s ∘ boxToPair.toContinuousLinearMap) z‖ ≤ _
    rw [boxToPair.toContinuousLinearMap.iteratedFDeriv_comp_right (sg s).1 z hn']
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ ≤ ((Cg * (Cr * A₁₀₀)) * radialGapDecay s) * ‖boxToPair.toContinuousLinearMap‖^n :=
        mul_le_mul_of_nonneg_right (bg s n hn (boxToPair z)) (pow_nonneg (norm_nonneg _) _)
      _ ≤ ((Cg * (Cr * A₁₀₀)) * radialGapDecay s) * D^40 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) n).trans
          (pow_le_pow_right₀ hD hn)
      _ = _ := by dsimp [Cext]; ring
  have eG (s : ℕ) (hs : s₀ ≤ s) (ζ υ : Frequency) (hpq : (ζ, υ) ∈ K) :
      g s (joinedInputs ζ υ) = normalizedGapRemainder A angular M χ₀ s (joinedInputs ζ υ) := by
    change gPair s (boxToPair (joinedInputs ζ υ)) = _
    rw [boxToPair_joined, eg s hs (ζ, υ) hpq]
    simp only [normalizedGapRemainder, firstInput_joined, secondInput_joined, gapRatio, r,
      physicalRadialRatio, angular, Function.comp_apply, boxToPair_joined, ang]
    rfl
  refine ⟨g, sG, bG, eG, ?_⟩
  intro s c
  obtain ⟨bound, expand⟩ := hBox A angular M χ₀ g (Cext * A₁₀₀) (mul_nonneg hCext hA₁₀₀)
    (fun n => (sG n).contDiffOn) (fun s n hn z _ => bG s n hn z) s
  refine ⟨fun ab => ?_, fun hs ζ υ hpq j => ?_⟩
  · simpa only [C, mul_assoc] using bound ab
  · exact expand ζ υ (nonzero (ζ, υ) (hKV hpq)).2 (hBall ζ υ hpq) (eG s hs ζ υ hpq) j

end Burnett.A05.BoxFourier
