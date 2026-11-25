import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CartesianNarrowPartition
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CartesianSchwartzSymbolLinearity
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.NarrowCartesianRadianConsumer

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Filter Finset MeasureTheory Metric Set
open scoped Topology ContDiff ENNReal NNReal BigOperators

def cartesianNarrowOrbitSymbol (w : SchwartzMap E ℂ) (s : ℝ) (i : ℕ)
    (η χ : ℝ → ℝ) (b : Joint → ℂ) (p : Joint) : ℂ :=
  ∑' k : ℕ, cartesianNarrowWindow w s i k p.2*regularizedLowCartesianSymbol η χ b p

def cartesianHighComplement (w : SchwartzMap E ℂ) (s : ℝ) (η χ : ℝ → ℝ)
    (b : Joint → ℂ) (p : Joint) : ℂ :=
  (1-w ((2*s/tau) • p.2))*regularizedLowCartesianSymbol η χ b p

/-- The exact high-frequency Cartesian symbol is the finite sum of the
eight actual narrow radian orbits. -/
theorem cartesianHighComplement_eq_narrowOrbit_sum (w : SchwartzMap E ℂ)
    (h₁ : ∀ q : E, ‖q‖≤1 → w q=1) (h₀ : ∀ q : E, (17/16 : ℝ)≤‖q‖ → w q=0)
    (s : ℝ) (η χ : ℝ → ℝ) (b : Joint → ℂ) (p : Joint) :
    (∑ i ∈ range 8, cartesianNarrowOrbitSymbol w s i η χ b p) =
      cartesianHighComplement w s η χ b p := by
  unfold cartesianNarrowOrbitSymbol cartesianHighComplement
  simp_rw [tsum_mul_right,← sum_mul,cartesianNarrowWindow_tsum_sum w h₁ h₀ s p.2]

private theorem cartesianNarrowOrbit_plateau {s : ℝ} (hs : 0<s)
    (η : ℝ → ℝ) (hη : ∀ r≥tau/(2*s), η r=1) {i : ℕ} (hi : i<8) :
    ∀ r≥tau/cartesianNarrowScale s i, η r=1 := by
  have hp : 0<cartesianNarrowScale s i := cartesianNarrowScale_pos hs i
  have hτ : 0<tau := mul_pos (by norm_num) Real.pi_pos
  have h := div_le_div_of_nonneg_left hτ.le hp (cartesianNarrowScale_le hs.le hi)
  exact fun r hr => hη r (h.trans hr)

private theorem cartesianNarrowOrbit_eq_reference (w : SchwartzMap E ℂ)
    (h₁ : ∀ q : E, ‖q‖≤1 → w q=1) (h₀ : ∀ q : E, (17/16 : ℝ)≤‖q‖ → w q=0)
    {s : ℝ} (hs : 0<s) (η χ : ℝ → ℝ) (b : Joint → ℂ) {i : ℕ}
    (hη : ∀ r≥tau/cartesianNarrowScale s i, η r=1) :
    cartesianNarrowOrbitSymbol w s i η χ b =
      narrowReferenceOrbitSymbol (lowCartesianHighAnnularReference (cartesianNarrowProfile w i) χ b)
        (cartesianNarrowScale s i) := by
  have hτ : 0<tau := mul_pos (by norm_num) Real.pi_pos
  funext p
  unfold cartesianNarrowOrbitSymbol narrowReferenceOrbitSymbol cartesianNarrowWindow
  apply tsum_congr
  intro k
  let S := cartesianNarrowScale s i
  let r := dyadicCoefficientScale S k
  have hS : 0<S := cartesianNarrowScale_pos hs i
  have hr : 0<r := dyadicCoefficientScale_pos hS k
  refine (radianHighReferenceBlock_eq_regularizedLowCartesianSymbol
    (cartesianNarrowProfile w i) η χ b hr p ?_).symm
  intro hp
  have hlo := (cartesianNarrowProfile_support w h₁ h₀ i _ hp).1
  rw [norm_smul,Real.norm_of_nonneg (div_nonneg hr.le hτ.le)] at hlo
  have hScale : r≤S := div_le_self hS.le (one_le_pow₀ (by norm_num))
  have lower := hlo.trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hScale hτ.le) (norm_nonneg _))
  apply hη
  apply (div_le_iff₀ hS).mpr
  have h := (le_div_iff₀ hτ).mp (by simpa only [div_mul_eq_mul_div] using lower)
  simpa only [one_mul,mul_comm S ‖p.2‖] using h

private theorem narrowReferenceOrbit_measurable_and_growth (A : Joint → ℂ)
    (hc : HasCompactSupport A) (hA : Continuous A)
    (hBand : ∀ p : Joint, A p≠0 → 1≤‖p.2‖ ∧ ‖p.2‖≤5/4) {s : ℝ} (hs : 0<s) :
    Measurable (narrowReferenceOrbitSymbol A s) ∧
      ∃ B : ℝ, 0≤B ∧ ∀ p : Joint, ‖narrowReferenceOrbitSymbol A s p‖ ≤ B*(1+‖p.1‖+‖p.2‖) := by
  have lim := narrowReferenceOrbitPartial_tendsto A hBand hs
  have hm (n : ℕ) : Measurable (narrowReferenceOrbitPartial A s n) := by
    unfold narrowReferenceOrbitPartial
    exact measurable_sum _ fun k _ =>
      (continuous_const.smul (hA.comp (continuous_const.smul continuous_id))).measurable
  have hMeas := measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.mpr lim)
  obtain ⟨B,B0,hB⟩ := exists_narrowReferenceOrbitPartial_order_bound A hA hc hBand
  refine ⟨hMeas,B,B0,fun p => ?_⟩
  have h := le_of_tendsto' (lim p).norm (fun n => hB hs n p)
  exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) B0)

private theorem cartesianNarrowOrbit_measurable_and_growth (w : SchwartzMap E ℂ)
    (h₁ : ∀ q : E, ‖q‖≤1 → w q=1) (h₀ : ∀ q : E, (17/16 : ℝ)≤‖q‖ → w q=0)
    (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ : ℝ} (hρ : 0≤ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ r≥ρ^2, χ r=0)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) {s : ℝ} (hs : 0<s) (hη : ∀ r≥tau/(2*s), η r=1)
    {i : ℕ} (hi : i<8) :
    Measurable (cartesianNarrowOrbitSymbol w s i η χ b) ∧
      ∃ B : ℝ, 0≤B ∧ ∀ p : Joint, ‖cartesianNarrowOrbitSymbol w s i η χ b p‖≤B*(1+‖p.1‖+‖p.2‖) := by
  let a := cartesianNarrowProfile w i
  let A := lowCartesianHighAnnularReference a χ b
  have band (q : E) (hq : a q≠0) : 1≤‖q‖ ∧ ‖q‖≤5/4 :=
    cartesianNarrowProfile_support w h₁ h₀ i q hq
  obtain ⟨hc,hA⟩ := lowCartesianHighAnnularReference_regular a χ b
    (by norm_num : (0:ℝ)<1) hρ hχ hcut (cartesianNarrowProfile_contDiff w i) band hV hContains hb
  have support (p : Joint) (hp : A p≠0) : 1≤‖p.2‖ ∧ ‖p.2‖≤5/4 := by
    obtain ⟨hl,hu,_⟩ := lowCartesianHighAnnularReference_support a χ b hρ hcut band p hp
    exact ⟨hl,hu⟩
  rw [cartesianNarrowOrbit_eq_reference (i := i) w h₁ h₀ hs η χ b (cartesianNarrowOrbit_plateau hs η hη hi)]
  exact narrowReferenceOrbit_measurable_and_growth A hc hA.continuous support (cartesianNarrowScale_pos hs i)

theorem cartesianHighComplement_measurable_and_growth
    (w : SchwartzMap E ℂ) (h₁ : ∀ q : E, ‖q‖≤1 → w q=1)
    (h₀ : ∀ q : E, (17/16 : ℝ)≤‖q‖ → w q=0)
    (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ : ℝ}
    (hρ : 0≤ρ) (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ r≥ρ^2, χ r=0)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) {s : ℝ} (hs : 0<s) (hη : ∀ r≥tau/(2*s), η r=1) :
    Measurable (cartesianHighComplement w s η χ b) ∧
      ∃ B : ℝ, 0≤B ∧ ∀ z : Joint, ‖cartesianHighComplement w s η χ b z‖≤B*(1+‖z.1‖+‖z.2‖) := by
  classical
  let S i := cartesianNarrowOrbitSymbol w s i η χ b
  have hProps (i : ℕ) (hi : i ∈ range 8) :
      Measurable (S i) ∧ ∃ B : ℝ, 0≤B ∧ ∀ z : Joint, ‖S i z‖≤B*(1+‖z.1‖+‖z.2‖) :=
    cartesianNarrowOrbit_measurable_and_growth w h₁ h₀ η χ b hρ hχ hcut hV hContains hb hs hη (mem_range.mp hi)
  choose C hC hBound using fun i (hi : i ∈ range 8) => (hProps i hi).2
  let B (i : ℕ) := if hi : i ∈ range 8 then C i hi else 0
  have hB0 (i : ℕ) (hi : i ∈ range 8) : 0≤B i := by simpa only [B,dif_pos hi] using hC i hi
  have hB (i : ℕ) (hi : i ∈ range 8) (z : Joint) : ‖S i z‖≤B i*(1+‖z.1‖+‖z.2‖) := by
    simpa only [B,dif_pos hi] using hBound i hi z
  rw [← funext (cartesianHighComplement_eq_narrowOrbit_sum w h₁ h₀ s η χ b)]
  refine ⟨measurable_sum _ (fun i hi => (hProps i hi).1),∑ i ∈ range 8, B i,sum_nonneg hB0,fun z => ?_⟩
  calc
    ‖∑ i ∈ range 8, S i z‖ ≤ ∑ i ∈ range 8, ‖S i z‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range 8, B i*(1+‖z.1‖+‖z.2‖) := sum_le_sum fun i hi => hB i hi z
    _ = _ := (sum_mul _ _ _).symm

/-- The eight orbit constants add to give a bound for the complete high
part of the same original Cartesian symbol. All input tests and the
Lipschitz coefficient are the same as in the single-orbit estimate. -/
theorem exists_cartesianHighComplement_radian_bound_paper
    (inputL2 : Bool)
    (w : SchwartzMap E ℂ) (h₁ : ∀ q : E, ‖q‖≤1 → w q=1)
    (h₀ : ∀ q : E, (17/16 : ℝ)≤‖q‖ → w q=0)
    (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ≤1/2) (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ r≥ρ^2, χ r=0)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {s : ℝ}, 0<s → (∀ r≥tau/(2*s), η r=1) → ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (cartesianHighComplement w s η χ b) (fun x => (D x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  classical
  choose C hC bounds using fun i : ℕ => exists_narrowCartesian_highOrbit_radian_bound_paper inputL2
    (cartesianNarrowProfile w i) η χ b hρ hρ' hχ hcut (cartesianNarrowProfile_contDiff w i)
    (fun q hq => cartesianNarrowProfile_support w h₁ h₀ i q hq) hV hContains hb
  refine ⟨∑ i ∈ range 8, C i,ENNReal.sum_lt_top.mpr fun i _ => hC i,?_⟩
  intro D L hD s hs hIR f g h
  let S i := cartesianNarrowOrbitSymbol w s i η χ b
  have hProps (i : ℕ) (hi : i∈range 8) :
      Measurable (S i) ∧ ∃ B : ℝ, 0≤B ∧ ∀ p : Joint, ‖S i p‖≤B*(1+‖p.1‖+‖p.2‖) :=
    cartesianNarrowOrbit_measurable_and_growth w h₁ h₀ η χ b hρ hχ hcut hV hContains hb hs hIR (mem_range.mp hi)
  have hMeas i hi := (hProps i hi).1
  choose B hB₀ hB using fun i (hi : i ∈ range 8) => (hProps i hi).2
  let Btotal (i : ℕ) := if hi : i∈range 8 then B i hi else 0
  have B0 (i : ℕ) (hi : i∈range 8) : 0≤Btotal i := by simpa only [Btotal,dif_pos hi] using hB₀ i hi
  have Bsize (i : ℕ) (hi : i∈range 8) (p : Joint) : ‖S i p‖≤Btotal i*(1+‖p.1‖+‖p.2‖) := by
    simpa only [Btotal,dif_pos hi] using hB i hi p
  have eq : cartesianHighComplement w s η χ b = fun p => ∑ i ∈ range 8, S i p :=
    (funext (cartesianHighComplement_eq_narrowOrbit_sum w h₁ h₀ s η χ b)).symm
  rw [eq,radianHighCommutatorPair_sum_schwartz_symbols _ S Btotal hMeas B0 Bsize]
  calc
    _ ≤ ∑ i ∈ range 8, ‖radianHighCommutatorPair (S i) (fun x => (D x).re) f g h‖ₑ :=
      enorm_sum_le _ _
    _ ≤ ∑ i ∈ range 8, (L : ℝ≥0∞)*C i*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
      refine sum_le_sum fun i hi => ?_
      exact bounds i D L hD (cartesianNarrowScale_pos hs i)
        (cartesianNarrowOrbit_plateau hs η hIR (mem_range.mp hi)) f g h
    _ = _ := by rw [← sum_mul,← mul_sum]

theorem exists_cartesianHighComplement_radian_bound
    (w : SchwartzMap E ℂ) (h₁ : ∀ q : E, ‖q‖≤1 → w q=1)
    (h₀ : ∀ q : E, (17/16 : ℝ)≤‖q‖ → w q=0)
    (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ≤1/2) (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ r≥ρ^2, χ r=0)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {s : ℝ}, 0<s → (∀ r≥tau/(2*s), η r=1) → ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (cartesianHighComplement w s η χ b) (fun x => (D x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_cartesianHighComplement_radian_bound_paper false w h₁ h₀ η χ b hρ hρ' hχ hcut hV hContains hb

end Burnett.A06
