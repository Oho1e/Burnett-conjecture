import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CartesianHighSlotFiniteSeminorm

set_option autoImplicit false
set_option maxHeartbeats 4400000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Finset Metric Set
open scoped ContDiff ENNReal NNReal BigOperators

private theorem finite_le_smooth (n : ℕ) : (n : WithTop ℕ∞)≤((⊤ : ℕ∞) : WithTop ℕ∞) := by
  change ((n : ℕ∞) : WithTop ℕ∞)≤((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

/-- A single normalized angular jet budget bounds the original `(4,4,2)`
high-slot pairing for every member of the actual angular coefficient family. -/
theorem exists_regularizedLowCartesian_highSlot_angularJetBound_paper (inputL2 : Bool)
    (η χ : ℝ → ℝ) {ρ r R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hr : 0<r) (hR : 1≤R)
    (hη : ContDiff ℝ ∞ η) (hηzero : ∀ z≤r, η z=0) (hηone : ∀ z≥R, η z=1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ z≥ρ^2, χ z=0) :
    ∃ (K : ℕ) (C : ℝ), 0≤C ∧ ∀ {V : Set Joint}, IsOpen V →
      closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V →
      ∀ (b : Joint → ℂ) (A : ℝ), 0≤A → ContDiffOn ℝ ∞ b V →
      (∀ n≤K, ∀ z ∈ closedBall (0:E) ρ ×ˢ sphere (0:E) 1,
        ‖iteratedFDeriv ℝ n b z‖≤A) →
      ∀ (d : SchwartzMap E ℝ) (L : ℝ≥0), LipschitzWith L d →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (regularizedLowCartesianSymbol η χ b) d f g h‖ₑ≤
        (L : ℝ≥0∞)*ENNReal.ofReal (C*A)*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨K,U,hU,high⟩ := exists_regularizedLowCartesian_highSlot_finiteSeminorm_bound_paper inputL2 hρ hρ' hR
  choose C hC jets using fun n : ℕ => exists_regularizedLowCartesianSymbol_quantitative_orderOne_bound
    n η χ hr hρ hR (hη.of_le (finite_le_smooth n)) hηzero hηone
    (hχ.of_le (finite_le_smooth n)) hcut
  let W := ∑ n ∈ range (K+1), C n
  have hW : 0≤W := sum_nonneg fun _ _ => hC _
  refine ⟨K,U*W,mul_nonneg hU hW,?_⟩
  intro V hV hContains b A hA hb hJets d L hd f g h
  let a := regularizedLowCartesianSymbol η χ b
  have ha : a ∈ orderOneSymbolSubmodule ℂ :=
    regularizedLowCartesianSymbol_mem_orderOneSymbolSubmodule η χ b hr hρ hR hη hηzero hηone hχ hcut
      hV hContains hb
  let B : OrderOneSymbol ℂ := ⟨a,ha⟩
  have orderBound : realOrderOneSymbolSeminorm ℂ K B≤W*A := by
    apply (orderOneSymbolSeminorm_le_iff (mul_nonneg hW hA) B).mpr
    intro n hn x
    have fit := jets n hV hContains b A hA (hb.of_le (finite_le_smooth n))
      (fun i hi z hz => hJets i (hi.trans hn) z hz) x
    have hj : orderOneWeightedJet n (B : Joint → ℂ) x≤C n*A := by
      rw [orderOneWeightedJet,← mul_div_assoc,div_le_iff₀ (symbolFrequencyWeight_pos x)]
      exact fit
    exact hj.trans (mul_le_mul_of_nonneg_right
      (single_le_sum (fun i _ => hC i) (mem_range.mpr (Nat.lt_succ_of_le hn))) hA)
  let D : SchwartzMap E ℂ :=
    { toFun := Complex.ofRealLI ∘ d
      smooth' := Complex.ofRealCLM.contDiff.comp d.smooth'
      decay' := by
        intro k n
        obtain ⟨M,hM⟩ := d.decay' k n
        refine ⟨M,fun x => ?_⟩
        rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left (d.smooth n).contDiffAt le_rfl]
        exact hM x }
  have hD : LipschitzWith L D := by
    simpa only [one_mul] using Complex.isometry_ofReal.lipschitz.comp hd
  have eq : (fun x => (D x).re)=(d : E → ℝ) := funext fun x => Complex.ofReal_re (d x)
  have H := high η χ b hηone hcut ha D L hD f g h
  rw [eq] at H
  refine H.trans (mul_le_mul_right' (mul_le_mul_left' (ENNReal.ofReal_le_ofReal ?_) _) _)
  exact (mul_le_mul_of_nonneg_left orderBound hU).trans_eq (by ring)

theorem exists_regularizedLowCartesian_highSlot_angularJetBound
    (η χ : ℝ → ℝ) {ρ r R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hr : 0<r) (hR : 1≤R)
    (hη : ContDiff ℝ ∞ η) (hηzero : ∀ z≤r, η z=0) (hηone : ∀ z≥R, η z=1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ z≥ρ^2, χ z=0) :
    ∃ (K : ℕ) (C : ℝ), 0≤C ∧ ∀ {V : Set Joint}, IsOpen V →
      closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V →
      ∀ (b : Joint → ℂ) (A : ℝ), 0≤A → ContDiffOn ℝ ∞ b V →
      (∀ n≤K, ∀ z ∈ closedBall (0:E) ρ ×ˢ sphere (0:E) 1,
        ‖iteratedFDeriv ℝ n b z‖≤A) →
      ∀ (d : SchwartzMap E ℝ) (L : ℝ≥0), LipschitzWith L d →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (regularizedLowCartesianSymbol η χ b) d f g h‖ₑ≤
        (L : ℝ≥0∞)*ENNReal.ofReal (C*A)*triLpMass f g h 4 4 2 :=
  exists_regularizedLowCartesian_highSlot_angularJetBound_paper false η χ hρ hρ' hr hR hη hηzero hηone hχ hcut

theorem exists_regularizedLowCartesian_highSlot_inputL2_angularJetBound
    (η χ : ℝ → ℝ) {ρ r R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hr : 0<r) (hR : 1≤R)
    (hη : ContDiff ℝ ∞ η) (hηzero : ∀ z≤r, η z=0) (hηone : ∀ z≥R, η z=1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ z≥ρ^2, χ z=0) :
    ∃ (K : ℕ) (C : ℝ), 0≤C ∧ ∀ {V : Set Joint}, IsOpen V →
      closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V →
      ∀ (b : Joint → ℂ) (A : ℝ), 0≤A → ContDiffOn ℝ ∞ b V →
      (∀ n≤K, ∀ z ∈ closedBall (0:E) ρ ×ˢ sphere (0:E) 1,
        ‖iteratedFDeriv ℝ n b z‖≤A) →
      ∀ (d : SchwartzMap E ℝ) (L : ℝ≥0), LipschitzWith L d →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (regularizedLowCartesianSymbol η χ b) d f g h‖ₑ≤
        (L : ℝ≥0∞)*ENNReal.ofReal (C*A)*triLpMass f g h 4 2 4 :=
  exists_regularizedLowCartesian_highSlot_angularJetBound_paper true η χ hρ hρ' hr hR hη hηzero hηone hχ hcut

/-- The same angular jet order and constant control both original
placements of the high input and high test exponents. -/
theorem exists_regularizedLowCartesian_highSlot_common_angularJetBound
    (η χ : ℝ → ℝ) {ρ r R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hr : 0<r) (hR : 1≤R)
    (hη : ContDiff ℝ ∞ η) (hηzero : ∀ z≤r, η z=0) (hηone : ∀ z≥R, η z=1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ z≥ρ^2, χ z=0) :
    ∃ (K : ℕ) (C : ℝ), 0≤C ∧ ∀ (inputL2 : Bool) {V : Set Joint}, IsOpen V →
      closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V →
      ∀ (b : Joint → ℂ) (A : ℝ), 0≤A → ContDiffOn ℝ ∞ b V →
      (∀ n≤K, ∀ z ∈ closedBall (0:E) ρ ×ˢ sphere (0:E) 1,
        ‖iteratedFDeriv ℝ n b z‖≤A) →
      ∀ (d : SchwartzMap E ℝ) (L : ℝ≥0), LipschitzWith L d →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (regularizedLowCartesianSymbol η χ b) d f g h‖ₑ≤
        (L : ℝ≥0∞)*ENNReal.ofReal (C*A)*
          triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  choose K C C0 bound using fun inputL2 : Bool =>
    exists_regularizedLowCartesian_highSlot_angularJetBound_paper inputL2
      η χ hρ hρ' hr hR hη hηzero hηone hχ hcut
  let Kmax := max (K false) (K true)
  let Cmax := max (C false) (C true)
  have hK (inputL2 : Bool) : K inputL2≤Kmax := by
    cases inputL2
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hC (inputL2 : Bool) : C inputL2≤Cmax := by
    cases inputL2
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine ⟨Kmax,Cmax,(C0 false).trans (hC false),?_⟩
  intro inputL2 V hV hContains b A hA hb hJets d L hd f g h
  refine (bound inputL2 hV hContains b A hA hb
    (fun n hn => hJets n (hn.trans (hK inputL2))) d L hd f g h).trans ?_
  exact mul_le_mul_right' (mul_le_mul_left'
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hC inputL2) hA)) _) _

end Burnett.A06
