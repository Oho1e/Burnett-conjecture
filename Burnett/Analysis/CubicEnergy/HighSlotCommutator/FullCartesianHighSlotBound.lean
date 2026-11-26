import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CartesianNarrowHighSum
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CartesianInfraredKernel

set_option autoImplicit false
set_option maxHeartbeats 4200000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal

/-- The three coefficient ranges of the narrow orbit proof, summed over
the eight actual operator profiles and the compact infrared transition,
bound the original fixed Cartesian symbol in the actual radian pairing. -/
theorem exists_regularizedLowCartesian_highSlotSchwartz_bound_paper
    (inputL2 : Bool)
    (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ r R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ≤1/2) (hr : 0<r) (hR : 0<R)
    (hη : ContDiff ℝ ∞ η) (hηzero : ∀ z≤r, η z=0) (hηone : ∀ z≥R, η z=1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ z≥ρ^2, χ z=0)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (regularizedLowCartesianSymbol η χ b) (fun x => (D x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨w,_hw,h₁,h₀,_hRadial⟩ := exists_coefficientRadialProfile 1 (17/16) (by norm_num) (by norm_num)
  have hτ : 0<tau := mul_pos (by norm_num) Real.pi_pos
  let s := tau/(2*R)
  have hs : 0<s := by unfold s; positivity
  have eqThreshold : tau/(2*s)=R := by
    unfold s
    field_simp [hτ.ne',hR.ne']
  have hIR : ∀ z≥tau/(2*s), η z=1 := by
    rw [eqThreshold]
    exact hηone
  let high := cartesianHighComplement w s η χ b
  let low := cartesianRemainderSymbol w s η χ b
  have eq : regularizedLowCartesianSymbol η χ b = fun p => high p+low p := by
    funext p
    dsimp only [high,low,cartesianHighComplement,cartesianRemainderSymbol]
    ring
  obtain ⟨hHm,BH,hBH0,hBH⟩ := cartesianHighComplement_measurable_and_growth
    w h₁ h₀ η χ b hρ hχ hcut hV hContains hb hs hIR
  obtain ⟨hLc,hLr⟩ := cartesianRemainderSymbol_regular
    w h₀ hs hr hρ η χ b hη hηzero hχ hcut hV hContains hb
  obtain ⟨BL,hBL0,hBL⟩ := exists_cartesianCompact_orderOne_size low hLc hLr.continuous
  obtain ⟨MH,hMH,boundH⟩ := exists_cartesianHighComplement_radian_bound_paper inputL2
    w h₁ h₀ η χ b hρ hρ' hχ hcut hV hContains hb
  obtain ⟨ML,hML,boundL⟩ := exists_compactRadianHighCommutatorPair_bound low hLc hLr
  refine ⟨MH+ML,ENNReal.add_lt_top.mpr ⟨hMH,hML⟩,?_⟩
  intro D L hD f g h
  rw [eq,radianHighCommutatorPair_add_schwartz_symbols high low BH BL hHm hLr.continuous.measurable
    hBH0 hBL0 hBH hBL D f g h]
  calc
    _ ≤ ‖radianHighCommutatorPair high (fun x => (D x).re) f g h‖ₑ +
        ‖radianHighCommutatorPair low (fun x => (D x).re) f g h‖ₑ := enorm_add_le _ _
    _ ≤ (L : ℝ≥0∞)*MH*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) +
        (L : ℝ≥0∞)*ML*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) :=
      add_le_add (boundH D L hD hs hIR f g h) (by
        cases inputL2
        · exact (boundL D L hD f g h).1
        · exact (boundL D L hD f g h).2)
    _ = _ := by rw [← add_mul,← mul_add]

theorem exists_regularizedLowCartesian_highSlotSchwartz_bound
    (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ r R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ≤1/2) (hr : 0<r) (hR : 0<R)
    (hη : ContDiff ℝ ∞ η) (hηzero : ∀ z≤r, η z=0) (hηone : ∀ z≥R, η z=1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ z≥ρ^2, χ z=0)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (regularizedLowCartesianSymbol η χ b) (fun x => (D x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_regularizedLowCartesian_highSlotSchwartz_bound_paper false η χ b hρ hρ' hr hR hη hηzero hηone hχ hcut hV hContains hb

/-- The coefficient in the actual radian estimate is a real Schwartz
function, with its original Lipschitz constant. -/
theorem exists_regularizedLowCartesian_realSchwartz_highSlot_bound_paper
    (inputL2 : Bool)
    (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ r R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ≤1/2) (hr : 0<r) (hR : 0<R)
    (hη : ContDiff ℝ ∞ η) (hηzero : ∀ z≤r, η z=0) (hηone : ∀ z≥R, η z=1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ z≥ρ^2, χ z=0)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (d : SchwartzMap E ℝ) (L : ℝ≥0), LipschitzWith L d →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (regularizedLowCartesianSymbol η χ b) d f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨M,hM,bound⟩ := exists_regularizedLowCartesian_highSlotSchwartz_bound_paper inputL2
    η χ b hρ hρ' hr hR hη hηzero hηone hχ hcut hV hContains hb
  refine ⟨M,hM,?_⟩
  intro d L hLip f g h
  let D : SchwartzMap E ℂ :=
    { toFun := Complex.ofRealLI ∘ d
      smooth' := Complex.ofRealCLM.contDiff.comp d.smooth'
      decay' := by
        intro k n
        obtain ⟨B,hB⟩ := d.decay' k n
        refine ⟨B,fun x => ?_⟩
        rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left (d.smooth n).contDiffAt le_rfl]
        exact hB x }
  have hD : LipschitzWith L D := by
    simpa only [one_mul] using Complex.isometry_ofReal.lipschitz.comp hLip
  have eq : (fun x => (D x).re) = (d : E → ℝ) := by
    funext x
    exact Complex.ofReal_re (d x)
  simpa only [eq] using bound D L hD f g h

theorem exists_regularizedLowCartesian_realSchwartz_highSlot_bound
    (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ r R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ≤1/2) (hr : 0<r) (hR : 0<R)
    (hη : ContDiff ℝ ∞ η) (hηzero : ∀ z≤r, η z=0) (hηone : ∀ z≥R, η z=1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ z≥ρ^2, χ z=0)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (d : SchwartzMap E ℝ) (L : ℝ≥0), LipschitzWith L d →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (regularizedLowCartesianSymbol η χ b) d f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_regularizedLowCartesian_realSchwartz_highSlot_bound_paper false η χ b hρ hρ' hr hR hη hηzero hηone hχ hcut hV hContains hb

/-- The original Cartesian commutator with low input L⁴, high input L²,
and high test L⁴, for a real Schwartz coefficient. -/
theorem exists_regularizedLowCartesian_realSchwartz_highSlot_inputL2_bound
    (η χ : ℝ → ℝ) (b : Joint → ℂ) {ρ r R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ≤1/2) (hr : 0<r) (hR : 0<R)
    (hη : ContDiff ℝ ∞ η) (hηzero : ∀ z≤r, η z=0) (hηone : ∀ z≥R, η z=1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ z≥ρ^2, χ z=0)
    {V : Set Joint} (hV : IsOpen V) (hContains : closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V)
    (hb : ContDiffOn ℝ ∞ b V) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (d : SchwartzMap E ℝ) (L : ℝ≥0), LipschitzWith L d →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (regularizedLowCartesianSymbol η χ b) d f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 2 4 :=
  exists_regularizedLowCartesian_realSchwartz_highSlot_bound_paper true
    η χ b hρ hρ' hr hR hη hηzero hηone hχ hcut hV hContains hb

end Burnett.A06
