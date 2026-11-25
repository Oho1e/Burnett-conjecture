import Burnett.Analysis.TransportPatches.ScreenSmoothSupport
import Burnett.Analysis.TransportPatches.ScreenWideSupport
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
set_option maxHeartbeats 3700000

noncomputable section

namespace Burnett.V06

open Matrix Set Filter Burnett.RicciSymbol TensorFrame
open scoped Matrix BigOperators ContDiff Topology

/-- A smooth angular cutoff equal to one on the inner cone and zero on and
beyond the outer boundary. The argument is the phase of a unit covector. -/
def angularScreenCutoff (r R f : ℝ) : ℝ :=
  1 - Real.smoothTransition ((f^2 - r^2) / (R^2 - r^2))

theorem angularScreenCutoff_one (r R f : ℝ) (hr : 0 ≤ r) (hR : r < R) (h : |f| ≤ r) :
    angularScreenCutoff r R f = 1 := by
  have hD : 0 < R^2 - r^2 := sub_pos.mpr ((sq_lt_sq₀ hr (hr.trans hR.le)).2 hR)
  have hAbs : |f| ≤ |r| := by simpa only [abs_of_nonneg hr] using h
  have hnum : f^2 - r^2 ≤ 0 := sub_nonpos.mpr (sq_le_sq.2 hAbs)
  simp [angularScreenCutoff, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hnum hD.le)]

theorem angularScreenCutoff_zero (r R f : ℝ) (hr : 0 ≤ r) (hR : r < R) (h : R ≤ |f|) :
    angularScreenCutoff r R f = 0 := by
  have hD : 0 < R^2 - r^2 := sub_pos.mpr ((sq_lt_sq₀ hr (hr.trans hR.le)).2 hR)
  have hf : R^2 ≤ f^2 := sq_le_sq.2 (by simpa [abs_of_nonneg (hr.trans hR.le)] using h)
  have ht : 1 ≤ (f^2 - r^2) / (R^2 - r^2) := (le_div_iff₀ hD).2 (by linarith)
  simp [angularScreenCutoff, Real.smoothTransition.one_of_one_le ht]

/-- The full angularly cut off multiplier symbol. The uncut formula is used
on the inner cone, with the same input tensor and normalized direction. -/
def globalAngularScreenSymbol (r R : ℝ) (B H : ScreenMatrix) (q : Covector) : ScreenMatrix :=
  angularScreenCutoff r R (symbolNorm B (screenUnitCovector q)) • frozenScreenSymbol B H q

theorem globalAngularScreenSymbol_eq_on_inner
    (r R : ℝ) (hr : 0 ≤ r) (hR : r < R) (B H : ScreenMatrix) (q : Covector)
    (h : |symbolNorm B (screenUnitCovector q)| ≤ r) :
    globalAngularScreenSymbol r R B H q = frozenScreenSymbol B H q := by
  rw [globalAngularScreenSymbol, angularScreenCutoff_one _ _ _ hr hR h, one_smul]

theorem globalAngularScreenSymbol_eq_zero_on_outer
    (r R : ℝ) (hr : 0 ≤ r) (hR : r < R) (B H : ScreenMatrix) (q : Covector)
    (h : R ≤ |symbolNorm B (screenUnitCovector q)|) :
    globalAngularScreenSymbol r R B H q = 0 := by
  rw [globalAngularScreenSymbol, angularScreenCutoff_zero _ _ _ hr hR h, zero_smul]

theorem globalAngularScreenSymbol_degreeZero (r R : ℝ) (B H : ScreenMatrix)
    (q : Covector) (c : ℝ) (hc : 0 < c) :
    globalAngularScreenSymbol r R B H (c • q) = globalAngularScreenSymbol r R B H q := by
  rw [globalAngularScreenSymbol, globalAngularScreenSymbol, screenUnitCovector_scale q c hc,
    frozenScreenSymbol_degreeZero B H q c hc]

private theorem symbolNorm_smul (B : ScreenMatrix) (q : Covector) (c : ℝ) :
    symbolNorm B (c • q) = c^2 * symbolNorm B q := by
  simp only [symbolNorm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem globalAngularScreenSymbol_even (r R : ℝ) (B H : ScreenMatrix) (q : Covector) :
    globalAngularScreenSymbol r R B H (-q) = globalAngularScreenSymbol r R B H q := by
  have hs : symbolNorm B (-screenUnitCovector q) = symbolNorm B (screenUnitCovector q) := by
    rw [← neg_one_smul ℝ (screenUnitCovector q), symbolNorm_smul]
    norm_num
  rw [globalAngularScreenSymbol, globalAngularScreenSymbol, screenUnitCovector_neg, hs,
    frozenScreenSymbol_even]

private theorem symbolNorm_unit_eq (B : ScreenMatrix) (q : Covector) :
    symbolNorm B (screenUnitCovector q) = symbolNorm B q / (q ⬝ᵥ q) := by
  have h : 0 ≤ q ⬝ᵥ q := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  rw [screenUnitCovector, symbolNorm_smul, inv_pow, Real.sq_sqrt h, div_eq_mul_inv, mul_comm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem smooth_unit_phase (U : Set E) (B : E → ScreenMatrix) (q : E → Covector)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun x => B x i j) U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x => q x i) U) (hQ₀ : ∀ x ∈ U, q x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => symbolNorm (B x) (screenUnitCovector (q x))) U := by
  simp only [symbolNorm_unit_eq]
  have hn : ContDiffOn ℝ ∞ (fun x => symbolNorm (B x) (q x)) U :=
    ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => ((hB i j).mul (hQ i)).mul (hQ j)))
  have hd : ContDiffOn ℝ ∞ (fun x => q x ⬝ᵥ q x) U :=
    ContDiffOn.sum (fun i _ => (hQ i).mul (hQ i))
  exact hn.div hd (fun x hx hz => hQ₀ x hx (dotProduct_self_eq_zero.mp hz))

/-- The constructed angular cutoff makes the whole symbol smooth wherever
the frequency is nonzero, on the same compact metric family. -/
theorem exists_globalAngularScreenSymbol_contDiffOn
    (K : Set ScreenMatrix) (hK : IsCompact K)
    (hInv : ∀ B ∈ K, IsUnit B.det) (hFrame : ∀ B ∈ K, Nonempty (LorentzFrame B)) :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧ ∀ (U : Set E) (B H : E → ScreenMatrix) (q : E → Covector),
      (∀ x ∈ U, B x ∈ K) →
      (∀ i j, ContDiffOn ℝ ∞ (fun x => B x i j) U) →
      (∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) U) →
      (∀ i, ContDiffOn ℝ ∞ (fun x => q x i) U) →
      (∀ x ∈ U, q x ≠ 0) → ∀ i j : Index,
        ContDiffOn ℝ ∞ (fun x => globalAngularScreenSymbol r R (B x) (H x) (q x) i j) U := by
  obtain ⟨ε, hε, hWide⟩ := exists_uniform_wide_screen_invertibility K hK hInv hFrame
  let r := ε / 3
  let R := 2 * ε / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : r < R := by dsimp [r, R]; linarith
  have hRε : R < ε := by dsimp [R]; linarith
  refine ⟨r, R, hr, hR, ?_⟩
  intro U B H q hMem hB hH hQ hQ₀ i j
  let s (x : E) := symbolNorm (B x) (screenUnitCovector (q x))
  let inner : Set E := U ∩ {x | |s x| < ε}
  let outer : Set E := U ∩ {x | R < |s x|}
  let f (x : E) := globalAngularScreenSymbol r R (B x) (H x) (q x) i j
  have hi : inner ⊆ U := inter_subset_left
  have hs : ContDiffOn ℝ ∞ s U := smooth_unit_phase U B q hB hQ hQ₀
  have hScalar : ContDiffOn ℝ ∞ (fun x => angularScreenCutoff r R (s x)) U := by
    unfold angularScreenCutoff
    exact contDiffOn_const.sub (Real.smoothTransition.contDiff.comp_contDiffOn
      (((hs.pow 2).sub contDiffOn_const).div_const (R^2 - r^2)))
  have hInner (x : E) (hx : x ∈ inner) :=
    hWide (B x) (hMem x hx.1) (screenUnitCovector (q x)) (screenUnitCovector_unit _ (hQ₀ x hx.1)) hx.2
  have hSmoothInner : ContDiffOn ℝ ∞ f inner := by
    have hp := frozenScreenSymbol_contDiffOn inner B H q (fun i j => (hB i j).mono hi)
      (fun i j => (hH i j).mono hi) (fun k => (hQ k).mono hi) (fun x hx => hQ₀ x hx.1)
      (fun x hx => (hInner x hx).1) (fun x hx => isUnit_iff_ne_zero.mp (hInner x hx).2) i j
    exact (hScalar.mono hi).mul hp
  have hSmoothOuter : ContDiffOn ℝ ∞ f outer := by
    refine (contDiffOn_const (c := (0 : ℝ))).congr ?_
    intro x hx
    change f x = 0
    simp [f, globalAngularScreenSymbol_eq_zero_on_outer r R hr.le hR (B x) (H x) (q x) hx.2.le]
  intro x hx
  have hcont : ContinuousWithinAt (fun y => |s y|) U x := (hs x hx).continuousWithinAt.abs
  by_cases hTest : |s x| < ε
  · have hInnerMem : inner ∈ 𝓝[U] x :=
      inter_mem self_mem_nhdsWithin (hcont.eventually (Iio_mem_nhds hTest))
    exact (hSmoothInner x ⟨hx, hTest⟩).mono_of_mem_nhdsWithin hInnerMem
  · have hTest' : R < |s x| := hRε.trans_le (le_of_not_gt hTest)
    have hOuterMem : outer ∈ 𝓝[U] x :=
      inter_mem self_mem_nhdsWithin (hcont.eventually (Ioi_mem_nhds hTest'))
    exact (hSmoothOuter x ⟨hx, hTest'⟩).mono_of_mem_nhdsWithin hOuterMem

end Burnett.V06
