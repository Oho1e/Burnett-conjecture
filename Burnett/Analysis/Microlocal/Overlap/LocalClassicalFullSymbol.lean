import Burnett.Analysis.Microlocal.Overlap.ActualClassicalFullSymbol
import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingClassicalPairings

/-! Left localization of full symbols given on the open coordinate window. -/

set_option autoImplicit false
set_option maxRecDepth 3400
set_option maxHeartbeats 2900000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open UnitCosphere (Cosphere)
open FixedCotangentChart (fixedChartPhase)
open Burnett.Microlocal.AtlasVolumeGradient
  (fixedVolumeGradientSchwartz fixedVolumeGradientSchwartz_tsupport coeffMul_tsupport_subset_real)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul coeffMul_toLp)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.SeparablePositive (conjugateSymbol conjugateSymbol_apply inner_symbolCLM_left)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Manifold Topology

open private firstOrderAction_mul_base from Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal

local notation "E" => CoordinateSpace

/-- Left multiplication by the real test cutoff in the symbol's base variable. -/
def leftCutoffClassicalSymbol (χ : D) (a : E → E → ℂ) (x ξ : E) : ℂ :=
  physicalCoefficient χ x * a x ξ

private theorem physicalCoefficient_smooth (χ : D) : ContDiff ℝ ∞ (physicalCoefficient χ : E → ℂ) :=
  Complex.ofRealCLM.contDiff.comp (test_smooth χ)

theorem leftCutoffClassicalSymbol_support (χ : D) (a : E → E → ℂ) (ξ : E) :
    tsupport (fun x => leftCutoffClassicalSymbol χ a x ξ) ⊆ tsupport (χ : E → ℝ) := by
  apply closure_mono
  intro x hx
  by_contra hz
  have he : (χ : E → ℝ) x = 0 := by simpa only [Function.mem_support, not_not] using hz
  exact hx (by simp [leftCutoffClassicalSymbol, physicalCoefficient, he])

theorem leftCutoffClassicalSymbol_smoothOn (χ : D) {U W : Set E} (hU : IsOpen U) (hW : IsOpen W)
    (hχ : tsupport (χ : E → ℝ) ⊆ U) {p : E → E → ℂ}
    (hp : ContDiffOn ℝ ∞ (uncurry p) (U ×ˢ W)) :
    ContDiffOn ℝ ∞ (uncurry (leftCutoffClassicalSymbol χ p)) (univ ×ˢ W) := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  by_cases hzU : z.1 ∈ U
  · exact ((physicalCoefficient_smooth χ).comp contDiff_fst).contDiffAt.mul
      (hp.contDiffAt ((hU.prod hW).mem_nhds ⟨hzU, hz.2⟩))
  · have hZero := notMem_tsupport_iff_eventuallyEq.mp (fun hzS => hzU (hχ hzS))
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hZero.comp_tendsto (continuous_fst.tendsto z)] with q hq
    change (χ : E → ℝ) q.1 = 0 at hq
    change (physicalCoefficient χ q.1) * p q.1 q.2 = 0
    simp [physicalCoefficient, hq]

theorem leftCutoffClassicalSymbol_smoothZero (χ : D) {U : Set E} (hU : IsOpen U)
    (hχ : tsupport (χ : E → ℝ) ⊆ U) {a : E → E → ℂ}
    (ha : ContDiffOn ℝ ∞ (fun x => a x 0) U) :
    ContDiff ℝ ∞ (fun x => leftCutoffClassicalSymbol χ a x 0) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact (physicalCoefficient_smooth χ).contDiffAt.mul (ha.contDiffAt (hU.mem_nhds hx))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun hxS => hx (hχ hxS))] with y hy
    change (χ : E → ℝ) y = 0 at hy
    simp [leftCutoffClassicalSymbol, physicalCoefficient, hy]

theorem leftCutoffClassicalSymbol_degreeZero (χ : D) {U : Set E}
    (hχ : tsupport (χ : E → ℝ) ⊆ U) {a : E → E → ℂ}
    (ha : ∀ x ∈ U, DegreeZero (a x)) (x : E) :
    DegreeZero (leftCutoffClassicalSymbol χ a x) := by
  intro s hs ξ
  by_cases hx : x ∈ U
  · exact congrArg ((physicalCoefficient χ x) * ·) (ha x hx s hs ξ)
  · have hZero : (χ : E → ℝ) x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχ h))
    simp [leftCutoffClassicalSymbol, physicalCoefficient, hZero]

private theorem leftCutoff_exteriorBounds (χ : D) {U : Set E} (hU : IsOpen U)
    (hχ : tsupport (χ : E → ℝ) ⊆ U) {b a : E → E → ℂ}
    (hbDiff : ContDiffOn ℝ ∞ (uncurry b) (U ×ˢ univ))
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (U ×ˢ ({0}ᶜ : Set E)))
    (R : ℝ) (hLarge : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ tsupport (χ : E → ℝ), ∀ ξ : E,
      R ≤ ‖ξ‖ → (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : E, max 1 R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n
        (fun y => leftCutoffClassicalSymbol χ b y ξ - leftCutoffClassicalSymbol χ a y ξ) x‖ ≤ C := by
  classical
  intro n
  let θ : E → ℂ := physicalCoefficient χ
  let S := tsupport (χ : E → ℝ)
  let q := leftCutoffClassicalSymbol χ (fun x ξ => b x ξ - a x ξ)
  have hs : IsCompact S := test_compactSupport χ
  have hθ : ContDiff ℝ ∞ θ := physicalCoefficient_smooth χ
  have hA (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ S, ‖iteratedFDeriv ℝ m θ x‖ ≤ A := by
    have hDer : Continuous (iteratedFDeriv ℝ m θ) := hθ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨A, hA⟩ := (hs.image hDer).isBounded.exists_norm_le
    exact ⟨max 0 A, le_max_left _ _, fun x hx =>
      (hA _ (mem_image_of_mem (iteratedFDeriv ℝ m θ) hx)).trans (le_max_right _ _)⟩
  choose A hA₀ hA' using hA
  choose B hB₀ hB' using hLarge
  let C := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * A k * B (n - k)
  have hC : 0 ≤ C := Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA₀ k)) (hB₀ (n - k))
  refine ⟨C, hC, fun x ξ hξ => ?_⟩
  have hEq : (fun y => leftCutoffClassicalSymbol χ b y ξ - leftCutoffClassicalSymbol χ a y ξ) =
      fun y => q y ξ := by
    funext y
    exact (mul_sub (physicalCoefficient χ y) (b y ξ) (a y ξ)).symm
  rw [hEq]
  by_cases hx : x ∈ S
  · have hxU := hχ hx
    have hξ0 : ξ ∈ ({0}ᶜ : Set E) :=
      norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hξ))
    have hbξ : ContDiffOn ℝ ∞ (fun y => b y ξ) U :=
      hbDiff.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy => ⟨hy, mem_univ _⟩)
    have haξ : ContDiffOn ℝ ∞ (fun y => a y ξ) U :=
      haDiff.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy => ⟨hy, hξ0⟩)
    have hN : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hProd := norm_iteratedFDerivWithin_mul_le hθ.contDiffOn (hbξ.sub haξ) hU.uniqueDiffOn hxU hN
    simp only [iteratedFDerivWithin_of_isOpen _ hU hxU] at hProd
    refine (mul_le_mul_of_nonneg_left hProd (by positivity : 0 ≤ 1 + ‖ξ‖)).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    calc
      _ = (n.choose k : ℝ) * ‖iteratedFDeriv ℝ k θ x‖ *
          ((1 + ‖ξ‖) * ‖iteratedFDeriv ℝ (n - k) (fun y => b y ξ - a y ξ) x‖) := by ring
      _ ≤ (n.choose k : ℝ) * A k * B (n - k) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hA' k x hx) (Nat.cast_nonneg _))
          (hB' (n - k) x hx ξ ((le_max_right _ _).trans hξ)) (by positivity)
          (mul_nonneg (Nat.cast_nonneg _) (hA₀ k))
  · have hZero : iteratedFDeriv ℝ n (fun y => q y ξ) x = 0 := by
      by_contra h
      exact hx (leftCutoffClassicalSymbol_support χ (fun x ξ => b x ξ - a x ξ) ξ
        (support_iteratedFDeriv_subset n h))
    simpa only [hZero, norm_zero, mul_zero] using hC

private theorem symbolCLM_conj_physicalCoefficient (χ : D) (u : ComplexL2 E) :
    symbolCLM (conjugateSymbol (physicalCoefficient χ)) u = symbolCLM (physicalCoefficient χ) u :=
  symbolL2_congr_ae _ _ (Eventually.of_forall fun x => by
    simp [physicalCoefficient, conjugateSymbol_apply]) u

/-- The coordinate-local pairing yields the actual left-localized operator.
Only test functions supported in the open coordinate region enter the input identity. -/
theorem hasLocalClassicalRepresentation_of_leftCutoff_fullSymbolPairing
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (χ : D) (b a : E → E → ℂ)
    (U L : Set E) (hU : IsOpen U) (hL : IsCompact L) (hχ : tsupport (χ : E → ℝ) ⊆ U)
    (hbDiff : ContDiffOn ℝ ∞ (uncurry b) (U ×ˢ univ))
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (U ×ˢ ({0}ᶜ : Set E)))
    (haZero : ContDiffOn ℝ ∞ (fun x => a x 0) U) (hDegree : ∀ x ∈ U, DegreeZero (a x))
    (R : ℝ) (hLarge : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ tsupport (χ : E → ℝ), ∀ ξ : E,
      R ≤ ‖ξ‖ → (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C)
    (hAct : ∀ f v : SchwartzMap E ℂ, tsupport (f : E → ℂ) ⊆ U → tsupport (v : E → ℂ) ⊆ L →
      inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) = classicalLeftPairing b f v) :
    HasLocalClassicalRepresentation ((symbolCLM (physicalCoefficient χ)).comp T)
      (leftCutoffClassicalSymbol χ a) L := by
  let b' := leftCutoffClassicalSymbol χ b
  let a' := leftCutoffClassicalSymbol χ a
  have hb' : ContDiff ℝ ∞ (uncurry b') := by
    have h := leftCutoffClassicalSymbol_smoothOn χ hU isOpen_univ hχ hbDiff
    rw [univ_prod_univ, contDiffOn_univ] at h
    exact h
  refine hasLocalClassicalRepresentation_of_fullSymbolPairing _ b' a' _ L (test_compactSupport χ) hL
    (leftCutoffClassicalSymbol_support χ b) (leftCutoffClassicalSymbol_support χ a) hb'
    (leftCutoffClassicalSymbol_smoothOn χ hU isOpen_compl_singleton hχ haDiff)
    (leftCutoffClassicalSymbol_smoothZero χ hU hχ haZero)
    (leftCutoffClassicalSymbol_degreeZero χ hχ hDegree) (max 1 R)
    (leftCutoff_exteriorBounds χ hU hχ hbDiff haDiff R hLarge) ?_
  intro f v hv
  have hInner : inner ℂ (f.toLp 2 volume) (symbolCLM (physicalCoefficient χ) (T (v.toLp 2 volume))) =
      inner ℂ ((coeffMul χ f).toLp 2 volume) (T (v.toLp 2 volume)) := by
    rw [coeffMul_toLp, inner_symbolCLM_left, symbolCLM_conj_physicalCoefficient χ]
  change inner ℂ (f.toLp 2 volume) (symbolCLM (physicalCoefficient χ) (T (v.toLp 2 volume))) = _
  rw [hInner, hAct _ _ ((coeffMul_tsupport_subset_real χ f).trans hχ) hv]
  unfold classicalLeftPairing
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change conj ((physicalCoefficient χ x) * f x) * _ =
      conj (f x) * Burnett.Analysis.FirstOrderDyadic.firstOrderAction
        (fun y ξ => physicalCoefficient χ y * b y ξ) v x
    rw [firstOrderAction_mul_base]
    simp only [map_mul, physicalCoefficient, Complex.conj_ofReal]
    ring

private theorem coeffMul_eq_self_on_support (χ : D) (f : SchwartzMap E ℂ)
    (hχ : ∀ x ∈ tsupport (f : E → ℂ), (χ : E → ℝ) x = 1) : coeffMul χ f = f := by
  apply SchwartzMap.ext
  intro x
  change (physicalCoefficient χ x) * f x = f x
  by_cases hx : x ∈ tsupport (f : E → ℂ)
  · simp [physicalCoefficient, hχ x hx]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- An exact full symbol given only on the open receiving chart yields the
paper pairing of the original, unmodified operator on the two localized gradients. -/
theorem tendsto_originalVolume_receivingLocalFullPairing
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hPair : HasOriginalReceivingPaperPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart '' K)
    (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart '' K)
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (b a : E → E → ℂ)
    (hbDiff : ContDiffOn ℝ ∞ (uncurry b) (c.chart.target ×ˢ univ))
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (c.chart.target ×ˢ ({0}ᶜ : Set E)))
    (haZero : ContDiffOn ℝ ∞ (fun x => a x 0) c.chart.target)
    (hDegree : ∀ x ∈ c.chart.target, DegreeZero (a x))
    (hLarge : ∀ S : Set E, IsCompact S → S ⊆ c.chart.target → ∃ R : ℝ,
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ : E, R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C)
    (hAct : ∀ f v : SchwartzMap E ℂ, tsupport (f : E → ℂ) ⊆ c.chart.target →
      tsupport (v : E → ℂ) ⊆ tsupport (η₁ : E → ℝ) →
      inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) = classicalLeftPairing b f v)
    (i j : JetSlot) :
    let h₀c := h₀.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let h₁c := h₁.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u := fixedVolumeGradientSchwartz B g hB hg hn c η₀ h₀c
    let v := fixedVolumeGradientSchwartz B g hB hg hn c η₁ h₁c
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let G (p : Cosphere r) :=
      let z := fixedChartPhase c p.val
      conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a z.1 (WithLp.toLp 2 z.2)) *
        atlasOrderedJetEntry c A.density p j i
    Integrable G τ ∧ Tendsto (fun n => inner ℂ (T ((v (σ n) j).toLp 2 volume))
      ((u (σ n) i).toLp 2 volume)) atTop (𝓝 (∫ p, G p ∂τ)) := by
  intro h₀c h₁c u v τ G
  obtain ⟨S, hS, _, hSU, α, hαDiff, hαComp, hαS, _, hαOne⟩ :=
    FlatRigidity.exists_smooth_cutoff_on_compact_chart (test_compactSupport η₀) c.chart.open_target h₀c
  let χ : D := ⟨α, hαDiff, hαComp⟩
  have hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target := hαS.trans hSU
  obtain ⟨R, hR⟩ := hLarge _ (test_compactSupport χ) hχ
  let T' := (symbolCLM (physicalCoefficient χ)).comp T
  let a' := leftCutoffClassicalSymbol χ a
  have hRep : HasLocalClassicalRepresentation T' a' (tsupport (η₁ : E → ℝ)) :=
    hasLocalClassicalRepresentation_of_leftCutoff_fullSymbolPairing T χ b a c.chart.target _
      c.chart.open_target (test_compactSupport η₁) hχ hbDiff haDiff haZero hDegree R hR hAct
  obtain ⟨I, H⟩ := hPair c K hK hKc a' S hS
    (fun ξ => (leftCutoffClassicalSymbol_support χ a ξ).trans hαS)
    (leftCutoffClassicalSymbol_smoothOn χ c.chart.open_target isOpen_compl_singleton hχ haDiff)
    (leftCutoffClassicalSymbol_smoothZero χ c.chart.open_target hχ haZero)
    (leftCutoffClassicalSymbol_degreeZero χ hχ hDegree) η₀ η₁ h₀ h₁ T' hRep i j
  let G' (p : Cosphere r) :=
    let z := fixedChartPhase c p.val
    conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a' z.1 (WithLp.toLp 2 z.2)) *
      atlasOrderedJetEntry c A.density p j i
  change Integrable G' τ at I
  change Tendsto (fun n => inner ℂ (T' ((v (σ n) j).toLp 2 volume))
    ((u (σ n) i).toLp 2 volume)) atTop (𝓝 (∫ p, G' p ∂τ)) at H
  have hG : G' = G := by
    funext p
    let x := (fixedChartPhase c p.val).1
    let ξ := WithLp.toLp 2 (fixedChartPhase c p.val).2
    change conj ((physicalCoefficient η₀ x * physicalCoefficient η₁ x) *
        (physicalCoefficient χ x * a x ξ)) * atlasOrderedJetEntry c A.density p j i =
      conj ((physicalCoefficient η₀ x * physicalCoefficient η₁ x) * a x ξ) *
        atlasOrderedJetEntry c A.density p j i
    by_cases hx : x ∈ tsupport (η₀ : E → ℝ)
    · have hOne : (χ : E → ℝ) x = 1 := hαOne x hx
      simp [physicalCoefficient, hOne]
    · have hZero : (η₀ : E → ℝ) x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [physicalCoefficient, hZero]
  rw [hG] at I H
  refine ⟨I, H.congr fun n => ?_⟩
  have hInside : tsupport (u (σ n) i : E → ℂ) ⊆ tsupport (η₀ : E → ℝ) :=
    fixedVolumeGradientSchwartz_tsupport B g hB hg hn c η₀ h₀c (σ n) i
  change inner ℂ (symbolCLM (physicalCoefficient χ) (T ((v (σ n) j).toLp 2 volume)))
    ((u (σ n) i).toLp 2 volume) = _
  rw [inner_symbolCLM_left, symbolCLM_conj_physicalCoefficient χ, ← coeffMul_toLp,
    coeffMul_eq_self_on_support χ _ (fun x hx => hαOne x (hInside hx))]

end Burnett.Microlocal.Overlap
