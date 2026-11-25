import Burnett.Analysis.Microlocal.Overlap.CompactClassicalQuantization
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartMovedSymbols

/-! The infrared cutoff is the only difference between the two frozen principal quantizations. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 4100000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Function Set Filter Burnett.Fourier
open Burnett.Geometry ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E radialCore_eq_zero)
open Burnett.Microlocal.Overlap
open scoped ContDiff InnerProduct Topology

open private contDiffOn_frequency_apply from Burnett.Analysis.Microlocal.Overlap.ReceivingChartMovedSymbols

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- Pull back a joint symbol using the actual base map and inverse-adjoint frequency map. -/
def receivingJointSymbol (c d : AtlasChart M) (χ : E → ℂ) (p : E → E → ℂ) (x ξ : E) : ℂ :=
  χ x * p (overlapTransition c d x) (receivingFrequency c d x ξ)

private theorem receivingJointSymbol_support (c d : AtlasChart M) (χ : E → ℂ) (p : E → E → ℂ)
    (ξ : E) : tsupport (fun x => receivingJointSymbol c d χ p x ξ) ⊆ tsupport χ :=
  tsupport_mul_subset_left

private theorem contDiffOn_jointSymbol_argument (c d : AtlasChart M) {s : Set (E × E)}
    (hs : MapsTo Prod.fst s (c.transition d).source) :
    ContDiffOn ℝ ∞ (fun z : E × E => (overlapTransition c d z.1, receivingFrequency c d z.1 z.2)) s :=
  (((overlapTransition_contDiffOn c d).comp contDiffOn_fst hs).prodMk
    (contDiffOn_frequency_apply c d hs))

private theorem receivingJointSymbol_contDiffOn (c d : AtlasChart M)
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχS : tsupport χ ⊆ (c.transition d).source)
    (p : E → E → ℂ) (hp : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E))) :
    ContDiffOn ℝ ∞ (uncurry (receivingJointSymbol c d χ p)) (univ ×ˢ ({0}ᶜ : Set E)) := by
  let U := (c.transition d).source
  have hU : IsOpen (U ×ˢ ({0}ᶜ : Set E)) := (c.transition d).open_source.prod isOpen_compl_singleton
  have hMap : MapsTo (fun z : E × E => (overlapTransition c d z.1, receivingFrequency c d z.1 z.2))
      (U ×ˢ ({0}ᶜ : Set E)) (univ ×ˢ ({0}ᶜ : Set E)) := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    change receivingFrequency c d z.1 z.2 ≠ 0
    rw [chartTransitionFrequency_eq_frozen c d hz.1]
    intro h
    exact hz.2 ((frozenChartFrequency c d hz.1).injective (h.trans (map_zero _).symm))
  have hComp := (hχ.comp contDiff_fst).contDiffOn.mul
    (hp.comp (contDiffOn_jointSymbol_argument c d (fun _ hz => hz.1)) hMap)
  intro z hz
  by_cases hx : z.1 ∈ U
  · exact (hComp.contDiffAt (hU.mem_nhds ⟨hx, hz.2⟩)).contDiffWithinAt
  · have hZero : χ =ᶠ[𝓝 z.1] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hχS h))
    apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E × E => (0 : ℂ)) z).congr_of_eventuallyEq
    filter_upwards [hZero.comp_tendsto (continuous_fst.continuousAt :
      ContinuousAt (Prod.fst : E × E → E) z)] with z' hz'
    change χ z'.1 = (0 : ℂ) at hz'
    simp only [uncurry, receivingJointSymbol, hz', zero_mul]

private theorem receivingJointSymbol_contDiff (c d : AtlasChart M)
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχS : tsupport χ ⊆ (c.transition d).source)
    (p : E → E → ℂ) (hp : ContDiff ℝ ∞ (uncurry p)) :
    ContDiff ℝ ∞ (uncurry (receivingJointSymbol c d χ p)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hx : z.1 ∈ (c.transition d).source
  · have hU : IsOpen ((c.transition d).source ×ˢ (univ : Set E)) :=
      (c.transition d).open_source.prod isOpen_univ
    exact ((hχ.comp contDiff_fst).contDiffOn.mul
      (hp.comp_contDiffOn (contDiffOn_jointSymbol_argument c d (fun _ hz => hz.1)))).contDiffAt
        (hU.mem_nhds ⟨hx, mem_univ _⟩)
  · have hZero : χ =ᶠ[𝓝 z.1] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hχS h))
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E × E => (0 : ℂ)) z).congr_of_eventuallyEq
    filter_upwards [hZero.comp_tendsto (continuous_fst.continuousAt :
      ContinuousAt (Prod.fst : E × E → E) z)] with z' hz'
    change χ z'.1 = (0 : ℂ) at hz'
    simp only [uncurry, receivingJointSymbol, hz', zero_mul]

private theorem receivingJointSymbol_zero_smooth (c d : AtlasChart M)
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχS : tsupport χ ⊆ (c.transition d).source)
    (p : E → E → ℂ) (hp : ContDiff ℝ ∞ (fun z => p z 0)) :
    ContDiff ℝ ∞ (fun x => receivingJointSymbol c d χ p x 0) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ (c.transition d).source
  · simp only [receivingJointSymbol, map_zero]
    exact (hχ.contDiffAt).mul ((hp.comp_contDiffOn (overlapTransition_contDiffOn c d)).contDiffAt
      ((c.transition d).open_source.mem_nhds hx))
  · have hZero : χ =ᶠ[𝓝 x] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hχS h))
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℂ)) x).congr_of_eventuallyEq
    filter_upwards [hZero] with x' hx'
    simp only [receivingJointSymbol, hx', zero_mul]

/-- The change of the infrared cutoff contributes a genuine compact error on a
compact input window. The bounded source operator quantizes the frozen symbol. -/
theorem exists_receivingJointPrincipalOperator
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    (p : E → E → ℂ) (hp : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)))
    (hp₀ : ContDiff ℝ ∞ (fun x => p x 0)) (hd : ∀ x, DegreeZero (p x)) :
    ∃ T : ComplexL2 E →L[ℂ] ComplexL2 E,
      (∀ f v : SchwartzMap E ℂ, inner ℂ (v.toLp 2 MeasureTheory.volume)
        (T (f.toLp 2 MeasureTheory.volume)) =
        classicalLeftPairing (receivingJointSymbol c d χ (infraredAngularPrincipal p)) v f) ∧
      HasLocalClassicalRepresentation T (receivingJointSymbol c d χ p) K := by
  let Q := receivingJointSymbol c d χ p
  let P := receivingJointSymbol c d χ (infraredAngularPrincipal p)
  have hQS (ξ : E) : tsupport (fun x => Q x ξ) ⊆ K :=
    (receivingJointSymbol_support c d χ p ξ).trans hχK
  have hPS (ξ : E) : tsupport (fun x => P x ξ) ⊆ K :=
    (receivingJointSymbol_support c d χ (infraredAngularPrincipal p) ξ).trans hχK
  have hP : ContDiff ℝ ∞ (uncurry P) :=
    receivingJointSymbol_contDiff c d χ hχ (hχK.trans hKU) _ (contDiff_uncurry_infraredAngularPrincipal hp)
  have hQ : ContDiffOn ℝ ∞ (uncurry Q) (univ ×ˢ ({0}ᶜ : Set E)) :=
    receivingJointSymbol_contDiffOn c d χ hχ (hχK.trans hKU) p hp
  have hQ₀ : ContDiff ℝ ∞ (fun x => Q x 0) :=
    receivingJointSymbol_zero_smooth c d χ hχ (hχK.trans hKU) p hp₀
  have hDeg (x : E) : DegreeZero (Q x) := by
    intro s hs ξ
    change χ x * p (overlapTransition c d x) (receivingFrequency c d x (s • ξ)) = _
    rw [map_smul, hd _ s hs]
    rfl
  obtain ⟨l, _, hl, _, hNorm⟩ := exists_frozenChartFrequency_norm_bounds c d K hK hKU
  have hHi (ξ : E) (hξ : 2 / l ≤ ‖ξ‖) : (fun x => P x ξ - Q x ξ) = fun _ => 0 := by
    funext x
    by_cases hx : x ∈ K
    · have hF : 2 ≤ ‖receivingFrequency c d x ξ‖ := by
        rw [chartTransitionFrequency_eq_frozen c d (hKU hx)]
        exact ((div_le_iff₀ hl).mp hξ).trans (by rw [mul_comm]; exact (hNorm x hx ξ).1)
      simp [P, Q, receivingJointSymbol, infraredAngularPrincipal, radialCore_eq_zero _ hF]
    · have hχ₀ : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hz => hx (hχK hz))
      simp [P, Q, receivingJointSymbol, hχ₀]
  obtain ⟨T, hAct, hRep⟩ := exists_classicalFullSymbolOperator P Q K hK hPS hQS hP hQ hQ₀ hDeg
    (2 / l) (by
      intro n
      exact ⟨0, le_rfl, fun x ξ hξ => by simp [hHi ξ hξ]⟩)
  exact ⟨T, fun f v => hAct v f, hRep K hK⟩

end Burnett.Microlocal.AtlasOverlapKernel
