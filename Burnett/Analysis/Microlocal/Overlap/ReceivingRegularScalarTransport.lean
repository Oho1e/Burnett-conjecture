import Burnett.Analysis.Microlocal.Overlap.ReceivingJointClassicalTransport
import Burnett.Analysis.Microlocal.Overlap.JointClassicalBilateralMixing
import Burnett.Analysis.Microlocal.Overlap.JointClassicalBilateralToLocal

/-! Keep the cutoff principal and its regularity in an actual chart transport. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 6000000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Function MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.BesselLocalization (coeffMul coeffMul_toLp physicalCoefficient)
open Burnett.Microlocal.SeparablePositive (inner_symbolCLM_left)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff InnerProduct Topology

open private receivingJointSymbol_support receivingJointSymbol_contDiffOn receivingJointSymbol_zero_smooth
  from Burnett.Analysis.Microlocal.Overlap.JointAngularMovingPrincipal
open private tsupport_physicalCoefficient_subset from Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical
open private symbolCLM_conj_physicalCoefficient from Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol
open private coeffMul_eq_of_one_on from Burnett.Analysis.Microlocal.Overlap.ReceivingSquareLocalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The same cutoff representative has compact base support, punctured and zero
smoothness, and all the bounds needed for bilateral principal mixing. -/
theorem receivingJointSymbol_regular_of_compactSupport
    (c d : AtlasChart M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (c.transition d).source) (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : tsupport χ ⊆ K) (a : E → E → ℂ)
    (ha : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (ha₀ : ContDiff ℝ ∞ (fun x => a x 0)) (hAd : ∀ x, DegreeZero (a x)) :
    let p := receivingJointSymbol c d χ a
    (∀ ξ, tsupport (fun x => p x ξ) ⊆ K) ∧
      ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)) ∧
      ContDiff ℝ ∞ (fun x => p x 0) ∧ HasAngularPrincipalRegularity p := by
  intro p
  have hpS (ξ : E) : tsupport (fun x => p x ξ) ⊆ K :=
    (receivingJointSymbol_support c d χ a ξ).trans hχK
  have hp : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)) :=
    receivingJointSymbol_contDiffOn c d χ hχ (hχK.trans hKU) a ha
  have hp₀ : ContDiff ℝ ∞ (fun x => p x 0) :=
    receivingJointSymbol_zero_smooth c d χ hχ (hχK.trans hKU) a ha₀
  have hpD (x : E) : DegreeZero (p x) := by
    intro s hs ξ
    change χ x * a (overlapTransition c d x) (receivingFrequency c d x (s • ξ)) = _
    rw [map_smul, hAd _ s hs]
    rfl
  obtain ⟨C, _, hC⟩ := exists_uniform_baseDerivative_of_homogeneousAngular p K hK hpS hp hp₀ hpD 0
  refine ⟨hpS, hp, hp₀, ⟨⟨C, fun x ξ => ?_⟩, (contDiff_uncurry_infraredAngularPrincipal hp).continuous,
    fun ξ _ => (contDiff_baseAngularSection p hp hp₀ ξ).continuous, fun x ξ hξ => ?_, hpD⟩⟩
  · simpa only [norm_iteratedFDeriv_zero] using hC x ξ
  · have h := hp.comp (contDiffOn_const.prodMk contDiffOn_id : ContDiffOn ℝ ∞
        (fun η : E => (x, η)) ({0}ᶜ : Set E)) (fun _ hy => ⟨mem_univ _, hy⟩)
    exact h.continuousOn.continuousAt
      (isOpen_compl_singleton.mem_nhds (mem_compl_singleton_iff.mpr hξ))

/-- An exact half-density transport with the actual cutoff principal retained.
Left localization on a larger certified window identifies this representative
globally and preserves the actual pairing on both inputs in the inner window. -/
theorem exists_receivingJointClassicalOperator_of_representation_with_regular_principal
    (c d : AtlasChart M) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hLK : L ⊆ interior K) (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (haS : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (ha : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (ha₀ : ContDiff ℝ ∞ (fun x => a x 0)) (hAd : ∀ x, DegreeZero (a x))
    (A : ComplexL2 E →L[ℂ] ComplexL2 E)
    (hA : HasLocalClassicalRepresentation A a (c.transition d '' K)) :
    ∃ (η : D) (T : ComplexL2 E →L[ℂ] ComplexL2 E),
      tsupport (η : E → ℝ) ⊆ K ∧ (∀ x ∈ L, (η : E → ℝ) x = 1) ∧
      let p := receivingJointSymbol c d (physicalCoefficient η) a
      (∀ x (hx : x ∈ L) ξ,
        p x ξ = a (c.transition d x) (frozenChartFrequency c d (hKU (interior_subset (hLK hx))) ξ)) ∧
      HasAngularPrincipalRegularity p ∧ HasLocalClassicalRepresentation T p L ∧
      ∀ (f v : SchwartzMap E ℂ) (hf : tsupport (f : E → ℂ) ⊆ L) (hv : tsupport (v : E → ℂ) ⊆ L),
        let hLK' := hLK.trans interior_subset
        let F := transportedHalfDensitySchwartz c d K hK hKU f (hf.trans hLK')
        let V := transportedHalfDensitySchwartz c d K hK hKU v (hv.trans hLK')
        inner ℂ (V.toLp 2 volume) (A (F.toLp 2 volume)) =
          inner ℂ (v.toLp 2 volume) (T (f.toLp 2 volume)) := by
  obtain ⟨C, hC, hBounds⟩ := exists_uniform_baseDerivative_of_homogeneousAngular a S hS haS ha ha₀ hAd 0
  have hSmooth (x : E) : ContDiffOn ℝ ∞ (a x) ({0}ᶜ : Set E) :=
    ha.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => ⟨mem_univ _, hz⟩)
  let a' (x : E) : BoundedSymbol E :=
    { toFun := a x
      measurable := (measurable_of_continuousOn_compl_singleton 0 (hSmooth x).continuousOn).aestronglyMeasurable
      bound := C
      bound_nonneg := hC
      norm_le := fun ξ => by simpa only [norm_iteratedFDeriv_zero] using hBounds x ξ }
  obtain ⟨J, hJ, hLJ, hJK, α, hα, hαC, hαS, _, hαL⟩ :=
    Burnett.Geometry.FlatRigidity.exists_smooth_cutoff_on_compact_chart hL isOpen_interior hLK
  let η : D := ⟨α, hα, hαC⟩
  let χ := physicalCoefficient η
  have hLJ' : L ⊆ J := hLJ.trans interior_subset
  have hηK : tsupport (η : E → ℝ) ⊆ K := hαS.trans (hJK.trans interior_subset)
  have hχJ : tsupport (χ : E → ℂ) ⊆ J := (tsupport_physicalCoefficient_subset η).trans hαS
  have hχK : tsupport (χ : E → ℂ) ⊆ K := hχJ.trans (hJK.trans interior_subset)
  have hχD : ContDiff ℝ ∞ (χ : E → ℂ) := Complex.ofRealCLM.contDiff.comp hα
  let p := receivingJointSymbol c d χ a
  obtain ⟨p₀, T₀, hSymbol, hRep, hPair⟩ :=
    exists_receivingJointClassicalOperator_of_representation c d K J hK hJ hJK hKU hConv a'
      S hS haS ha ha₀ hAd A hA
  obtain ⟨R, hR, hAct⟩ := hRep
  let T := (symbolCLM χ).comp T₀
  have hRep₁ := hasLocalClassicalRepresentation_leftCutoff_of_bilateral T₀ R hR p₀ J L η hαS
    (fun f v _ hv => hAct f v (hv.trans hLJ'))
  have hEq : (fun x ξ => χ x * p₀ x ξ) = p := by
    funext x ξ
    change χ x * p₀ x ξ = χ x * a (overlapTransition c d x) (receivingFrequency c d x ξ)
    by_cases hx : x ∈ J
    · rw [hSymbol x hx ξ]
    · have hχ₀ := image_eq_zero_of_notMem_tsupport (fun hz => hx (hχJ hz))
      rw [hχ₀, zero_mul, zero_mul]
  have hRep₂ : HasLocalClassicalRepresentation T p L := hEq ▸ hRep₁
  have hReg := (receivingJointSymbol_regular_of_compactSupport c d K hK hKU χ hχD hχK a ha ha₀ hAd).2.2.2
  refine ⟨η, T, hηK, hαL, fun x hx ξ => ?_, hReg, hRep₂, fun f v hf hv => ?_⟩
  · let hxU := hKU (interior_subset (hLK hx))
    have hOne : χ x = 1 := by
      change (α x : ℂ) = 1
      rw [hαL x hx, Complex.ofReal_one]
    change χ x * a (overlapTransition c d x) (receivingFrequency c d x ξ) = _
    rw [hOne, one_mul, overlapTransition_eq c d hxU, chartTransitionFrequency_eq_frozen c d hxU]
  · intro _ F V
    refine (hPair f v (hf.trans hLJ') (hv.trans hLJ')).trans ?_
    change inner ℂ (v.toLp 2 volume) (T₀ (f.toLp 2 volume)) =
      inner ℂ (v.toLp 2 volume) (symbolCLM χ (T₀ (f.toLp 2 volume)))
    have h := inner_symbolCLM_left χ (v.toLp 2 volume) (T₀ (f.toLp 2 volume))
    rw [symbolCLM_conj_physicalCoefficient, ← coeffMul_toLp,
      coeffMul_eq_of_one_on η hαL v hv] at h
    exact h

end Burnett.Microlocal.AtlasOverlapKernel
