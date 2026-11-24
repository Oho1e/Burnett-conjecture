import Burnett.Analysis.Microlocal.Overlap.ReceivingJointClassicalTransport
import Burnett.Analysis.Microlocal.Overlap.LocalClassicalPuncturedPrincipal

/-! An actual compactly based classical full symbol transforms with its joint principal symbol. -/
set_option autoImplicit false
set_option maxRecDepth 4700
set_option maxHeartbeats 4000000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Function Set MeasureTheory Burnett.Fourier
open Burnett.Geometry ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul coeffMul_toLp)
open Burnett.Microlocal.SeparablePositive (inner_symbolCLM_left)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped ContDiff InnerProduct Topology

open private angularPrincipalZeroExtension from Burnett.Analysis.Microlocal.Overlap.LocalClassicalPuncturedPrincipal
open private symbolCLM_conj_physicalCoefficient coeffMul_eq_self_on_support
  from Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

private theorem exists_receivingJointClassicalOperator_of_compactPrincipal
    (c d : AtlasChart M) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hLK : L ⊆ interior K) (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (haS : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (ha : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (ha₀ : ContDiff ℝ ∞ (fun x => a x 0)) (hAd : ∀ x, DegreeZero (a x))
    (A : ComplexL2 E →L[ℂ] ComplexL2 E)
    (hA : HasLocalClassicalRepresentation A a (c.transition d '' K)) :
    ∃ p : E → E → ℂ, ∃ T : ComplexL2 E →L[ℂ] ComplexL2 E,
      (∀ x ∈ L, ∀ ξ, p x ξ = a (overlapTransition c d x) (receivingFrequency c d x ξ)) ∧
      HasLocalClassicalRepresentation T p L ∧
      ∀ f v : SchwartzMap E ℂ,
        ∀ (hf : tsupport (f : E → ℂ) ⊆ L) (hv : tsupport (v : E → ℂ) ⊆ L),
          let hLK' := hLK.trans interior_subset
          let F := transportedHalfDensitySchwartz c d K hK hKU f (hf.trans hLK')
          let V := transportedHalfDensitySchwartz c d K hK hKU v (hv.trans hLK')
          inner ℂ (V.toLp 2 volume) (A (F.toLp 2 volume)) =
            inner ℂ (v.toLp 2 volume) (T (f.toLp 2 volume)) := by
  obtain ⟨B, hB, hBounds⟩ := exists_uniform_baseDerivative_of_homogeneousAngular a S hS haS ha ha₀ hAd 0
  have hSmooth (x : E) : ContDiffOn ℝ ∞ (a x) ({0}ᶜ : Set E) :=
    ha.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => ⟨mem_univ _, hz⟩)
  let a' (x : E) : BoundedSymbol E :=
    { toFun := a x
      measurable := (measurable_of_continuousOn_compl_singleton 0 (hSmooth x).continuousOn).aestronglyMeasurable
      bound := B
      bound_nonneg := hB
      norm_le := fun ξ => by simpa only [norm_iteratedFDeriv_zero] using hBounds x ξ }
  exact exists_receivingJointClassicalOperator_of_representation c d K L hK hL hLK hKU hConv
    a' S hS haS ha ha₀ hAd A hA

/-- This uses the same actual operator with the given classical full symbol.
Its natural principal symbol on the overlap depends jointly on the
receiving position and inverse-adjoint frequency. -/
theorem exists_receivingJointClassicalOperator_of_fullSymbolPairing
    (c d : AtlasChart M) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hLK : L ⊆ interior K) (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (b a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hbS : ∀ ξ, tsupport (fun x => b x ξ) ⊆ S) (haS : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hb : ContDiff ℝ ∞ (uncurry b))
    (ha : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (ha₀ : ContDiff ℝ ∞ (fun x => a x 0)) (hAd : ∀ x, DegreeZero (a x))
    (R : ℝ) (hLarge : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ : E, R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C)
    (A : ComplexL2 E →L[ℂ] ComplexL2 E)
    (hA : ∀ f v : SchwartzMap E ℂ, tsupport (v : E → ℂ) ⊆ c.transition d '' K →
      inner ℂ (f.toLp 2 volume) (A (v.toLp 2 volume)) = classicalLeftPairing b f v) :
    ∃ p : E → E → ℂ, ∃ T : ComplexL2 E →L[ℂ] ComplexL2 E,
      (∀ x ∈ L, ∀ ξ, p x ξ = a (overlapTransition c d x) (receivingFrequency c d x ξ)) ∧
      HasLocalClassicalRepresentation T p L ∧
      ∀ f v : SchwartzMap E ℂ,
        ∀ (hf : tsupport (f : E → ℂ) ⊆ L) (hv : tsupport (v : E → ℂ) ⊆ L),
          let hLK' := hLK.trans interior_subset
          let F := transportedHalfDensitySchwartz c d K hK hKU f (hf.trans hLK')
          let V := transportedHalfDensitySchwartz c d K hK hKU v (hv.trans hLK')
          inner ℂ (V.toLp 2 volume) (A (F.toLp 2 volume)) =
            inner ℂ (v.toLp 2 volume) (T (f.toLp 2 volume)) := by
  have hKS : IsCompact (c.transition d '' K) :=
    hK.image_of_continuousOn ((c.transition d).continuousOn.mono hKU)
  have hRep : HasLocalClassicalRepresentation A a (c.transition d '' K) :=
    hasLocalClassicalRepresentation_of_fullSymbolPairing A b a S (c.transition d '' K) hS hKS
      hbS haS hb ha ha₀ hAd R hLarge hA
  exact exists_receivingJointClassicalOperator_of_compactPrincipal c d K L hK hL hLK hKU hConv
    a S hS haS ha ha₀ hAd A hRep

/-- The overlap theorem assumes only the actual classical symbol near the
target window. A left cutoff is inserted inside that open set. The
principal data and its smoothness are required only away from frequency zero. -/
theorem exists_receivingJointClassicalOperator_of_targetLocalSymbol
    (c d : AtlasChart M) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hLK : L ⊆ interior K) (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (U : Set E) (hU : IsOpen U) (hKU' : c.transition d '' K ⊆ U)
    (b a : E → E → ℂ) (hb : ContDiffOn ℝ ∞ (uncurry b) (U ×ˢ univ))
    (ha : ContDiffOn ℝ ∞ (uncurry a) (U ×ˢ ({0}ᶜ : Set E)))
    (hAd : ∀ x ∈ U, ∀ s : ℝ, 0 < s → ∀ ξ : E, ξ ≠ 0 → a x (s • ξ) = a x ξ)
    (hLarge : ∀ S : Set E, IsCompact S → S ⊆ U → ∃ R : ℝ,
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ : E, R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ n (fun y => b y ξ - a y ξ) x‖ ≤ C)
    (A : ComplexL2 E →L[ℂ] ComplexL2 E)
    (hA : ∀ f v : SchwartzMap E ℂ, tsupport (f : E → ℂ) ⊆ U →
      tsupport (v : E → ℂ) ⊆ c.transition d '' K →
      inner ℂ (f.toLp 2 volume) (A (v.toLp 2 volume)) = classicalLeftPairing b f v) :
    ∃ p : E → E → ℂ, ∃ T : ComplexL2 E →L[ℂ] ComplexL2 E,
      (∀ x ∈ L, ∀ ξ, ξ ≠ 0 → p x ξ = a (overlapTransition c d x) (receivingFrequency c d x ξ)) ∧
      HasLocalClassicalRepresentation T p L ∧
      ∀ f v : SchwartzMap E ℂ,
        ∀ (hf : tsupport (f : E → ℂ) ⊆ L) (hv : tsupport (v : E → ℂ) ⊆ L),
          let hLK' := hLK.trans interior_subset
          let F := transportedHalfDensitySchwartz c d K hK hKU f (hf.trans hLK')
          let V := transportedHalfDensitySchwartz c d K hK hKU v (hv.trans hLK')
          inner ℂ (V.toLp 2 volume) (A (F.toLp 2 volume)) =
            inner ℂ (v.toLp 2 volume) (T (f.toLp 2 volume)) := by
  let a₀ := angularPrincipalZeroExtension a
  have ha₀ (x : E) (ξ : E) (hξ : ξ ≠ 0) : a₀ x ξ = a x ξ := by
    simp [a₀, angularPrincipalZeroExtension, hξ]
  have hDiff : ContDiffOn ℝ ∞ (uncurry a₀) (U ×ˢ ({0}ᶜ : Set E)) :=
    ha.congr fun z hz => ha₀ z.1 z.2 hz.2
  have hZero : ContDiffOn ℝ ∞ (fun x => a₀ x 0) U := by
    simpa only [a₀, angularPrincipalZeroExtension, if_pos rfl] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℂ)) U)
  have hD (x : E) (hx : x ∈ U) : DegreeZero (a₀ x) := by
    intro s hs ξ
    by_cases hξ : ξ = 0
    · rw [hξ, smul_zero]
    · rw [ha₀ _ _ (smul_ne_zero hs.ne' hξ), ha₀ _ _ hξ]
      exact hAd x hx s hs ξ hξ
  let hLK' := hLK.trans interior_subset
  let W := c.transition d '' K
  have hW : IsCompact W := hK.image_of_continuousOn ((c.transition d).continuousOn.mono hKU)
  obtain ⟨J, _, _, hJU, α, hα, hαC, hαS, _, hαW⟩ :=
    Burnett.Geometry.FlatRigidity.exists_smooth_cutoff_on_compact_chart hW hU hKU'
  let χ : D := ⟨α, hα, hαC⟩
  have hχU : tsupport (χ : E → ℝ) ⊆ U := hαS.trans hJU
  obtain ⟨R, hR⟩ := hLarge _ (test_compactSupport χ) hχU
  let A' := (symbolCLM (physicalCoefficient χ)).comp A
  let a' := leftCutoffClassicalSymbol χ a₀
  have hRep : HasLocalClassicalRepresentation A' a' W :=
    hasLocalClassicalRepresentation_of_leftCutoff_fullSymbolPairing A χ b a₀ U W hU hW
      hχU hb hDiff hZero hD (max 1 R) (by
        intro n
        obtain ⟨C, hC, hBound⟩ := hR n
        refine ⟨C, hC, fun x hx ξ hξ => ?_⟩
        have hξ₀ : ξ ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le ((le_max_left _ _).trans hξ))
        simpa only [ha₀ _ _ hξ₀] using hBound x hx ξ ((le_max_right _ _).trans hξ)) hA
  obtain ⟨p, T, hp, hT, hPair⟩ := exists_receivingJointClassicalOperator_of_compactPrincipal
    c d K L hK hL hLK hKU hConv a' _ (test_compactSupport χ)
    (leftCutoffClassicalSymbol_support χ a₀)
    (leftCutoffClassicalSymbol_smoothOn χ hU isOpen_compl_singleton hχU hDiff)
    (leftCutoffClassicalSymbol_smoothZero χ hU hχU hZero)
    (leftCutoffClassicalSymbol_degreeZero χ hχU hD) A' hRep
  refine ⟨p, T, fun x hx ξ hξ => ?_, hT, fun f v hf hv => ?_⟩
  · have hxK := hLK' hx
    have hE : overlapTransition c d x ∈ W := by
      rw [overlapTransition_eq c d (hKU hxK)]
      exact mem_image_of_mem _ hxK
    have hχ : physicalCoefficient χ (overlapTransition c d x) = 1 := by
      change (α (overlapTransition c d x) : ℂ) = 1
      rw [hαW _ hE, Complex.ofReal_one]
    have hη : receivingFrequency c d x ξ ≠ 0 := by
      rw [chartTransitionFrequency_eq_frozen c d (hKU hxK)]
      intro hh
      exact hξ ((frozenChartFrequency c d (hKU hxK)).injective (hh.trans (map_zero _).symm))
    simpa only [a', leftCutoffClassicalSymbol, hχ, one_mul, ha₀ _ _ hη] using hp x hx ξ
  intro _ F V
  have hV : tsupport (V : E → ℂ) ⊆ W :=
    (transportedHalfDensity_smooth_compact_support c d K hK hKU v (hv.trans hLK')).2.2
  have hEqual : inner ℂ (V.toLp 2 volume) (A' (F.toLp 2 volume)) =
      inner ℂ (V.toLp 2 volume) (A (F.toLp 2 volume)) := by
    have h := inner_symbolCLM_left (physicalCoefficient χ) (V.toLp 2 volume) (A (F.toLp 2 volume))
    rw [symbolCLM_conj_physicalCoefficient, ← coeffMul_toLp,
      coeffMul_eq_self_on_support χ V (fun x hx => hαW x (hV hx))] at h
    exact h.symm
  exact hEqual.symm.trans (hPair f v hf hv)

end Burnett.Microlocal.AtlasOverlapKernel
