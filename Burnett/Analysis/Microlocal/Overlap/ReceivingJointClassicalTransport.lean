import Burnett.Analysis.Microlocal.Overlap.JointAngularTransportedOperator
import Burnett.Analysis.Microlocal.Overlap.ReceivingHalfDensityOperator
import Burnett.Analysis.Microlocal.Overlap.ReceivingSquareLocalization

/-! Transport of an actual classical operator including its compact residual. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 4100000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Set MeasureTheory Function Burnett.Fourier
open Burnett.Geometry ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.BesselLocalization (coeffMul physicalCoefficient)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff InnerProduct Topology

open private coeffMul_eq_of_one_on from Burnett.Analysis.Microlocal.Overlap.ReceivingSquareLocalization
open private tsupport_physicalCoefficient_subset from Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- On a common compact overlap, the genuine target operator has an exact
half-density pairing in the source chart and the naturally transported
joint principal symbol. The given compact residual is transported by a
bounded operator and its adjoint. -/
theorem exists_receivingJointClassicalOperator_of_representation
    (c d : AtlasChart M) (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hLK : L ⊆ interior K) (hKU : K ⊆ (c.transition d).source) (hConv : Convex ℝ K)
    (a : E → BoundedSymbol E) (S : Set E) (hS : IsCompact S)
    (hAs : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (ha : ContDiffOn ℝ ∞ (fun z : E × E => a z.1 z.2) (univ ×ˢ ({0}ᶜ : Set E)))
    (hAz : ContDiff ℝ ∞ (fun x => a x 0)) (hAd : ∀ x, DegreeZero (a x : E → ℂ))
    (A : ComplexL2 E →L[ℂ] ComplexL2 E)
    (hA : HasLocalClassicalRepresentation A (fun x ξ => a x ξ) (c.transition d '' K)) :
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
  obtain ⟨J, _, _, hJK, α, hα, hαC, hαS, _, hαL⟩ :=
    Burnett.Geometry.FlatRigidity.exists_smooth_cutoff_on_compact_chart hL isOpen_interior hLK
  let η : D := ⟨α, hα, hαC⟩
  let χ := physicalCoefficient η
  have hηK : tsupport (η : E → ℝ) ⊆ K := hαS.trans (hJK.trans interior_subset)
  have hχS : tsupport (χ : E → ℂ) ⊆ K := (tsupport_physicalCoefficient_subset η).trans hηK
  have hχD : ContDiff ℝ ∞ (χ : E → ℂ) := Complex.ofRealCLM.contDiff.comp hα
  have hχL (x : E) (hx : x ∈ L) : χ x = 1 := by
    change (α x : ℂ) = 1
    rw [hαL x hx, Complex.ofReal_one]
  let hLK' := hLK.trans interior_subset
  obtain ⟨B, T₀, hB, hRep, hPair⟩ := exists_classical_transportedJointAngularOperator
    c d K L hK hKU hConv hLK' χ hχD hχS hχL a S hS hAs ha hAz hAd
  obtain ⟨U, hU⟩ := exists_receivingHalfDensityOperator c d K hK hKU η hηK
  obtain ⟨R, hR, hRA⟩ := hA
  let Q := U.adjoint.comp (R.comp U)
  have hQ : IsCompactOperator Q := (hR.comp_clm U).clm_comp U.adjoint
  let p := receivingJointSymbol c d χ (fun x ξ => a x ξ)
  have hRep' := hasLocalClassicalRepresentation_add_compact T₀ Q p K hRep hQ
  refine ⟨p, T₀ + Q, fun x hx ξ => ?_, ?_, fun f v hf hv => ?_⟩
  · simp only [p, receivingJointSymbol, hχL x hx, one_mul]
  · obtain ⟨V, hV, h⟩ := hRep'
    exact ⟨V, hV, fun f v hv => h f v (hv.trans hLK')⟩
  intro _ F V
  have hUinput (g : SchwartzMap E ℂ) (hg : tsupport (g : E → ℂ) ⊆ L) :
      U (g.toLp 2 volume) = (transportedHalfDensitySchwartz c d K hK hKU g (hg.trans hLK')).toLp 2 volume := by
    rw [hU]
    apply congrArg (fun q : SchwartzMap E ℂ => q.toLp 2 volume)
    ext x
    change transportedHalfDensity c d K (coeffMul η g) x = transportedHalfDensity c d K g x
    rw [coeffMul_eq_of_one_on η hαL g hg]
  have hFS : tsupport (F : E → ℂ) ⊆ c.transition d '' K :=
    (transportedHalfDensity_smooth_compact_support c d K hK hKU f (hf.trans hLK')).2.2
  calc
    _ = inner ℂ (V.toLp 2 volume) (B (F.toLp 2 volume)) +
        inner ℂ (V.toLp 2 volume) (R (F.toLp 2 volume)) := by
      rw [hRA V F hFS, hB F V, classicalLeftPairing]
    _ = inner ℂ (v.toLp 2 volume) (T₀ (f.toLp 2 volume)) +
        inner ℂ (v.toLp 2 volume) (Q (f.toLp 2 volume)) := by
      rw [hPair f v (hf.trans hLK') hv]
      simp only [Q, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        hUinput f hf, hUinput v hv, F, V]
    _ = _ := by rw [ContinuousLinearMap.add_apply, inner_add_right]

end Burnett.Microlocal.AtlasOverlapKernel
