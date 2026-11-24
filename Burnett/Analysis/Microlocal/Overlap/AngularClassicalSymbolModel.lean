import Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical
import Burnett.Analysis.Microlocal.Overlap.AngularOrderMinusOneQuantization

/-! A concrete full symbol decomposition produces the exact local classical representation. -/

set_option autoImplicit false
set_option maxRecDepth 2800
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularDyadicKernel (E)
open scoped ComplexConjugate ContDiff InnerProduct Topology

theorem hasLocalClassicalRepresentation_of_actualFullSymbol
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (a rem : E → E → ℂ)
    (S L : Set E) (hS : IsCompact S) (hL : IsCompact L)
    (hSupp : ∀ ξ, tsupport (fun x => rem x ξ) ⊆ S)
    (hSmooth : ContDiff ℝ ∞ (uncurry rem)) (hDecay : OrderMinusOneBounds rem)
    (hAct : ∀ f v : SchwartzMap E ℂ, tsupport (v : E → ℂ) ⊆ L →
      inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) =
        (∫ x, conj (f x) * firstOrderAction (infraredAngularPrincipal a) v x) +
          ∫ x, conj (f x) * firstOrderAction rem v x) :
    HasLocalClassicalRepresentation T a L := by
  obtain ⟨R, hR, hr⟩ := compact_orderMinusOne_leftAction_model rem S L hS hL hSupp hSmooth hDecay
  refine ⟨R, hR, fun f v hv => ?_⟩
  rw [hAct f v hv, hr f v hv]

end Burnett.Microlocal.Overlap
