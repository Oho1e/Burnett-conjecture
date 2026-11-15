import Burnett.Algebra.MinkowskiNormalize
import Burnett.Algebra.LorentzPhysical

noncomputable section

namespace Burnett.RicciSymbol.NullFrame

open TensorFrame

/-- From an actual Lorentz frame and a nonzero null covector, construct a
frame that sends that covector to the canonical null direction. The existence
statement does not posit a normalized frame as a new mathematical input. -/
theorem exists_normalized_frame (gInv : Tensor2) (base : LorentzFrame gInv)
    (ξ : Covector) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0) :
    ∃ frame : LorentzFrame gInv,
      covector frame.components ξ = NullScreen.nullCovector := by
  obtain ⟨rotation, hrotation⟩ := MinkowskiNormalize.exists_normalizing_frame
    (covector base.components ξ)
    (LorentzPhysical.transformed_covector_ne_zero gInv base ξ hξ)
    (by rw [LorentzPhysical.transformed_symbolNorm gInv base ξ, hs])
  refine ⟨FrameComposition.composeFrames gInv base rotation, ?_⟩
  rw [FrameComposition.covector_composeFrames, hrotation]

/-- A pointwise chosen normalized frame. No smoothness or uniform parameter
bounds are asserted for this choice. -/
def normalizedFrame (gInv : Tensor2) (base : LorentzFrame gInv)
    (ξ : Covector) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0) : LorentzFrame gInv :=
  Classical.choose (exists_normalized_frame gInv base ξ hξ hs)

theorem normalizedFrame_frequency (gInv : Tensor2) (base : LorentzFrame gInv)
    (ξ : Covector) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0) :
    covector (normalizedFrame gInv base ξ hξ hs).components ξ = NullScreen.nullCovector :=
  Classical.choose_spec (exists_normalized_frame gInv base ξ hξ hs)

end Burnett.RicciSymbol.NullFrame
