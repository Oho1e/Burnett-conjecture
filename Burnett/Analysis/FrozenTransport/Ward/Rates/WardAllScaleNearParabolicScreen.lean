import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearParabolicSmooth
import Burnett.Analysis.FrozenTransport.Ward.WardActualThinSpectrum

set_option autoImplicit false
set_option maxRecDepth 6600
set_option maxHeartbeats 6300000

noncomputable section

namespace Burnett.C02

open Set Burnett.Analysis.ProjectiveNullCaps Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix

def wardParabolicNormalizedFrequency (p : WardParabolicTestPoint) : E :=
  p.2.1 (parabolicDilation p.2.2.1 p.2.2.2)

def wardParabolicScreenDomain (V : Set E) : Set WardParabolicTestPoint :=
  {p | p.1 ∈ V ∧ wardParabolicNormalizedFrequency p ≠ 0}

/-- A smooth parabolic extension of the actual thin screen with its
common fixed-wide screen still evaluated at the original covector. -/
def wardParabolicThinScreenEntry (W : E → E → OrderedPair → OrderedPair → ℝ)
    (tube inner outer : ℝ) (k j : OrderedPair) (p : WardParabolicTestPoint) : ℝ :=
  parabolicConeFactor p.2.1 tube p.2.2.1 inner outer p.2.2.2 *
    W p.1 (wardParabolicNormalizedFrequency p) k j

theorem wardParabolicThinScreenEntry_contDiffOn (V : Set E)
    (W : E → E → OrderedPair → OrderedPair → ℝ)
    (hW : ∀ k j, ContDiffOn ℝ ∞ (fun p : Joint => W p.1 p.2 k j) (V ×ˢ {u : E | u ≠ 0}))
    (tube inner outer : ℝ) (hTube : tube ≠ 0) (k j : OrderedPair) :
    ContDiffOn ℝ ∞ (wardParabolicThinScreenEntry W tube inner outer k j) (wardParabolicScreenDomain V) := by
  let O := wardParabolicScreenDomain V
  let F (p : WardParabolicTestPoint) := p.2.1
  let δ (p : WardParabolicTestPoint) := p.2.2.1
  let u (p : WardParabolicTestPoint) := p.2.2.2
  have hF : ContDiffOn ℝ ∞ F O := (contDiff_fst.comp contDiff_snd).contDiffOn
  have hδ : ContDiffOn ℝ ∞ δ O := (contDiff_fst.comp (contDiff_snd.comp contDiff_snd)).contDiffOn
  have hu : ContDiffOn ℝ ∞ u O := (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)).contDiffOn
  have hFreq : ContDiffOn ℝ ∞ wardParabolicNormalizedFrequency O :=
    hF.clm_apply (parabolicDilation_contDiffOn hδ hu)
  have hMap : MapsTo (fun p : WardParabolicTestPoint => (p.1,wardParabolicNormalizedFrequency p))
      O (V ×ˢ {u : E | u ≠ 0}) := fun _ hp => hp
  have hProj : ContDiffOn ℝ ∞ (fun p : WardParabolicTestPoint => W p.1 (wardParabolicNormalizedFrequency p) k j) O :=
    (hW k j).comp (contDiffOn_fst.prodMk hFreq) hMap
  have hRatio : ContDiffOn ℝ ∞ (fun p : WardParabolicTestPoint => parabolicConeRatio (F p) tube (δ p) (u p)) O :=
    parabolicConeRatio_contDiffOn hF contDiffOn_const hδ hu (fun _ hp => ⟨hTube,hp.2⟩)
  exact ((descendingProfile_contDiff (inner^2) (outer^2)).comp_contDiffOn (hRatio.pow 2)).mul hProj

/-- On the true chart with nonzero width this extension is the exact
actual thin screen coefficient. No additional screen acts on the field. -/
theorem wardParabolicThinScreenEntry_eq_actual (m : Tensor2) (w : E) (F : NullCapChart m w)
    (W : E → E → OrderedPair → OrderedPair → ℝ) (x : E) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m)
    (hWide : ∀ ξ, ∀ k j, W x ξ k j = (wideScreenAngular wi wo m hm).matrix ξ k j)
    (tube δ inner outer : ℝ) (hδ : δ ≠ 0) (hη : 0 < tube * δ^2)
    (u : NullFrequencyCoordinates) (k j : OrderedPair) :
    wardParabolicThinScreenEntry W tube inner outer k j (x,F.toFrequency.toContinuousLinearMap,δ,u) =
      (thinScreenAngular m wi wo hm hη inner outer).matrix (F.toFrequency (parabolicDilation δ u)) k j := by
  simp only [wardParabolicThinScreenEntry, wardParabolicNormalizedFrequency, hWide,
    thinScreenAngular, Matrix.smul_apply, smul_eq_mul]
  rw [thinConeProfile_parabolic F tube hδ]
  rfl

end Burnett.C02
