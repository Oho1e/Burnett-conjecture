import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearLowNormalizedKernel
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearParabolicScreen
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearParabolicMasks
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearVertexSmooth

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 14500000

noncomputable section

namespace Burnett.C02

open Set
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol Burnett.RicciSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix.Norms.Elementwise

private def wardLowCoreScreenPoint (x : WardParabolicLowTestPoint) (u : NullFrequencyCoordinates) :
    WardParabolicTestPoint := (x.1.1,x.1.2.1,x.1.2.2,u)

private def wardLowCoreThirdInput (p : WardParabolicLowTestPoint) : NullFrequencyCoordinates :=
  p.2.2.1+p.2.2.2 • p.2.1

def wardParabolicLowCoreDomain (V : Set E) : Set WardParabolicLowTestPoint :=
  {p | wardLowCoreScreenPoint p p.2.1 ∈ wardParabolicScreenDomain V ∧
    wardLowCoreScreenPoint p p.2.2.1 ∈ wardParabolicScreenDomain V ∧
    wardLowCoreScreenPoint p (wardLowCoreThirdInput p) ∈ wardParabolicScreenDomain V}

private def wardParabolicLowCoreAmplitude (W : E → E → OrderedPair → OrderedPair → ℝ)
    (tube inn out : ℝ) (k : OrderedPair) (p : WardParabolicTestPoint) : ComplexTensor2 :=
  fun i j => (wardParabolicThinScreenEntry W tube inn out (i,j) k p : ℂ)

/-- The normalized first-low physical cubic contains the original three
screened columns, the cancelled test factor, and the original frequency
gradient denominators. -/
def wardParabolicLowScreenedCore (G : E → Mat) (W : E → E → OrderedPair → OrderedPair → ℝ)
    (M : WardParabolicTestPoint → ℝ) (tube inn out : ℝ) (k j l : OrderedPair)
    (p : WardParabolicLowTestPoint) : ℂ :=
  let s := wardLowCoreScreenPoint p p.2.1
  let t := wardLowCoreScreenPoint p p.2.2.1
  let u := wardLowCoreScreenPoint p (wardLowCoreThirdInput p)
  let q₀ := wardParabolicNormalizedFrequency s
  let q₁ := wardParabolicNormalizedFrequency t
  let q₂ := wardParabolicNormalizedFrequency u
  let H := wardParabolicLowCoreAmplitude W tube inn out k s
  let J := wardParabolicLowCoreAmplitude W tube inn out j t
  let L := wardParabolicLowCoreAmplitude W tube inn out l u
  let Γ := complexPrincipalVertex (G p.1.1) (fun i => (p.2.2.2 • q₀) i) H
    (fun i => q₁ i) J (fun i => (-q₂) i) L
  (wardParabolicLowCyclicTest M p : ℂ) * Γ * ((((‖q₀‖ * ‖q₁‖ * ‖q₂‖)⁻¹ : ℝ)) : ℂ)

theorem wardParabolicLowScreenedCore_contDiffOn (V : Set E)
    (G : E → Mat) (hG : ContDiffOn ℝ ∞ G V) (hND : ∀ x ∈ V, Matrix.det (G x) ≠ 0)
    (W : E → E → OrderedPair → OrderedPair → ℝ)
    (hW : ∀ k j, ContDiffOn ℝ ∞ (fun p : Joint => W p.1 p.2 k j) (V ×ˢ {u : E | u ≠ 0}))
    (M : WardParabolicTestPoint → ℝ) (hM : ContDiff ℝ ∞ M)
    (tube inn out : ℝ) (hTube : tube ≠ 0) (k j l : OrderedPair) :
    ContDiffOn ℝ ∞ (wardParabolicLowScreenedCore G W M tube inn out k j l)
      (wardParabolicLowCoreDomain V) := by
  let X := WardParabolicLowTestPoint
  let O := wardParabolicLowCoreDomain V
  let c (p : X) := p.1.1
  let F (p : X) := p.1.2.1
  let δ (p : X) := p.1.2.2
  let ρ (p : X) := p.2.2.2
  let u₀ (p : X) := p.2.1
  let θ (p : X) := p.2.2.1
  let v (p : X) := wardLowCoreThirdInput p
  let q₀ (p : X) := wardParabolicNormalizedFrequency (wardLowCoreScreenPoint p (u₀ p))
  let q₁ (p : X) := wardParabolicNormalizedFrequency (wardLowCoreScreenPoint p (θ p))
  let q₂ (p : X) := wardParabolicNormalizedFrequency (wardLowCoreScreenPoint p (v p))
  have dc : ContDiff ℝ ∞ c := contDiff_fst.fst
  have dF : ContDiff ℝ ∞ F := contDiff_fst.snd.fst
  have dδ : ContDiff ℝ ∞ δ := contDiff_fst.snd.snd
  have dρ : ContDiff ℝ ∞ ρ := contDiff_snd.snd.snd
  have du₀ : ContDiff ℝ ∞ u₀ := contDiff_snd.fst
  have dθ : ContDiff ℝ ∞ θ := contDiff_snd.snd.fst
  have dv : ContDiff ℝ ∞ v := dθ.add (dρ.smul du₀)
  have hg₀ : MapsTo c O V := fun _ hp => hp.1.1
  have dq (u : X → NullFrequencyCoordinates) (du : ContDiff ℝ ∞ u) :
      ContDiffOn ℝ ∞ (fun p => wardParabolicNormalizedFrequency (wardLowCoreScreenPoint p (u p))) O :=
    dF.contDiffOn.clm_apply (parabolicDilation_contDiffOn dδ.contDiffOn du.contDiffOn)
  have nq₀ (p : X) (hp : p ∈ O) : q₀ p ≠ 0 := hp.1.2
  have nq₁ (p : X) (hp : p ∈ O) : q₁ p ≠ 0 := hp.2.1.2
  have nq₂ (p : X) (hp : p ∈ O) : q₂ p ≠ 0 := hp.2.2.2
  have amp (u : X → NullFrequencyCoordinates) (du : ContDiff ℝ ∞ u)
      (hu : MapsTo (fun p => wardLowCoreScreenPoint p (u p)) O (wardParabolicScreenDomain V))
      (b d : OrderedPair) :
      ContDiffOn ℝ ∞ (fun p => wardParabolicLowCoreAmplitude W tube inn out b
        (wardLowCoreScreenPoint p (u p)) d.1 d.2) O := by
    have ds : ContDiff ℝ ∞ (fun p => wardLowCoreScreenPoint p (u p)) :=
      dc.prodMk (dF.prodMk (dδ.prodMk du))
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((wardParabolicThinScreenEntry_contDiffOn V W hW tube inn out hTube d b).comp ds.contDiffOn hu)
  have hvertex := wardComplexPrincipalVertex_contDiffOn O (G ∘ c) (hG.comp dc.contDiffOn hg₀)
    (fun p hp => hND (c p) (hg₀ hp))
    (fun p => ρ p • q₀ p) q₁ (fun p => -q₂ p) (dρ.contDiffOn.smul (dq u₀ du₀)) (dq θ dθ) (dq v dv).neg
    (fun p => wardParabolicLowCoreAmplitude W tube inn out k (wardLowCoreScreenPoint p (u₀ p)))
    (fun p => wardParabolicLowCoreAmplitude W tube inn out j (wardLowCoreScreenPoint p (θ p)))
    (fun p => wardParabolicLowCoreAmplitude W tube inn out l (wardLowCoreScreenPoint p (v p)))
    (amp u₀ du₀ (fun _ hp => hp.1) k) (amp θ dθ (fun _ hp => hp.2.1) j) (amp v dv (fun _ hp => hp.2.2) l)
  have hDen := (((dq u₀ du₀).norm ℝ nq₀).mul ((dq θ dθ).norm ℝ nq₁)).mul ((dq v dv).norm ℝ nq₂)
  have hInv : ContDiffOn ℝ ∞ (fun p => (((‖q₀ p‖ * ‖q₁ p‖ * ‖q₂ p‖)⁻¹ : ℝ) : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hDen.inv fun p hp => mul_ne_zero (mul_ne_zero (norm_ne_zero_iff.mpr (nq₀ p hp))
        (norm_ne_zero_iff.mpr (nq₁ p hp))) (norm_ne_zero_iff.mpr (nq₂ p hp)))
  exact (((Complex.ofRealCLM.contDiff.comp (wardParabolicLowCyclicTest_smooth M hM)).contDiffOn.mul
    hvertex).mul hInv)

end Burnett.C02
