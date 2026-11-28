import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearActualGradient
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearBranchMasks
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearCapTemplate
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearLowActualCore
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearParabolicJetBudget
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearLowScreenedCore
import Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives

set_option autoImplicit false
set_option maxRecDepth 8700
set_option maxHeartbeats 15500000

noncomputable section

namespace Burnett.C02

open Set Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.A05 (endpointDirection_contDiffOn)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix.Norms.Elementwise

open private wardLowCoreScreenPoint wardLowCoreThirdInput from Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearLowScreenedCore
open private directionDerivativeCoefficient_smooth from Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives

abbrev WardNearProfileParameters (N : ℕ) := WardParabolicBase × CapNeighborParameters N
abbrev WardNearProfileInput (N : ℕ) :=
  WardNearProfileParameters N × NullFrequencyCoordinates × NullFrequencyCoordinates × ℝ

def wardNearProfileCorePoint {N : ℕ} (x : WardNearProfileInput N) : WardParabolicLowTestPoint :=
  (x.1.1,x.2)

def wardNearProfileArguments {N : ℕ} (x : WardNearProfileInput N) (j : Fin 3) :
    NullFrequencyCoordinates :=
  ![x.2.1,x.2.2.1,x.2.2.1+x.2.2.2 • x.2.1] j

def wardNearProfileTestPoint {N : ℕ} (x : WardNearProfileInput N) (j : Fin 3) :
    WardParabolicTestPoint :=
  (x.1.1.1,x.1.1.2.1,x.1.1.2.2,wardNearProfileArguments x j)

def wardNearProfileCapPoint {N : ℕ} (tube : ℝ) (s : Fin 3) (x : WardNearProfileInput N) :
    BaseCapProfileData N :=
  (((x.1.1.2.1,tube,x.1.1.2.2),x.1.2),wardNearProfileArguments x s)

def wardParabolicNearProfileDomain (N : ℕ) (V : Set E) (tube b : ℝ) (s : Fin 3) :
    Set (WardNearProfileInput N) :=
  {x | wardNearProfileCorePoint x ∈ wardParabolicLowCoreDomain V ∧
    wardNearProfileCapPoint tube s x ∈ baseCapProfileDomain N ∧
    ∀ j : Fin 3, (wardNearProfileArguments x j).1 ≠ 0 ∧
      wardNearProfileTestPoint x j ∈ wardParabolicTestDomain b}

private theorem wardNearProfileArgument_contDiff {N : ℕ} (j : Fin 3) :
    ContDiff ℝ ∞ (fun x : WardNearProfileInput N => wardNearProfileArguments x j) := by
  fin_cases j
  · exact contDiff_snd.fst
  · exact contDiff_snd.snd.fst
  · exact contDiff_snd.snd.fst.add (contDiff_snd.snd.snd.smul contDiff_snd.fst)

private theorem wardNearProfileFrame_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (fun x : WardNearProfileInput N => x.1.1.2.1) := contDiff_fst.fst.snd.fst

private theorem wardNearProfileWidth_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (fun x : WardNearProfileInput N => x.1.1.2.2) := contDiff_fst.fst.snd.snd

private theorem wardNearProfileTestPoint_contDiff {N : ℕ} (j : Fin 3) :
    ContDiff ℝ ∞ (fun x : WardNearProfileInput N => wardNearProfileTestPoint x j) :=
  contDiff_fst.fst.fst.prodMk ((wardNearProfileFrame_contDiff N).prodMk
    ((wardNearProfileWidth_contDiff N).prodMk (wardNearProfileArgument_contDiff j)))

private theorem wardNearProfileCapPoint_contDiff {N : ℕ} (tube : ℝ) (j : Fin 3) :
    ContDiff ℝ ∞ (wardNearProfileCapPoint (N := N) tube j) :=
  (((wardNearProfileFrame_contDiff N).prodMk (contDiff_const.prodMk (wardNearProfileWidth_contDiff N))).prodMk
    contDiff_fst.snd).prodMk (wardNearProfileArgument_contDiff j)

private theorem wardParabolicNormalizedFrequency_contDiff :
    ContDiff ℝ ∞ wardParabolicNormalizedFrequency :=
  contDiff_snd.fst.clm_apply (contDiffOn_univ.mp
    (parabolicDilation_contDiffOn contDiff_snd.snd.fst.contDiffOn contDiff_snd.snd.snd.contDiffOn))

private theorem wardNearProfileScreenDomain_open {V : Set E} (hV : IsOpen V) :
    IsOpen (wardParabolicScreenDomain V) :=
  (hV.preimage continuous_fst).inter
    (isOpen_ne_fun wardParabolicNormalizedFrequency_contDiff.continuous continuous_const)

private theorem wardNearProfileCoreDomain_open {V : Set E} (hV : IsOpen V) :
    IsOpen (wardParabolicLowCoreDomain V) := by
  let X := WardParabolicLowTestPoint
  have one (u : X → NullFrequencyCoordinates) (hu : ContDiff ℝ ∞ u) :
      IsOpen {p : X | wardLowCoreScreenPoint p (u p) ∈ wardParabolicScreenDomain V} :=
    (wardNearProfileScreenDomain_open hV).preimage
      (continuous_fst.fst.prodMk (continuous_fst.snd.fst.prodMk (continuous_fst.snd.snd.prodMk hu.continuous)))
  exact (one (fun p => p.2.1) contDiff_snd.fst).inter
    ((one (fun p => p.2.2.1) contDiff_snd.snd.fst).inter
      (one wardLowCoreThirdInput (contDiff_snd.snd.fst.add (contDiff_snd.snd.snd.smul contDiff_snd.fst))))

theorem wardParabolicNearProfileDomain_open {V : Set E} (hV : IsOpen V)
    (N : ℕ) (tube b : ℝ) (s : Fin 3) : IsOpen (wardParabolicNearProfileDomain N V tube b s) := by
  have hCore : Continuous (wardNearProfileCorePoint (N := N)) := continuous_fst.fst.prodMk continuous_snd
  have hTest (j : Fin 3) : IsOpen {x : WardNearProfileInput N |
      (wardNearProfileArguments x j).1 ≠ 0 ∧ wardNearProfileTestPoint x j ∈ wardParabolicTestDomain b} :=
    (isOpen_ne_fun (wardNearProfileArgument_contDiff (N := N) j).fst.continuous continuous_const).inter
      ((wardParabolicTestDomain_open b).preimage (wardNearProfileTestPoint_contDiff j).continuous)
  have hAll : IsOpen {x : WardNearProfileInput N | ∀ j : Fin 3,
      (wardNearProfileArguments x j).1 ≠ 0 ∧ wardNearProfileTestPoint x j ∈ wardParabolicTestDomain b} := by
    rw [show {x : WardNearProfileInput N | ∀ j : Fin 3, (wardNearProfileArguments x j).1 ≠ 0 ∧
      wardNearProfileTestPoint x j ∈ wardParabolicTestDomain b} =
      ⋂ j : Fin 3, {x | (wardNearProfileArguments x j).1 ≠ 0 ∧
        wardNearProfileTestPoint x j ∈ wardParabolicTestDomain b} by ext x; simp]
    exact isOpen_iInter_of_finite hTest
  exact ((wardNearProfileCoreDomain_open hV).preimage hCore).inter
    (((baseCapProfileDomain_open N).preimage (wardNearProfileCapPoint_contDiff tube s).continuous).inter hAll)

private theorem wardParabolicDilation_neg (δ : ℝ) (x : NullFrequencyCoordinates) :
    parabolicDilation δ (-x) = -parabolicDilation δ x := by
  simp [parabolicDilation]

def wardParabolicNearProfile {N : ℕ} (G : E → Mat)
    (W : E → E → OrderedPair → OrderedPair → ℝ) (M : WardParabolicTestPoint → ℝ)
    (ϑ : ℝ → ℝ) (κ tube thinIn thinOut capIn capOut : ℝ) (comparable : Bool) (s : Fin 3)
    (j : WardNearEntries) (x : WardNearProfileInput N) : ℂ :=
  let F := x.1.1.2.1
  let δ := x.1.1.2.2
  let v₀ := wardNearProfileArguments x 0
  let v₁ := wardNearProfileArguments x 1
  let v₂ := wardNearProfileArguments x 2
  let q (k : Fin 3) := wardParabolicNormalizedFrequency (wardNearProfileTestPoint x k)
  let mask := if comparable then wardParabolicComparableNearBranchWeight ϑ F δ κ v₀ v₁ (-v₂)
    else wardParabolicLowNearBranchWeight ϑ F δ κ x.2.2.2 v₀ v₁ v₂
  let base := parabolicBaseProfile F tube δ capIn capOut x.1.2 (wardNearProfileArguments x s)
  let vertex := wardParabolicLowScreenedCore G W M tube thinIn thinOut j.1.1 j.2.1.1 j.2.2.1
    (wardNearProfileCorePoint x)
  (-Complex.I/3) * (mask : ℂ) * (base : ℂ) * vertex *
    (wardNearGradientDirection j.1.2 (q 0) * wardNearGradientDirection j.2.1.2 (q 1) *
      wardNearGradientDirection j.2.2.2 (-(q 2)))

/-- The complete local normalized symbol, with its actual branch masks,
one base cap and all gradient directions, is jointly smooth before
the compact extension used by the signed or shifted charts. -/
theorem wardParabolicNearProfile_contDiffOn {N : ℕ} (V : Set E)
    (G : E → Mat) (hG : ContDiffOn ℝ ∞ G V) (hND : ∀ x ∈ V, Matrix.det (G x) ≠ 0)
    (W : E → E → OrderedPair → OrderedPair → ℝ)
    (hW : ∀ k j, ContDiffOn ℝ ∞ (fun p : Joint => W p.1 p.2 k j) (V ×ˢ {u : E | u ≠ 0}))
    (M : WardParabolicTestPoint → ℝ) (hM : ContDiff ℝ ∞ M) (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (κ tube thinIn thinOut capIn capOut b : ℝ) (hκ : κ ≠ 0) (hTube : tube ≠ 0)
    (comparable : Bool) (s : Fin 3) (j : WardNearEntries) :
    ContDiffOn ℝ ∞ (wardParabolicNearProfile G W M ϑ κ tube thinIn thinOut capIn capOut comparable s j)
      (wardParabolicNearProfileDomain N V tube b s) := by
  let X := WardNearProfileInput N
  let O := wardParabolicNearProfileDomain N V tube b s
  let F (x : X) := x.1.1.2.1
  let δ (x : X) := x.1.1.2.2
  let u (x : X) := wardNearProfileArguments x 0
  let v (x : X) := wardNearProfileArguments x 1
  let w (x : X) := wardNearProfileArguments x 2
  let q (k : Fin 3) (x : X) := wardParabolicNormalizedFrequency (wardNearProfileTestPoint x k)
  have hCore : ContDiff ℝ ∞ (wardNearProfileCorePoint (N := N)) := contDiff_fst.fst.prodMk contDiff_snd
  have hVertex := (wardParabolicLowScreenedCore_contDiffOn V G hG hND W hW M hM tube thinIn thinOut
    hTube j.1.1 j.2.1.1 j.2.2.1).comp hCore.contDiffOn (fun _ (hx : _ ∈ O) => hx.1)
  have hBase := Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((parabolicBaseProfile_joint_contDiffOn N capIn capOut).comp (wardNearProfileCapPoint_contDiff tube s).contDiffOn
      (fun _ (hx : _ ∈ O) => hx.2.1))
  have dn (k : Fin 3) : ContDiff ℝ ∞ (q k) :=
    wardParabolicNormalizedFrequency_contDiff.comp (wardNearProfileTestPoint_contDiff k)
  have nonzero (x : X) (hx : x ∈ O) : q 0 x ≠ 0 ∧ q 1 x ≠ 0 ∧ q 2 x ≠ 0 :=
    ⟨hx.1.1.2,hx.1.2.1.2,hx.1.2.2.2⟩
  have hDirection (k : Fin 4) (f : X → E) (hf : ContDiff ℝ ∞ f)
      (hn : ∀ x ∈ O, f x ≠ 0) :
      ContDiffOn ℝ ∞ (fun x => wardNearGradientDirection k (f x)) O :=
    ((directionDerivativeCoefficient_smooth k).comp_contDiffOn endpointDirection_contDiffOn).comp hf.contDiffOn
      (fun x hx => hn x hx)
  have hD₀ := hDirection j.1.2 (q 0) (dn 0) (fun x hx => (nonzero x hx).1)
  have hD₁ := hDirection j.2.1.2 (q 1) (dn 1) (fun x hx => (nonzero x hx).2.1)
  have hD₂ := hDirection j.2.2.2 (fun x => -(q 2 x)) (dn 2).neg
    (fun x hx => neg_ne_zero.mpr (nonzero x hx).2.2)
  have du : ContDiffOn ℝ ∞ u O := (wardNearProfileArgument_contDiff (N := N) 0).contDiffOn
  have dv : ContDiffOn ℝ ∞ v O := (wardNearProfileArgument_contDiff (N := N) 1).contDiffOn
  have dw : ContDiffOn ℝ ∞ w O := (wardNearProfileArgument_contDiff (N := N) 2).contDiffOn
  have dF : ContDiffOn ℝ ∞ F O := (wardNearProfileFrame_contDiff N).contDiffOn
  have dδ : ContDiffOn ℝ ∞ δ O := (wardNearProfileWidth_contDiff N).contDiffOn
  cases comparable
  · have hMask := Complex.ofRealCLM.contDiff.comp_contDiffOn
      (wardParabolicLowNearBranchWeight_contDiffOn O ϑ hϑ F δ (fun x => x.2.2.2) κ hκ u v w dF dδ
        contDiff_snd.snd.snd.contDiffOn du dv dw nonzero)
    exact ((((contDiffOn_const.mul hMask).mul hBase).mul hVertex).mul ((hD₀.mul hD₁).mul hD₂))
  · have hMask := Complex.ofRealCLM.contDiff.comp_contDiffOn
      (wardParabolicComparableNearBranchWeight_contDiffOn O ϑ hϑ F δ κ hκ u v (fun x => -(w x)) dF dδ
        du dv dw.neg (fun x hx => ⟨(nonzero x hx).1,(nonzero x hx).2.1,by
          rw [wardParabolicDilation_neg,map_neg]
          exact neg_ne_zero.mpr (nonzero x hx).2.2⟩))
    exact ((((contDiffOn_const.mul hMask).mul hBase).mul hVertex).mul ((hD₀.mul hD₁).mul hD₂))

end Burnett.C02
