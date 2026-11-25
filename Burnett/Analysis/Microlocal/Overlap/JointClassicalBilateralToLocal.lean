import Burnett.Analysis.Microlocal.Overlap.ReceivingOriginalSourceReplacement
import Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol
import Burnett.Analysis.Microlocal.Overlap.ReceivingOriginalSourceReplacement

/-! A left window converts a bilateral classical representation to the actual local operator class. -/
set_option autoImplicit false
set_option maxRecDepth 3900
set_option maxHeartbeats 4000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Fourier Burnett.Geometry.ConnectionDifference
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.SeparablePositive (inner_symbolCLM_left)
open Burnett.Microlocal.AtlasVolumeGradient (coeffMul_tsupport_subset_real)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul coeffMul_toLp)
open Burnett.X02.SobolevTestJet (D)
open scoped ComplexConjugate InnerProduct Topology

local notation "E" => CoordinateSpace

open private symbolCLM_conj_physicalCoefficient from Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol
open private firstOrderAction_mul_base from Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal

/-- An actual bilateral representation becomes a local representation, with
arbitrary left Schwartz tests, after multiplication on its output by a cutoff
supported in the left window. The given compact correction stays compact. -/
theorem hasLocalClassicalRepresentation_leftCutoff_of_bilateral
    (T R : ComplexL2 E →L[ℂ] ComplexL2 E) (hR : IsCompactOperator R)
    (a : E → E → ℂ) (W L : Set E) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ W)
    (hRep : ∀ f v : SchwartzMap E ℂ, tsupport (f : E → ℂ) ⊆ W → tsupport (v : E → ℂ) ⊆ L →
      inner ℂ (f.toLp 2 volume) (T (v.toLp 2 volume)) =
        classicalLeftPairing (infraredAngularPrincipal a) f v + inner ℂ (f.toLp 2 volume) (R (v.toLp 2 volume))) :
    HasLocalClassicalRepresentation ((symbolCLM (physicalCoefficient χ)).comp T)
      (fun x ξ => physicalCoefficient χ x * a x ξ) L := by
  let c := physicalCoefficient χ
  let Mχ := symbolCLM c
  refine ⟨Mχ.comp R, hR.clm_comp Mχ, fun f v hv => ?_⟩
  have hSupp : tsupport (coeffMul χ f : E → ℂ) ⊆ W := (coeffMul_tsupport_subset_real χ f).trans hχ
  have hL (A : ComplexL2 E →L[ℂ] ComplexL2 E) :
      inner ℂ (f.toLp 2 volume) ((Mχ.comp A) (v.toLp 2 volume)) =
        inner ℂ ((coeffMul χ f).toLp 2 volume) (A (v.toLp 2 volume)) := by
    change inner ℂ (f.toLp 2 volume) (symbolCLM c (A (v.toLp 2 volume))) = _
    have h := inner_symbolCLM_left c (f.toLp 2 volume) (A (v.toLp 2 volume))
    rw [symbolCLM_conj_physicalCoefficient, ← coeffMul_toLp] at h
    exact h.symm
  have hI : classicalLeftPairing (infraredAngularPrincipal a) (coeffMul χ f) v =
      ∫ x, conj (f x) * firstOrderAction (infraredAngularPrincipal (fun y ξ => c y * a y ξ)) v x := by
    unfold classicalLeftPairing
    apply integral_congr_ae
    filter_upwards with x
    have he : infraredAngularPrincipal (fun y ξ => c y * a y ξ) =
        (fun y ξ => c y * infraredAngularPrincipal a y ξ) := by
      funext y ξ
      unfold infraredAngularPrincipal
      ring
    rw [he, firstOrderAction_mul_base]
    change conj ((c x) * f x) * _ = _
    simp only [map_mul, c, physicalCoefficient, Complex.conj_ofReal]
    ring
  rw [hL T, hL R, hRep _ _ hSupp hv, hI]

end Burnett.Microlocal.Overlap
