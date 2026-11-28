import Burnett.Analysis.TransportWard.Weyl.ScaledSymbolA01
import Burnett.Analysis.FrozenTransport.V03SegmentTaylor

set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 1600

noncomputable section

namespace Burnett.V03

open Function Burnett.A03 Burnett.A02.FrequencySplit
open scoped ContDiff

local notation "P" => RadianParameter
local notation "W" => radianFrequencyWeight

def frequencyDirectionalSymbol (a : E → E → ℂ) (e : E) (x ξ : E) : ℂ :=
  fderiv ℝ (a x) ξ e

private theorem frequencyDirectionalSymbol_eq_joint (a : E → E → ℂ)
    (hs : ContDiff ℝ ∞ (uncurry a)) (e : E) (p : P) :
    frequencyDirectionalSymbol a e p.1 p.2 = fderiv ℝ (uncurry a) p (0,e) := by
  let L := ContinuousLinearMap.inr ℝ E E
  have hLine : HasFDerivAt (fun ζ => (p.1,ζ)) L p.2 := by
    exact (L.hasFDerivAt.add_const (p.1,0)).congr_of_eventuallyEq
      (.of_forall fun ζ => by simp [L])
  have hd := ((hs.differentiable (by simp)) p).hasFDerivAt.comp p.2 hLine
  change fderiv ℝ (uncurry a ∘ fun ζ => (p.1,ζ)) p.2 e = _
  rw [hd.fderiv]
  rfl

theorem frequencyDirectionalSymbol_jointSmooth (a : E → E → ℂ)
    (hs : ContDiff ℝ ∞ (uncurry a)) :
    ContDiff ℝ ∞ (fun z : P × E => frequencyDirectionalSymbol a z.2 z.1.1 z.1.2) := by
  simp_rw [frequencyDirectionalSymbol_eq_joint a hs]
  exact ((hs.fderiv_right (by simp)).comp contDiff_fst).clm_apply
    (contDiff_const.prodMk contDiff_snd)

theorem frequencyDirectionalSymbol_smooth (a : E → E → ℂ)
    (hs : ContDiff ℝ ∞ (uncurry a)) (e : E) :
    ContDiff ℝ ∞ (uncurry (frequencyDirectionalSymbol a e)) :=
  (frequencyDirectionalSymbol_jointSmooth a hs).comp (contDiff_id.prodMk contDiff_const)

/-- One genuine fiber derivative costs exactly one power of the same
ordinary frequency weight in the scaled joint jets. -/
theorem scaled_frequencyDirectionalSymbol_le (a : E → E → ℂ)
    (hs : ContDiff ℝ ∞ (uncurry a)) (e : E) (n : ℕ) (p : P) :
    W p.2 * ‖radianScaledParameterJet (uncurry (frequencyDirectionalSymbol a e)) n p‖ ≤
      ‖e‖ * ‖radianScaledParameterJet (uncurry a) (n+1) p‖ := by
  let s := W p.2
  let d : P := (0,e)
  let S := radianParameterScale s
  let G (q : P) := uncurry a (p+S q)
  let H (q : P) := uncurry (frequencyDirectionalSymbol a e) (p+S q)
  have hG : ContDiff ℝ ∞ G := hs.comp (contDiff_const.add S.contDiff)
  have hH : ContDiff ℝ ∞ H :=
    (frequencyDirectionalSymbol_smooth a hs e).comp (contDiff_const.add S.contDiff)
  have hD : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
  have hd : ‖d‖ = ‖e‖ := by
    simp only [d, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg e)]
  have he : (fun q => fderiv ℝ G q d) = s • H := by
    funext q
    have ha := (hs.differentiable (by simp) (p+S q)).hasFDerivAt.comp q
      (S.hasFDerivAt.const_add p)
    change fderiv ℝ (uncurry a ∘ fun y => p+S y) q d = _
    have hScale : S d = s • d := by
      apply Prod.ext
      · simp [S,d]
      · rfl
    rw [ha.fderiv, ContinuousLinearMap.comp_apply, hScale, map_smul]
    exact congrArg (s • ·) (frequencyDirectionalSymbol_eq_joint a hs e (p+S q)).symm
  have hOrder : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  calc
    _ = ‖iteratedFDeriv ℝ n (fun q => fderiv ℝ G q d) 0‖ := by
      rw [he, iteratedFDeriv_const_smul_apply (hH.contDiffAt.of_le hOrder), norm_smul,
        Real.norm_of_nonneg (radian_frequency_weight_pos p.2).le]
      rw [radian_parameter_jet_affine _ (frequencyDirectionalSymbol_smooth a hs e) n p s]
      rfl
    _ ≤ ‖d‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ G) 0‖ :=
      norm_iteratedFDeriv_clm_apply_const hD.contDiffAt (by exact_mod_cast le_top)
    _ = _ := by
      rw [hd, norm_iteratedFDeriv_fderiv]
      exact congrArg (fun v => ‖e‖ * ‖v‖) (radian_parameter_jet_affine _ hs (n+1) p s)

theorem secondFDeriv_eq_frequencyDirectionalSymbol_twice (a : E → E → ℂ)
    (hs : ContDiff ℝ ∞ (uncurry a)) (x ξ e : E) :
    secondFDeriv (a x) ξ e e =
      frequencyDirectionalSymbol (frequencyDirectionalSymbol a e) e x ξ := by
  let D : (E →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ e
  have hSlice : ContDiff ℝ ∞ (a x) := hs.comp (contDiff_const.prodMk contDiff_id)
  have hD : ContDiff ℝ ∞ (fderiv ℝ (a x)) := hSlice.fderiv_right (by simp)
  have hm : DifferentiableAt ℝ (fderiv ℝ (a x)) ξ := (hD.differentiable (by simp)) ξ
  have h := D.hasFDerivAt.comp ξ hm.hasFDerivAt
  change _ = fderiv ℝ (D ∘ fderiv ℝ (a x)) ξ e
  rw [h.fderiv]
  rfl

end Burnett.V03
