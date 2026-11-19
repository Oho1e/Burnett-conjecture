import Burnett.Analysis.ShiftedFourierWindow.LowPassFourier
import Burnett.Analysis.SignedFourierWindow.SignedBands
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
open MeasureTheory Burnett.Fourier
open scoped FourierTransform RealInnerProductSpace ContDiff

private def waveWindow (ξ q : Space) := Complex.exp ((↑(2*Real.pi*inner ℝ ξ q):ℂ)*Complex.I)
private theorem waveWindow_unit (ξ q : Space) : ‖waveWindow ξ q‖=1 := by simp [waveWindow,Complex.norm_exp]

def modulatedWindowSymbol (a : SchwartzMap Space ℂ) (q : Space) : BoundedSymbol Space where
  toFun ξ := waveWindow ξ q * a ξ
  measurable := (show Continuous (fun ξ => waveWindow ξ q * a ξ) by unfold waveWindow; fun_prop).aestronglyMeasurable
  bound := SchwartzMap.seminorm ℝ 0 0 a
  bound_nonneg := apply_nonneg _ _
  norm_le ξ := by rw [norm_mul,waveWindow_unit,one_mul]; exact SchwartzMap.norm_le_seminorm ℝ a ξ

/-- On Schwartz inputs, the extended L² projection and the actual pointwise
Fourier integral give the same function almost everywhere. -/
theorem shiftedWindow_L2_ae (a : SchwartzMap Space ℂ) (ha : HasCompactSupport (a : Space → ℂ))
    (f : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) (q : Space) :
    (fourierMultiplier (rescaleSymbol (modulatedWindowSymbol a q) s hs) (f.toLp 2 volume) : Space → ℂ) =ᵐ[volume]
      shiftedWindowOperator a f s q := by
  let m := rescaleSymbol (modulatedWindowSymbol a q) s hs
  let v := SchwartzMap.fourierTransformCLE ℂ f
  let A := fun ξ : Space => (waveWindow (s • ξ) q * a (s • ξ)) * v ξ
  have h₁ : HasCompactSupport (fun ξ : Space => a (s • ξ)) := ha.comp_homeomorph (Homeomorph.smulOfNeZero s hs.ne')
  have h₂ : HasCompactSupport A := (h₁.mul_left (f := fun ξ => waveWindow (s • ξ) q)).mul_right
  have hr : ContDiff ℝ ∞ (fun ξ : Space => 2*Real.pi*inner ℝ (s • ξ) q) :=
    contDiff_const.mul ((contDiff_const.smul contDiff_id).inner ℝ contDiff_const)
  have hw : ContDiff ℝ ∞ (fun ξ : Space => waveWindow (s • ξ) q) :=
    ((Complex.ofRealCLM.contDiff.comp hr).mul (contDiff_const (c := Complex.I))).cexp
  have h₃ : ContDiff ℝ ∞ A := (hw.mul ((a.smooth ⊤).comp (contDiff_const.smul contDiff_id))).mul (v.smooth ⊤)
  let G : SchwartzMap Space ℂ := h₂.toSchwartzMap h₃
  have he : symbolL2 m (fourierL2Equiv (f.toLp 2 volume)) = G.toLp 2 volume := by
    rw [fourierL2Equiv_schwartz]
    apply Lp.ext
    filter_upwards [symbolL2_ae m (v.toLp 2 volume),v.coeFn_toLp 2 volume,G.coeFn_toLp 2 volume] with ξ hm hv hG
    rw [hm,hv,hG]
    rfl
  have phys (x : Space) : 𝓕⁻ (G : Space → ℂ) x = shiftedWindowOperator a f s q x := by
    rw [Real.fourierIntegralInv_eq']
    change (∫ ξ : Space, waveWindow ξ x * ((waveWindow (s • ξ) q * a (s • ξ)) * v ξ)) =
      ∫ ξ : Space, (waveWindow ξ x * waveWindow (s • ξ) q * a (s • ξ)) * v ξ
    simp only [mul_assoc]
  change (fourierL2Equiv.symm (symbolL2 m (fourierL2Equiv (f.toLp 2 volume))) : Space → ℂ) =ᵐ[volume] _
  rw [he]
  exact (fourierL2Equiv_symm_schwartz_ae G).trans (Filter.Eventually.of_forall phys)

end Burnett.Analysis.SignedFourierWindow
