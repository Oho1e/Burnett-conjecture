import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinSchwartz
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinExtension

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.DyadicSquare (rescaleSymbol)
open Burnett.Analysis.ShiftedFourierWindow (shifted_window_physical)
open Burnett.Analysis.SignedFourierWindow
open Set MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open scoped ENNReal ContDiff

/-- One complex-linear bounded operator on all of Lᵖ, with its fixed exact
Fourier symbol on L²∩Lᵖ and the manuscript's radian integral on Schwartz tests. -/
def MikhlinRealization (m : E → ℝ) (p : ℝ) (hp : 1<p) : Prop :=
  let P := ENNReal.ofReal p
  letI : Fact (1 ≤ P) := ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
  ∃ (M : BoundedSymbol E) (S : Lp ℂ P (volume : Measure E) →L[ℂ] Lp ℂ P volume) (C : ℝ),
    (∀ ξ, M ξ = (m ξ : ℂ)) ∧ (∀ f, ‖S f‖ ≤ C * ‖f‖) ∧
    (∀ (f : E → ℂ) (h₂ : MemLp f 2 volume) (hp' : MemLp f P volume),
      (S (hp'.toLp f) : E → ℂ) =ᵐ[volume] (fourierMultiplier M (h₂.toLp f) : E → ℂ)) ∧
    (∀ f : SchwartzMap E ℂ, (S (f.toLp P volume) : E → ℂ) =ᵐ[volume] radianAction m f)

theorem homogeneous_multiplier_all_Lp (m : E → ℝ) (hm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ)=m ξ) (p : ℝ) (hp : 1<p) : MikhlinRealization m p hp := by
  let P := ENNReal.ofReal p
  letI : Fact (1 ≤ P) := ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
  obtain ⟨M,hM⟩ := mikhlin_bounded_symbol m hm hh
  obtain ⟨C,hC,bd⟩ := homogeneous_multiplier_intersection_bound m hm hh M hM p hp
  obtain ⟨S,hs,eq⟩ := mikhlin_extend_from_intersection P ENNReal.ofReal_ne_top (fourierMultiplier M) C hC bd
  exact ⟨M,S,C.toReal,hM,hs,eq,fun f => (eq f (f.memLp 2 volume) (f.memLp P volume)).trans
    (mikhlin_action_test m M hM hh f)⟩

/-- The actual linear output/input symbols cⱼ and the real Riesz factors
used with Dⱼ=−i∂ⱼ all act boundedly at each finite exponent above one. -/
theorem paper_cj_riesz_all_Lp (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ ξ, b (t • ξ)=t*b ξ) (j : Index) (p : ℝ) (hp : 1<p) :
    MikhlinRealization (angularComponent b j) p hp ∧ MikhlinRealization (mikhlinRiesz j) p hp :=
  ⟨homogeneous_multiplier_all_Lp _ (angularComponent_contDiffOn b hb j) (angularComponent_scale hh j) p hp,
   homogeneous_multiplier_all_Lp _ (mikhlinRiesz_regular j).1 (mikhlinRiesz_regular j).2 p hp⟩

end Burnett.A02.FrequencySplit
