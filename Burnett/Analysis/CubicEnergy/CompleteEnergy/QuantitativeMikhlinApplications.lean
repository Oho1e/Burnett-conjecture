import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlin
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinApplications
import Burnett.Analysis.CubicEnergy.CompleteEnergy.SymbolSeminormLow

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Burnett.Fourier Burnett.RicciSymbol
open scoped ContDiff ENNReal

/-- The finite-jet coefficient persists for the bounded operator on the full
complex Lᵖ space and for its agreement with the manuscript's radian formula. -/
theorem homogeneous_multiplier_all_Lp_sphere_bound (p : ℝ) (hp : 1<p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : E → ℝ), ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ) = m ξ) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n m ξ‖ ≤ D) →
      let P := ENNReal.ofReal p
      letI : Fact (1 ≤ P) := ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
      ∃ (M : BoundedSymbol E) (S : Lp ℂ P (volume : Measure E) →L[ℂ] Lp ℂ P volume),
        (∀ ξ, M ξ = (m ξ : ℂ)) ∧ (∀ f, ‖S f‖ ≤ C * D * ‖f‖) ∧
        (∀ (f : E → ℂ) (h₂ : MemLp f 2 volume) (hp' : MemLp f P volume),
          (S (hp'.toLp f) : E → ℂ) =ᵐ[volume] (fourierMultiplier M (h₂.toLp f) : E → ℂ)) ∧
        (∀ f : SchwartzMap E ℂ, (S (f.toLp P volume) : E → ℂ) =ᵐ[volume] radianAction m f) := by
  obtain ⟨C,hC,bound⟩ := homogeneous_multiplier_intersection_sphere_bound p hp
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro m hm hh D hD jet P
  letI : Fact (1 ≤ P) := ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
  obtain ⟨M,hM⟩ := mikhlin_bounded_symbol m hm hh
  obtain ⟨S,hs,eq⟩ := mikhlin_extend_from_intersection P ENNReal.ofReal_ne_top (fourierMultiplier M)
    (C * ENNReal.ofReal D) (ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top)
    (fun f hf hfp => (bound m hm hh D hD jet M hM f hf hfp).2)
  refine ⟨M,S,hM,fun f => ?_,eq,?_⟩
  · simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hD] using hs f
  · intro f
    exact (eq f (f.memLp 2 volume) (f.memLp P volume)).trans (mikhlin_action_test m M hM hh f)

/-- The actual angular factors c_j(D) have linear bounds from b's spherical
jet, with the same coefficient for all four coordinate indices. -/
theorem paper_cj_Schwartz_sphere_bound (p : ℝ) (hp : 1<p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
      (∀ (t : ℝ), 0<t → ∀ ξ, b (t • ξ) = t*b ξ) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (j : Index) (f : SchwartzMap E ℂ),
        eLpNorm (radianAction (angularComponent b j) f) (ENNReal.ofReal p) volume ≤
          C * ENNReal.ofReal D * eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,bound⟩ := homogeneous_multiplier_intersection_sphere_bound p hp
  obtain ⟨A,hA,ajet⟩ := angular_component_sphere_jet 6
  refine ⟨C * ENNReal.ofReal A, ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top, ?_⟩
  intro b hb hom D hD jet j f
  let m := angularComponent b j
  have hm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0} := angularComponent_contDiffOn b hb j
  have hh : ∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ) = m ξ := angularComponent_scale hom j
  obtain ⟨M,hM⟩ := mikhlin_bounded_symbol m hm hh
  rw [← eLpNorm_congr_ae (mikhlin_action_test m M hM hh f)]
  have h := (bound m hm hh (A*D) (mul_nonneg hA hD) (ajet b hb D hD jet j) M hM
    f (f.memLp 2 volume) (f.memLp _ volume)).2
  simpa only [ENNReal.ofReal_mul hA, mul_assoc] using h

end Burnett.A02.FrequencySplit
