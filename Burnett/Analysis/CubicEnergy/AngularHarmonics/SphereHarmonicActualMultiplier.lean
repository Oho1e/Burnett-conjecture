import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicRadialJetBounds
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlinApplications

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

namespace Burnett.A06

open Metric MeasureTheory Burnett.Fourier Burnett.A02.FrequencySplit
open scoped ENNReal ContDiff

/-- The angular symbol of the manuscript's actual normalized harmonic. -/
def sphereHarmonicMultiplierSymbol (d : ℕ) (i : Fin ((d + 1)^2)) : RotationSpace → ℝ :=
  sphereHarmonicRadialSymbol d (sphereHarmonicPolynomialBasis d i)

theorem sphereHarmonicMultiplierSymbol_eq (d : ℕ) (i : Fin ((d + 1)^2))
    {ξ : RotationSpace} (hξ : ξ ≠ 0) :
    sphereHarmonicMultiplierSymbol d i ξ =
      sphereHarmonicBasisFunction d i ⟨roundSphereRadialNormalize ξ,
        mem_sphere_zero_iff_norm.mpr (roundSphereRadialNormalize_norm hξ)⟩ := rfl

/-- The actual whole-space multiplier for each real spherical harmonic has
norm O((d+1)^7), uniformly within the degree, together with its radian
formula and its compatibility with the actual L² operator. -/
theorem exists_sphereHarmonicMultiplier_Lp_bound (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) (i : Fin ((d + 1)^2)),
      let P := ENNReal.ofReal p
      letI : Fact (1 ≤ P) :=
        ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
      ∃ (M : BoundedSymbol RotationSpace)
        (S : Lp ℂ P (volume : Measure RotationSpace) →L[ℂ] Lp ℂ P volume),
      (∀ ξ, M ξ = (sphereHarmonicMultiplierSymbol d i ξ : ℂ)) ∧
      (∀ f, ‖S f‖ ≤ C * ((d : ℝ) + 1)^7 * ‖f‖) ∧
      (∀ (f : RotationSpace → ℂ) (h₂ : MemLp f 2 volume) (hp' : MemLp f P volume),
        (S (hp'.toLp f) : RotationSpace → ℂ) =ᵐ[volume]
          (fourierMultiplier M (h₂.toLp f) : RotationSpace → ℂ)) ∧
      ∀ f : SchwartzMap RotationSpace ℂ,
        (S (f.toLp P volume) : RotationSpace → ℂ) =ᵐ[volume] radianAction (sphereHarmonicMultiplierSymbol d i) f := by
  obtain ⟨A,hA,hjet⟩ := exists_sphereHarmonicRadialSymbol_mikhlin_jets
  obtain ⟨B,hB,hbound⟩ := homogeneous_multiplier_all_Lp_sphere_bound p hp
  refine ⟨B*A, mul_nonneg hB hA, ?_⟩
  intro d i
  let H := sphereHarmonicPolynomialBasis d i
  let D := A * ((d : ℝ) + 1)^7
  have hnorm : ‖sphereHarmonicToLp d H‖ = 1 := by
    have h := sphereHarmonicBasisFunction_toLp d i
    change sphereHarmonicToLp d H = (sphereHarmonicLpOrthonormalBasis d i : RoundSphereL2) at h
    rw [h]
    exact (sphereHarmonicLpOrthonormalBasis d).orthonormal.norm_eq_one i
  have jet (n : ℕ) (hn : n ≤ 6) (x : RotationSpace) (hx : x ∈ sphere (0 : RotationSpace) 1) :
      ‖iteratedFDeriv ℝ n (sphereHarmonicRadialSymbol d H) x‖ ≤ D := by
    simpa only [hnorm,mul_one,D] using hjet d H n hn x hx
  obtain ⟨M,S,hM,hs,hs₂,hsTest⟩ := hbound (sphereHarmonicRadialSymbol d H)
    (sphereHarmonicRadialSymbol_contDiffOn d H)
    (sphereHarmonicRadialSymbol_smul d H) D (by positivity) jet
  exact ⟨M,S,hM,(fun f => by simpa only [D,mul_assoc] using hs f),hs₂,hsTest⟩

end Burnett.A06
