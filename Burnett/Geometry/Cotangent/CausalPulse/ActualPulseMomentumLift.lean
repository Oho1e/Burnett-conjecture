import Burnett.Geometry.Cotangent.CausalPulse.CanonicalPulseFirstIntegral

set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option maxRecDepth 3650

noncomputable section

namespace Burnett.Geometry.CausalOrbitPulse

open Set MeasureTheory
open scoped ContDiff Topology Manifold ENNReal
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonInitialFamily Burnett.Geometry.ActualTestLift

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M]

attribute [local instance] puncturedMeasurable puncturedBorel unitNullMeasurable unitNullBorel

/-- On a spacetime with a continuous Cauchy time for its null orbits, the
original unit-null measure lifts to the full null cone. The lift preserves
the exact quadratic moments and satisfies the full cotangent transport law. -/
theorem exists_actualFullMomentumLift_of_completeNullTime
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (T : M → ℝ)
    (hTc : Continuous T) (hT : HasCompleteNullTime T g hg hn hs)
    (μ : Measure (cotangentUnitNull r g hn)) [IsLocallyFiniteMeasure μ]
    (ht : HasActualUnitTransport r g hn μ) :
    ∃ s : CotangentBundle M → ℝ, ∃ hpos : ∀ p ∈ cotangentUnitNull r g hn, 0 < s p,
      let ν := actualWeightedLift r g hn s hpos μ
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ s puncturedCotangent ∧
      ν.Regular ∧ ν {p | dualEnergy g hn p.val ≠ 0} = 0 ∧
      (∀ K : Set M, IsCompact K →
        let V := {p : cotangentUnitNull r g hn | p.val.1 ∈ K}
        let Q := {p : puncturedCotangent (M := M) | p.val.1 ∈ K}
        (∫⁻ p : puncturedCotangent (M := M),
          ENNReal.ofReal (Q.indicator (fun q : puncturedCotangent (M := M) => (cotangentNorm r q.val)^2) p)
          ∂ν) = μ V ∧ μ V < (⊤ : ℝ≥0∞)) ∧
      (∀ Q : CotangentBundle M → ℝ,
        Measurable (fun p : puncturedCotangent (M := M) => Q p.val) →
        (∀ p ∈ puncturedCotangent, ∀ a > (0 : ℝ), Q (cotangentScale a p) = a^2 * Q p) →
        (Integrable (fun p : puncturedCotangent (M := M) => Q p.val) ν ↔
          Integrable (fun p : cotangentUnitNull r g hn => Q p.val) μ) ∧
        (∫ p : puncturedCotangent (M := M), Q p.val ∂ν) = ∫ p : cotangentUnitNull r g hn, Q p.val ∂μ) ∧
      ∀ b : CotangentBundle M → ℝ,
        ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ b puncturedCotangent →
        HasCompactSupport (fun p : puncturedCotangent (M := M) => b p.val) →
        Integrable (fun p : puncturedCotangent (M := M) => actualHamiltonDerivative g b p.val) ν ∧
        (∫ p : puncturedCotangent (M := M), actualHamiltonDerivative g b p.val ∂ν) = 0 := by
  obtain ⟨E, hE, hEpos, hEhom, hH⟩ := exists_smooth_canonicalPulseFirstIntegral T hTc r g hg hn hs hT
  have hpp (p : CotangentBundle M) (hp : p ∈ cotangentUnitNull r g hn) : p ∈ puncturedCotangent :=
    cotangentUnitNull_covector_ne_zero r g hn hp
  have hEAt (p : CotangentBundle M) (hp : p ∈ cotangentUnitNull r g hn) :
      ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞ E p :=
    hE.contMDiffAt (isOpen_puncturedCotangent.mem_nhds (hpp p hp))
  obtain ⟨s, hpos, hsSmooth, _, hTransport⟩ :=
    actual_full_transport_of_null_firstIntegral r g hg hn hs μ ht E hEAt
      (fun p hp => hEpos p (hpp p hp)) (fun p hp _ => hEhom p hp) (fun p hp => hH p (hpp p hp) hp.2)
  have hsCont : ContinuousOn s (cotangentUnitNull r g hn) :=
    hsSmooth.continuousOn.mono hpp
  obtain ⟨hReg, hSupport⟩ := actualWeightedLift_regular_null r g hg hn hs μ s hsCont hpos
  exact ⟨s, hpos, hsSmooth, hReg, hSupport,
    fun K hK => actualWeightedLift_local_second_moment r g hn μ s hsCont hpos K hK hg hs,
    fun Q hQ hscale => actualWeightedLift_quadratic_pairing r g hn μ s hsCont hpos Q hQ hscale,
    hTransport⟩

end Burnett.Geometry.CausalOrbitPulse
