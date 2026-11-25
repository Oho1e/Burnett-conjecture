import Burnett.Geometry.Cotangent.ActualCrossingFirstIntegral
import Burnett.Geometry.Cotangent.ActualWeightedLiftMoments

set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option maxRecDepth 3650

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set MeasureTheory
open scoped ContDiff Topology Manifold ENNReal
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonCauchySlice Burnett.Geometry.CotangentHamiltonCrossingEnergy
open Burnett.Geometry.ActualTestLift

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M]

attribute [local instance] puncturedMeasurable puncturedBorel unitNullMeasurable unitNullBorel

/-- An actual unit-null transport measure has the original full-momentum lift
on a spacetime with a smooth spacelike Cauchy slice. The single section and
measure give the preserved quadratic moments and every full transport test. -/
theorem exists_actualFullMomentumLift_of_smooth_spacelike_cauchy
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    (S : Set M) (hC : RegularCauchySliceProperty g S) (hS : SmoothSpacelikeSlice g S)
    (μ : Measure (cotangentUnitNull r g hn)) [IsLocallyFiniteMeasure μ]
    (ht : HasActualUnitTransport r g hn μ) :
    ∃ s : CotangentBundle M → ℝ, ∃ hpos : ∀ p ∈ cotangentUnitNull r g hn, 0 < s p,
      let ν := actualWeightedLift r g hn s hpos μ
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ s puncturedCotangent ∧
      (∀ p (hp : p ∈ cotangentUnitNull r g hn),
        s p = (globalCrossingEnergy r g hg hn hs hL S hC
          ⟨p, cotangentUnitNull_covector_ne_zero r g hn hp, hp.2⟩)⁻¹) ∧
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
  obtain ⟨E, hE, hEpos, hEhom, hTrace, hH⟩ :=
    exists_smooth_actualCrossing_firstIntegral r g hg hn hs hL S hC hS
  have hpp (p : CotangentBundle M) (hp : p ∈ cotangentUnitNull r g hn) : p ∈ puncturedCotangent :=
    cotangentUnitNull_covector_ne_zero r g hn hp
  have hEAt (p : CotangentBundle M) (hp : p ∈ cotangentUnitNull r g hn) :
      ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞ E p :=
    hE.contMDiffAt (isOpen_puncturedCotangent.mem_nhds (hpp p hp))
  obtain ⟨s, hpos, hsSmooth, hsTrace, hTransport⟩ :=
    actual_full_transport_of_null_firstIntegral r g hg hn hs μ ht E hEAt
      (fun p hp => hEpos p (hpp p hp)) (fun p hp _ => hEhom p hp) (fun p hp => hH p (hpp p hp) hp.2)
  have hsCont : ContinuousOn s (cotangentUnitNull r g hn) :=
    hsSmooth.continuousOn.mono (fun p hp => hpp p hp)
  obtain ⟨hReg, hSupport⟩ := actualWeightedLift_regular_null r g hg hn hs μ s hsCont hpos
  refine ⟨s, hpos, hsSmooth, ?_, hReg, hSupport, ?_, ?_, hTransport⟩
  · intro p hp
    rw [hsTrace p hp, hTrace p (hpp p hp) hp.2]
  · intro K hK
    exact actualWeightedLift_local_second_moment r g hn μ s hsCont hpos K hK hg hs
  · intro Q hQ hscale
    exact actualWeightedLift_quadratic_pairing r g hn μ s hsCont hpos Q hQ hscale

end Burnett.Geometry.CotangentHamiltonInitialFamily
