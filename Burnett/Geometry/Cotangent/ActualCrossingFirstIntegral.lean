import Burnett.Geometry.Cotangent.MaximalCanonicalCrossing
import Burnett.Geometry.Cotangent.CanonicalTestDerivative

set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option maxRecDepth 3700

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter
open scoped ContDiff Topology Manifold
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonMaximalCurve Burnett.Geometry.CotangentHamiltonCauchySlice
open Burnett.Geometry.CotangentHamiltonCrossingEnergy Burnett.Geometry.ActualTestLift

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

private def crossingEnergyTrace (r : Metric (M := M)) (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) (S : Set M) (hC : RegularCauchySliceProperty g S)
    (q : CotangentBundle M) : ℝ := by
  classical
  exact if h : q ∈ puncturedCotangent ∧ dualEnergy g hn q = 0 then
    globalCrossingEnergy r g hg hn hs hL S hC ⟨q, h⟩ else 1

private theorem crossingEnergyTrace_eq (r : Metric (M := M)) (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) (S : Set M) (hC : RegularCauchySliceProperty g S)
    (q : CotangentBundle M) (hq : q ∈ puncturedCotangent) (hzero : dualEnergy g hn q = 0) :
    crossingEnergyTrace r g hg hn hs hL S hC q = globalCrossingEnergy r g hg hn hs hL S hC ⟨q, hq, hzero⟩ := by
  classical
  exact dif_pos ⟨hq, hzero⟩

/-- The original crossing norm extends as a positive smooth homogeneous energy,
and its actual Hamilton derivative vanishes on the entire punctured null cone. -/
theorem exists_smooth_actualCrossing_firstIntegral [SecondCountableTopology M]
    (r : Metric (M := M)) (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) (S : Set M) (hC : RegularCauchySliceProperty g S)
    (hS : SmoothSpacelikeSlice g S) :
    ∃ E : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ E puncturedCotangent ∧
      (∀ p ∈ puncturedCotangent, 0 < E p) ∧
      (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), E (cotangentScale t p) = t * E p) ∧
      (∀ p (hp : p ∈ puncturedCotangent) (hzero : dualEnergy g hn p = 0),
        E p = globalCrossingEnergy r g hg hn hs hL S hC ⟨p, hp, hzero⟩) ∧
      (∀ p ∈ puncturedCotangent, dualEnergy g hn p = 0 → actualHamiltonDerivative g E p = 0) := by
  let e := crossingEnergyTrace r g hg hn hs hL S hC
  let N := cotangentUnitNull r g hn
  have hEeq (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) (hzero : dualEnergy g hn p = 0) :
      e p = globalCrossingEnergy r g hg hn hs hL S hC ⟨p, hp, hzero⟩ :=
    crossingEnergyTrace_eq r g hg hn hs hL S hC p hp hzero
  have he : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ e N := by
    intro p hp
    have hpp := cotangentUnitNull_covector_ne_zero r g hn hp
    obtain ⟨F, hF, hEq⟩ := exists_smooth_actualCrossingEnergy_germ r g hg hn hs hL S hC hS p hpp hp.2
    have hLocal : e =ᶠ[𝓝[N] p] F := by
      filter_upwards [hEq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q heq hq
      have hpq := cotangentUnitNull_covector_ne_zero r g hn hq
      exact (hEeq q hpq hq.2).trans (heq hpq hq.2).symm
    exact hF.contMDiffWithinAt.congr_of_eventuallyEq_of_mem hLocal hp
  have hepos (p : CotangentBundle M) (hp : p ∈ N) : 0 < e p := by
    rw [hEeq p (cotangentUnitNull_covector_ne_zero r g hn hp) hp.2]
    exact globalCrossingEnergy_pos r g hg hn hs hL S hC _
  have hehom (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) (hzero : dualEnergy g hn p = 0)
      (a : ℝ) (ha : 0 < a) : e (cotangentScale a p) = a * e p := by
    let z : PuncturedNullCotangent g hn := ⟨p, hp, hzero⟩
    let w := positiveScaleNullPhase g hn z a ha
    calc
      e (cotangentScale a p) = globalCrossingEnergy r g hg hn hs hL S hC w :=
        hEeq _ w.property.1 w.property.2
      _ = a * globalCrossingEnergy r g hg hn hs hL S hC z :=
        globalCrossingEnergy_positiveScale r g hg hn hs hL S hC z a ha
      _ = a * e p := by rw [hEeq p hp hzero]
  obtain ⟨E, hE, hEpos, hEhom, hEN⟩ := exists_positive_degreeOne_energy_extension r g hg hn hs e he hepos
  have hSame (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) (hzero : dualEnergy g hn p = 0) :
      E p = globalCrossingEnergy r g hg hn hs hL S hC ⟨p, hp, hzero⟩ :=
    (eq_of_positive_homogeneous_of_unitNull_trace r g hn e E hehom hEhom hEN hp hzero).trans (hEeq p hp hzero)
  refine ⟨E, hE, hEpos, hEhom, hSame, ?_⟩
  intro p hp hzero
  let z : PuncturedNullCotangent g hn := ⟨p, hp, hzero⟩
  let A := maximalPuncturedTrajectory g hg hn hs p hp
  have hmax (B : CanonicalTrajectory g p) : B.domain ⊆ A.domain :=
    (maximalPuncturedTrajectory_spec g hg hn hs p hp B).1
  have hConst : E ∘ A.curve =ᶠ[𝓝 (0 : ℝ)] fun _ => E p := by
    filter_upwards [A.domain_open.mem_nhds A.zero_mem] with t ht
    let w := nullPhaseAt g hg hn hs z A t ht
    calc
      (E ∘ A.curve) t = globalCrossingEnergy r g hg hn hs hL S hC w :=
        hSame _ w.property.1 w.property.2
      _ = globalCrossingEnergy r g hg hn hs hL S hC z :=
        globalCrossingEnergy_along_maximal r g hg hn hs hL S hC z A hmax t ht
      _ = E p := (hSame p hp hzero).symm
  have hA₀ : A.curve 0 ∈ puncturedCotangent := A.initial.symm ▸ hp
  have hODE := hasDerivAt_testAlong_canonicalTrajectory g hg hn hs A A.zero_mem hA₀ E hE
  rw [A.initial] at hODE
  exact hODE.unique ((hasDerivAt_const (0 : ℝ) (E p)).congr_of_eventuallyEq hConst)

end Burnett.Geometry.CotangentHamiltonInitialFamily
