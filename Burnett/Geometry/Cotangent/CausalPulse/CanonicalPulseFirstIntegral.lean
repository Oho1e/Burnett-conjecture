import Burnett.Geometry.Cotangent.CausalPulse.CanonicalPulseFromTime
import Burnett.Geometry.Cotangent.CanonicalTestDerivative
import Burnett.Geometry.Cotangent.ActualWeightedLiftMoments
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false
set_option maxHeartbeats 5900000

noncomputable section

namespace Burnett.Geometry.CausalOrbitPulse

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonInitialFamily Burnett.Geometry.CotangentHamiltonCrossingEnergy
open Burnett.Geometry.CotangentHamiltonMaximalCurve
open Burnett.Geometry.ActualTestLift

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M]

private def pulseEnergyTrace (f : M → ℝ) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (p : CotangentBundle M) : ℝ := by
  classical
  exact if h : p ∈ puncturedCotangent ∧ dualEnergy g hn p = 0 then
    canonicalPulseEnergy f g hg hn hs ⟨p, h⟩ else 1

/-- A continuous Cauchy time on the actual null orbits suffices to construct
a positive homogeneous smooth energy with zero Hamilton derivative there. -/
theorem exists_smooth_canonicalPulseFirstIntegral (T : M → ℝ) (hTc : Continuous T)
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hT : HasCompleteNullTime T g hg hn hs) :
    ∃ E : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ E puncturedCotangent ∧
      (∀ p ∈ puncturedCotangent, 0 < E p) ∧
      (∀ p ∈ puncturedCotangent, ∀ a > (0 : ℝ), E (cotangentScale a p) = a * E p) ∧
      (∀ p ∈ puncturedCotangent, dualEnergy g hn p = 0 → actualHamiltonDerivative g E p = 0) := by
  obtain ⟨f, hf, hNonneg, hPos⟩ := exists_smooth_timeStripPulse T hTc (-1) 1
  have hSupp : Function.support f = T ⁻¹' Ioo (-1) 1 := by
    ext x
    change f x ≠ 0 ↔ T x ∈ Ioo (-1) 1
    exact ⟨fun h => (hPos x).mp (lt_of_le_of_ne (hNonneg x) h.symm), fun h => ((hPos x).mpr h).ne'⟩
  let e := pulseEnergyTrace f g hg hn hs
  let N := cotangentUnitNull r g hn
  have heq (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) (hzero : dualEnergy g hn p = 0) :
      e p = canonicalPulseEnergy f g hg hn hs ⟨p, hp, hzero⟩ := dif_pos ⟨hp, hzero⟩
  have hMass (z : PuncturedNullCotangent g hn) : 0 < canonicalPulseMass f g hg hn hs z :=
    canonicalPulseMass_pos_of_completeNullTime T f hf.continuous hNonneg hSupp g hg hn hs hT z
  have hSmooth : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ e N := by
    intro p hp
    have hpun := cotangentUnitNull_covector_ne_zero r g hn hp
    let z : PuncturedNullCotangent g hn := ⟨p, hpun, hp.2⟩
    obtain ⟨J, hJ, hJnear⟩ := exists_smooth_canonicalPulseMass_germ T f hTc hf hSupp g hg hn hs hT z
    have hJp : J p = canonicalPulseMass f g hg hn hs z := (mem_of_mem_nhds hJnear) hpun hp.2
    have hJne : J p ≠ 0 := by rw [hJp]; exact (hMass z).ne'
    have hLocal : e =ᶠ[𝓝[N] p] (fun q => (J q)⁻¹) := by
      filter_upwards [hJnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqN
      have hqpun := cotangentUnitNull_covector_ne_zero r g hn hqN
      exact (heq q hqpun hqN.2).trans (congrArg Inv.inv (hq hqpun hqN.2)).symm
    exact (hJ.inv₀ hJne).contMDiffWithinAt.congr_of_eventuallyEq_of_mem hLocal hp
  have hepos (p : CotangentBundle M) (hp : p ∈ N) : 0 < e p := by
    rw [heq p (cotangentUnitNull_covector_ne_zero r g hn hp) hp.2]
    exact inv_pos.mpr (hMass _)
  have hehom (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) (hzero : dualEnergy g hn p = 0)
      (a : ℝ) (ha : 0 < a) : e (cotangentScale a p) = a * e p := by
    let z : PuncturedNullCotangent g hn := ⟨p, hp, hzero⟩
    let w := positiveScaleNullPhase g hn z a ha
    calc
      e (cotangentScale a p) = canonicalPulseEnergy f g hg hn hs w := heq _ w.property.1 w.property.2
      _ = a * canonicalPulseEnergy f g hg hn hs z := canonicalPulseEnergy_positiveScale f g hg hn hs z a ha
      _ = a * e p := by rw [heq p hp hzero]
  obtain ⟨E, hE, hEpos, hEhom, hEN⟩ := exists_positive_degreeOne_energy_extension r g hg hn hs e hSmooth hepos
  have hAgree (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) (hzero : dualEnergy g hn p = 0) :
      E p = canonicalPulseEnergy f g hg hn hs ⟨p, hp, hzero⟩ :=
    (eq_of_positive_homogeneous_of_unitNull_trace r g hn e E hehom hEhom hEN hp hzero).trans (heq p hp hzero)
  refine ⟨E, hE, hEpos, hEhom, fun p hp hzero => ?_⟩
  let z : PuncturedNullCotangent g hn := ⟨p, hp, hzero⟩
  let A := maximalPuncturedTrajectory g hg hn hs p hp
  have hmax (B : CanonicalTrajectory g p) : B.domain ⊆ A.domain :=
    (maximalPuncturedTrajectory_spec g hg hn hs p hp B).1
  have hConst : E ∘ A.curve =ᶠ[𝓝 (0 : ℝ)] fun _ => E p := by
    filter_upwards [A.domain_open.mem_nhds A.zero_mem] with t ht
    let w := nullPhaseAt g hg hn hs z A t ht
    calc
      (E ∘ A.curve) t = canonicalPulseEnergy f g hg hn hs w := hAgree _ w.property.1 w.property.2
      _ = canonicalPulseEnergy f g hg hn hs z := canonicalPulseEnergy_invariant f g hg hn hs z A hmax t ht
      _ = E p := (hAgree p hp hzero).symm
  have hA₀ : A.curve 0 ∈ puncturedCotangent := A.initial.symm ▸ hp
  have hDeriv := hasDerivAt_testAlong_canonicalTrajectory g hg hn hs A A.zero_mem hA₀ E hE
  rw [A.initial] at hDeriv
  exact hDeriv.unique ((hasDerivAt_const (0 : ℝ) (E p)).congr_of_eventuallyEq hConst)

end Burnett.Geometry.CausalOrbitPulse
