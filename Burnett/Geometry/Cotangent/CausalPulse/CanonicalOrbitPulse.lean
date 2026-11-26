import Burnett.Geometry.Cotangent.CausalPulse.CausalOrbitPulse
import Burnett.Geometry.Cotangent.MaximalCanonicalFlowSmoothness

set_option autoImplicit false
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.Geometry.CausalOrbitPulse

open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonCrossingEnergy Burnett.Geometry.CotangentHamiltonMaximalCurve
open Burnett.Geometry.CotangentHamiltonInitialFamily

private theorem pulseIntegral_congr {X : Type*} (f : X → ℝ) {γ β : ℝ → X} {I : Set ℝ}
    (h : EqOn γ β I) : pulseIntegral f γ I = pulseIntegral f β I := by
  unfold pulseIntegral
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    by_cases ht : t ∈ I
    · simp only [indicator_of_mem ht, Function.comp_apply, h ht]
    · simp only [indicator_of_notMem ht]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

/-- Affine pulse mass along the actual maximal null Hamilton trajectory. -/
def canonicalPulseMass (f : M → ℝ) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (z : PuncturedNullCotangent g hn) : ℝ :=
  let A := maximalPuncturedTrajectory g hg hn hs z.val z.property.1
  pulseIntegral f (fun t => (A.curve t).1) A.domain

theorem canonicalPulseMass_eq_on_maximal (f : M → ℝ) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (z : PuncturedNullCotangent g hn)
    (A : CanonicalTrajectory g z.val) (hmax : ∀ D : CanonicalTrajectory g z.val, D.domain ⊆ A.domain) :
    canonicalPulseMass f g hg hn hs z = pulseIntegral f (fun t => (A.curve t).1) A.domain := by
  let C := maximalPuncturedTrajectory g hg hn hs z.val z.property.1
  have hspec := maximalPuncturedTrajectory_spec g hg hn hs z.val z.property.1 A
  have hDom : C.domain = A.domain := Subset.antisymm (hmax C) hspec.1
  change pulseIntegral f (fun t => (C.curve t).1) C.domain = _
  rw [hDom]
  exact pulseIntegral_congr f fun _ ht => congrArg (fun p : CotangentBundle M => p.1) (hspec.2 ht)

theorem canonicalPulseMass_invariant (f : M → ℝ) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (z : PuncturedNullCotangent g hn)
    (A : CanonicalTrajectory g z.val) (hmax : ∀ D : CanonicalTrajectory g z.val, D.domain ⊆ A.domain)
    (b : ℝ) (hb : b ∈ A.domain) :
    canonicalPulseMass f g hg hn hs (nullPhaseAt g hg hn hs z A b hb) = canonicalPulseMass f g hg hn hs z := by
  let w := nullPhaseAt g hg hn hs z A b hb
  let B : CanonicalTrajectory g w.val := CanonicalTrajectory.shift g hg hn hs A b hb
  rw [canonicalPulseMass_eq_on_maximal f g hg hn hs w B (shift_domain_maximal g hg hn hs A hmax b hb),
    canonicalPulseMass_eq_on_maximal f g hg hn hs z A hmax]
  exact pulseIntegral_translate f (fun t => (A.curve t).1) A.domain b

theorem canonicalPulseMass_positiveScale (f : M → ℝ) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (z : PuncturedNullCotangent g hn)
    (a : ℝ) (ha : 0 < a) :
    canonicalPulseMass f g hg hn hs (positiveScaleNullPhase g hn z a ha) = a⁻¹ * canonicalPulseMass f g hg hn hs z := by
  let A := maximalPuncturedTrajectory g hg hn hs z.val z.property.1
  let hmax (D : CanonicalTrajectory g z.val) : D.domain ⊆ A.domain :=
    (maximalPuncturedTrajectory_spec g hg hn hs z.val z.property.1 D).1
  let w := positiveScaleNullPhase g hn z a ha
  let B : CanonicalTrajectory g w.val := CanonicalTrajectory.positiveScale g hg hn hs A a ha
  rw [canonicalPulseMass_eq_on_maximal f g hg hn hs w B (positiveScale_domain_maximal g hg hn hs A hmax a ha),
    canonicalPulseMass_eq_on_maximal f g hg hn hs z A hmax]
  exact pulseIntegral_positiveScale f (fun t => (A.curve t).1) A.domain ha

def canonicalPulseEnergy (f : M → ℝ) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (z : PuncturedNullCotangent g hn) : ℝ :=
  (canonicalPulseMass f g hg hn hs z)⁻¹

theorem canonicalPulseEnergy_invariant (f : M → ℝ) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (z : PuncturedNullCotangent g hn)
    (A : CanonicalTrajectory g z.val) (hmax : ∀ D : CanonicalTrajectory g z.val, D.domain ⊆ A.domain)
    (b : ℝ) (hb : b ∈ A.domain) :
    canonicalPulseEnergy f g hg hn hs (nullPhaseAt g hg hn hs z A b hb) = canonicalPulseEnergy f g hg hn hs z :=
  congrArg Inv.inv (canonicalPulseMass_invariant f g hg hn hs z A hmax b hb)

theorem canonicalPulseEnergy_positiveScale (f : M → ℝ) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (z : PuncturedNullCotangent g hn) (a : ℝ) (ha : 0 < a) :
    canonicalPulseEnergy f g hg hn hs (positiveScaleNullPhase g hn z a ha) = a * canonicalPulseEnergy f g hg hn hs z := by
  rw [canonicalPulseEnergy, canonicalPulseMass_positiveScale f g hg hn hs z a ha, canonicalPulseEnergy,
    mul_inv_rev, inv_inv, mul_comm]

end Burnett.Geometry.CausalOrbitPulse
