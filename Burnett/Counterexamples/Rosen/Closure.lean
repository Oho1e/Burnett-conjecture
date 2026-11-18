import Burnett.Counterexamples.Rosen.BaseTestClass
import Burnett.Counterexamples.Rosen.Auxiliary

/-!
# Rosen multiscale example

The multiscale example with its compact-set admissibility and intrinsic kinetic tests.
-/

set_option autoImplicit false

noncomputable section

noncomputable section

namespace Burnett.RosenMultiscale

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.InverseField
open Burnett.Geometry.CovariantTensorNorm
open Transport Transport.BaseTestClass
open scoped BigOperators ENNReal Topology

/-- The multiscale sequence and the full kinetic representation in each of its two charts. -/
theorem rosen_multiscale_full_example :
    (∃ B, RosenMultiscaleSequence B ∧
      ∀ (pulled : Bool) (K : Set CoordinateSpace), IsCompact K →
        K ⊆ {x | x 0 ∈ rosenExampleOpenInterval} →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
          eLpNorm (fun x => norm3 (metricComponents rosenEuclideanAuxiliary x)
            (rosenEuclideanDh pulled B n x)) ⊤ (volume.restrict K) ≤ ENNReal.ofReal C) ∧
    (∀ pulled, RosenFullKineticLimit pulled ∧
      ∀ S : rosenBaseDomain → CoordinateMetric,
        (∀ i j : Index, HasLocalSmoothBaseRepresentatives (fun x => S x i j)) → HasCompactSupport S →
        let l := fun p : rosenPhaseDomain =>
          ∑ k : Index × Index, S (phaseBase p) k.1 k.2 * p.val.2 k.1 * p.val.2 k.2
        let r := fun x : rosenBaseDomain =>
          ∑ k : Index × Index, S x k.1 k.2 * rosenLimitEinstein pulled x.val k.1 k.2 *
            Real.sqrt |(rosenLimitMetric pulled x.val).det|
        Integrable l (rosenPhaseMeasure pulled) ∧ Integrable r rosenBaseLebesgue ∧
        (∫ p, l p ∂rosenPhaseMeasure pulled) = ∫ x, r x ∂rosenBaseLebesgue) ∧
    (∀ x : Coordinate, x 0 ∈ rosenInterval → ∀ i, contractedSource Real.cos (fun _ => 0) x i = 0) ∧
    (∀ n : ℕ, eLpNorm (fun u => (deriv (rosenExamplePhase n) u)^2) ⊤
      (volume.restrict rosenInterval) ≤ ENNReal.ofReal 4) ∧
    ∀ f : ℝ → ℝ, IntegrableOn f rosenInterval →
      (∀ n : ℕ, IntegrableOn (fun u => f u * (deriv (rosenExamplePhase n) u)^2) rosenInterval) ∧
      Tendsto (fun n : ℕ => ∫ u in rosenInterval, f u * (deriv (rosenExamplePhase n) u)^2) atTop
        (𝓝 (∫ u in rosenInterval, f u)) := by
  obtain ⟨⟨B, hB⟩, hKinetic, hSource, hPhaseNorm, hPhaseLimit⟩ := rosen_multiscale_example
  refine ⟨⟨B, hB, ?_⟩, fun pulled => ⟨hKinetic pulled, intrinsic_tensor_einstein_moment pulled⟩,
    hSource, hPhaseNorm, hPhaseLimit⟩
  intro pulled K hK hspace
  exact hB.euclideanDh_eLpNorm_on_compact pulled hK hspace volume

end Burnett.RosenMultiscale
