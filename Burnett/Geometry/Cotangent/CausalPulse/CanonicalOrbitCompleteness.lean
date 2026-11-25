import Burnett.Geometry.Cotangent.CausalPulse.AffineEndSubtype
import Burnett.Geometry.Cotangent.CausalPulse.CanonicalPulseFromTime

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.Geometry.CausalOrbitPulse

open Set Filter Bundle
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonCauchySlice Burnett.Geometry.CotangentHamiltonMaximalCurve
open Burnett.Geometry.CotangentHamiltonInitialFamily Burnett.Geometry.CotangentHamiltonAffineReparam
open Burnett.Geometry.CotangentHamiltonTimeReversal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

/-- The base of the actual maximal Hamiltonian trajectory is continuously
differentiable on its actual open affine domain. -/
theorem maximalPuncturedTrajectory_contMDiffOn_base (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (p : CotangentBundle M) (hp : p ∈ puncturedCotangent) :
    let A := maximalPuncturedTrajectory g hg hn hs p hp
    ContMDiffOn 𝓘(ℝ) Model 1 (fun t => (A.curve t).1) A.domain := by
  intro A
  let F := maximalPuncturedFlow g hg hn hs
  let L : ℝ → CotangentBundle M × ℝ := fun t => (p, t)
  have hL : ContMDiff 𝓘(ℝ) (CotangentModelWithCorners.prod 𝓘(ℝ)) ∞ L :=
    contMDiff_const.prodMk contMDiff_id
  have hF : ContMDiffOn 𝓘(ℝ) CotangentModelWithCorners ∞ (F ∘ L) A.domain :=
    (maximalPuncturedFlow_jointSmooth g hg hn hs).2.comp hL.contMDiffOn (fun _ ht => ⟨hp, ht⟩)
  have hProj : ContMDiff CotangentModelWithCorners Model ∞ (fun z : CotangentBundle M => z.1) :=
    contMDiff_proj (𝕜 := ℝ) (IB := Model) (n := ∞) (CotangentFiber (M := M))
  refine ((hProj.comp_contMDiffOn hF).of_le (by simp)).congr ?_
  intro t _
  exact congrArg (fun p : CotangentBundle M => p.1)
    (maximalPuncturedFlow_eq_curve g hg hn hs p hp t).symm

/-- A time that takes every real value on two-ended regular causal paths
does so on the true maximal nonzero null Hamilton trajectories. -/
theorem hasCompleteNullTime_of_complete_regular_causal_paths
    (g : Field (M := M)) (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (T : M → ℝ)
    (hPath : ∀ (γ : ℝ → M) (I : Set ℝ), IsOpen I → I.OrdConnected →
      ∀ [Nonempty I] [IsCountablyGenerated (atTop : Filter I)] [IsCountablyGenerated (atBot : Filter I)],
      ContMDiffOn 𝓘(ℝ) Model 1 γ I → RegularCausalOn g γ I →
      (∀ x : M, ¬ Tendsto (fun t : I => γ t) atBot (𝓝 x)) →
      (∀ x : M, ¬ Tendsto (fun t : I => γ t) atTop (𝓝 x)) →
      (MonotoneOn (T ∘ γ) I ∨ AntitoneOn (T ∘ γ) I) ∧ SurjOn (T ∘ γ) I univ) :
    HasCompleteNullTime T g hg hL.isNondegenerate hL.isSymmetric := by
  let hn := hL.isNondegenerate
  let hs := hL.isSymmetric
  intro z
  let A := maximalPuncturedTrajectory g hg hn hs z.val z.property.1
  let γ : ℝ → M := fun t => (A.curve t).1
  have hA : ∀ C : CanonicalTrajectory g z.val, C.domain ⊆ A.domain :=
    fun C => (maximalPuncturedTrajectory_spec g hg hn hs z.val z.property.1 C).1
  have hIne : A.domain.Nonempty := ⟨0, A.zero_mem⟩
  letI : Nonempty A.domain := hIne.to_subtype
  letI : IsCountablyGenerated (atTop : Filter A.domain) :=
    atTop_isCountablyGenerated_open_interval A.domain_open A.domain_interval hIne
  letI : IsCountablyGenerated (atBot : Filter A.domain) :=
    atBot_isCountablyGenerated_open_interval A.domain_open A.domain_interval hIne
  have hNoLim (x : M) := maximal_no_base_limit_at_affine_ends g hg hn hs hL A
    z.property.1 z.property.2 hA x
  have hLeft (x : M) : ¬ Tendsto (fun t : A.domain => γ t) atBot (𝓝 x) := by
    intro h
    apply (hNoLim x).1
    change Tendsto γ (leftAffineEndFilter A.domain) (𝓝 x)
    rw [← map_atBot_coe_eq_leftAffineEnd A.domain_open A.domain_interval hIne]
    exact h
  have hRight (x : M) : ¬ Tendsto (fun t : A.domain => γ t) atTop (𝓝 x) := by
    intro h
    apply (hNoLim x).2
    change Tendsto γ (CotangentHamiltonAffineExtension.rightAffineEndFilter A.domain) (𝓝 x)
    rw [← map_atTop_coe_eq_rightAffineEnd A.domain_open A.domain_interval hIne]
    exact h
  exact hPath γ A.domain A.domain_open A.domain_interval
    (maximalPuncturedTrajectory_contMDiffOn_base g hg hn hs z.val z.property.1)
    (canonicalTrajectory_regularCausalOn_base g hg hn hs A z.property.1 z.property.2) hLeft hRight

end Burnett.Geometry.CausalOrbitPulse
