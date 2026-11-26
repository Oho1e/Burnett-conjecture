import Burnett.Geometry.ContravariantTensor
import Burnett.Geometry.Cotangent.RadialExtension

set_option autoImplicit false
set_option maxHeartbeats 4700000

noncomputable section

namespace Burnett.Geometry.ContravariantTensor

open Set Filter
open scoped BigOperators ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.UnitNullAngular (Phase)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Evaluation of the tensor on two copies of the actual cotangent variable
is a smooth function on the entire cotangent bundle. -/
theorem contMDiff_intrinsicTensorPhase (Q : ContravariantTwoTensor M) (hQ : IsSmoothContravariant Q) :
    ContMDiff CotangentModelWithCorners 𝓘(ℝ) ∞ (intrinsicTensorPhase Q) := by
  intro p
  let c := p.1
  have hp : p ∈ cotangentSource c := mem_chart_source CoordinateSpace c
  let z := cotangentChart c p
  have hz : z ∈ phaseTarget c := cotangentChart_mapsTo c hp
  let f (w : Phase) : ℝ := ∑ i, ∑ j, contravariantComponents Q c w.1 i j * (w.2 i * w.2 j)
  have hFin (i : Index) : ContDiff ℝ ∞ (fun w : Phase => w.2 i) := contDiff_pi.mp contDiff_snd i
  have hf : ContDiffOn ℝ ∞ f (phaseTarget c) := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact ((hQ c i j).comp contDiff_fst.contDiffOn (fun _ hw => hw.1)).mul
      ((hFin i).contDiffOn.mul (hFin j).contDiffOn)
  have hSmooth : ContMDiffAt CoordinatePhaseModel 𝓘(ℝ) ∞ f z := by
    simpa only [CoordinatePhaseModel, Model, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod] using
      (hf.contDiffAt ((isOpen_phaseTarget c).mem_nhds hz)).contMDiffAt
  have hComp : ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞ (f ∘ cotangentChart c) p :=
    hSmooth.comp p
      ((contMDiffOn_cotangentChart c).contMDiffAt ((isOpen_cotangentSource c).mem_nhds hp))
  have hEq : intrinsicTensorPhase Q =ᶠ[𝓝 p] f ∘ cotangentChart c := by
    filter_upwards [(isOpen_cotangentSource c).mem_nhds hp] with q hq
    exact intrinsicTensorPhase_eq_components Q c q hq
  exact hEq.contMDiffAt_iff.mpr hComp

theorem intrinsicTensorPhase_cotangentScale (Q : ContravariantTwoTensor M) (p : CotangentBundle M) (a : ℝ) :
    intrinsicTensorPhase Q (cotangentScale a p) = a^2 * intrinsicTensorPhase Q p := by
  obtain ⟨x, ξ⟩ := p
  change Q x (a • ξ.toLinearMap) (a • ξ.toLinearMap) = a ^ 2 * Q x ξ.toLinearMap ξ.toLinearMap
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, pow_two, mul_assoc]

theorem intrinsicTensorPhase_tsupport (Q : ContravariantTwoTensor M) :
    tsupport (intrinsicTensorPhase Q) ⊆ (fun p => p.1) ⁻¹' closure {x | Q x ≠ 0} := by
  apply closure_minimal _ (isClosed_closure.preimage continuous_cotangent_projection)
  intro p h
  apply subset_closure
  intro hQ
  exact h (by simp [intrinsicTensorPhase, hQ])

end Burnett.Geometry.ContravariantTensor
