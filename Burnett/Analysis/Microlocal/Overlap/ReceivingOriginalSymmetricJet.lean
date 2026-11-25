import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetSymmetricProjection
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartCovariantGradient

/-! The original covariant input lies in the symmetric jet fiber in every receiving chart. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 4800000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set Filter Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart BackgroundConnection
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeCovariantGradientSchwartz
  fixedVolumeCovariantGradientSchwartz_apply)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The actual fixed covariant jet of a symmetric field is symmetric in its last two slots. -/
theorem fixedCovariantJet_symmetric (R H : Field (M := M)) (hH : IsSymmetric H)
    (c : AtlasChart M) (x : E) (a b d : Index) :
    fixedCovariantJet R H c x a b d = fixedCovariantJet R H c x a d b := by
  have hMetric (x : E) : IsSymmetricTensor (metricComponents (fixedForm H c) x) := by
    intro i j
    change H (c.chart.symm x) _ _ = H (c.chart.symm x) _ _
    exact hH _ _ _
  have hDerivative := coordinateJet_symmetric (metricComponents (fixedForm H c)) x (Eventually.of_forall hMetric) a
  let Γ := computedConnection (fixedForm R c) x
  let J := metricComponents (fixedForm H c) x
  unfold fixedCovariantJet covariantJet
  change
    coordinateJet (metricComponents (fixedForm H c)) x a b d - (∑ e, Γ e a b * J e d) -
      ∑ e, Γ e a d * J b e =
    coordinateJet (metricComponents (fixedForm H c)) x a d b - (∑ e, Γ e a d * J e b) -
      ∑ e, Γ e a b * J d e
  rw [hDerivative b d]
  have hbd : (∑ e, Γ e a d * J b e) = ∑ e, Γ e a d * J e b :=
    Finset.sum_congr rfl (fun e _ => congrArg (Γ e a d * ·) (hMetric x b e))
  have hdb : (∑ e, Γ e a b * J d e) = ∑ e, Γ e a b * J e d :=
    Finset.sum_congr rfl (fun e _ => congrArg (Γ e a b * ·) (hMetric x d e))
  rw [hbd, hdb, sub_right_comm]

variable [IsManifold Model ∞ M] [SecondCountableTopology M]

/-- The actual original half-density jet is already symmetric in its tensor
slots, including its zero extension. -/
theorem fixedVolumeCovariantGradientSchwartz_pairSwap
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsg : ∀ n, IsSymmetric (g n))
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (n : ℕ) (i : JetSlot) :
    fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n (jetPairSwap i) =
      fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i := by
  have hS : IsSymmetric (fun x => g n x - B x) := by
    intro x y z
    change g n x y z - B x y z = g n x z y - B x z y
    rw [hsg n x y z, hsB x y z]
  ext x
  simp only [fixedVolumeCovariantGradientSchwartz_apply]
  exact congrArg (fun a : ℝ => ((((χ : E → ℝ) x * Burnett.Microlocal.AtlasVolumeGradient.fixedHalfDensity B c x) *
    a : ℝ) : ℂ)) (fixedCovariantJet_symmetric r.inner (fun x => g n x - B x) hS c x i.1 i.2.2 i.2.1)

/-- In coordinates the canonical fiber projection averages just the
original slot and its last-pair interchange. -/
theorem jetFiberCoordinates_projectComplexSymmetricJet {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis Index ℝ V) (F : ComplexCovariantJet V) (i : JetSlot) :
    jetFiberCoordinates b (projectComplexSymmetricJet V F : ComplexCovariantJet V) i =
      (2 : ℂ)⁻¹ * (jetFiberCoordinates b F i + jetFiberCoordinates b F (jetPairSwap i)) := by
  change jetFiberCoordinates b ((2 : ℂ)⁻¹ • (F + swapComplexCovariantJet V F)) i = _
  rw [map_smul, map_add, Pi.smul_apply, Pi.add_apply, jetFiberCoordinates_swap, smul_eq_mul]

end Burnett.Microlocal.Overlap
