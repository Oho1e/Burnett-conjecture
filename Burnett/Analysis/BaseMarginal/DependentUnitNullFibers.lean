import Burnett.Analysis.BaseMarginal.IntrinsicAngularPointwiseMoments
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! Positive angular measures on the actual dependent unit null fibers. -/

set_option autoImplicit false

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set Filter MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open scoped ContDiff ENNReal Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The auxiliary unit covectors over x on the background null cone. -/
def unitNullFiberSet (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (x : M) : Set (Cosphere r) :=
  {p | projection p = x ∧ hamiltonian B hn p = 0}

abbrev UnitNullFiber (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (x : M) := ↥(unitNullFiberSet r B hn x)

/-- Evaluate the covector on a tangent vector at the very same base point. -/
def unitNullFiberEval {r : Metric (M := M)} {B : Field (M := M)} {hn : IsNondegenerate B}
    {x : M} (p : UnitNullFiber r B hn x) (u : TangentSpace Model x) : ℝ :=
  p.val.val.2 (cast (congrArg (TangentSpace Model) p.property.1.symm) u)

/-- The total-space representation is the pushforward by the fiber inclusion. -/
def ambientUnitNullFiberLaw {r : Metric (M := M)} {B : Field (M := M)} {hn : IsNondegenerate B}
    (ν : ∀ x : M, Measure (UnitNullFiber r B hn x)) (x : M) : Measure (Cosphere r) :=
  (ν x).map Subtype.val

/-- A measurable family of positive fiber measures, finite almost everywhere
relative to the background geometric volume. -/
structure UnitNullFiberMeasures (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) where
  law : ∀ x : M, Measure (UnitNullFiber r B hn x)
  measurable_ambient : Measurable (ambientUnitNullFiberLaw law)
  finite_ae : ∀ᵐ x ∂ManifoldVolume.geometricMeasure B, law x univ < ⊤

/-- Reconstruct the supplied measure over the original geometric volume. -/
def UnitNullFiberMeasures.Reconstructs {r : Metric (M := M)} {B : Field (M := M)}
    {hn : IsNondegenerate B} (ν : UnitNullFiberMeasures r B hn) (μ : Measure (Cosphere r)) : Prop :=
  μ = (ManifoldVolume.geometricMeasure B).bind (ambientUnitNullFiberLaw ν.law)

/-- The reconstruction holds on each Borel set by restricting it to the actual fibers. -/
theorem UnitNullFiberMeasures.reconstructs_apply {r : Metric (M := M)} {B : Field (M := M)}
    {hn : IsNondegenerate B} {ν : UnitNullFiberMeasures r B hn} {μ : Measure (Cosphere r)}
    (h : ν.Reconstructs μ) {S : Set (Cosphere r)} (hS : MeasurableSet S) :
    μ S = ∫⁻ x, ν.law x (Subtype.val ⁻¹' S) ∂ManifoldVolume.geometricMeasure B := by
  change μ = (ManifoldVolume.geometricMeasure B).bind (ambientUnitNullFiberLaw ν.law) at h
  rw [h, Measure.bind_apply hS ν.measurable_ambient.aemeasurable]
  exact lintegral_congr fun x => Measure.map_apply measurable_subtype_coe hS

/-- One volume-conull set supports the mass and every tangent-vector moment. -/
def UnitNullFiberMeasures.HasMassAndMoments {r : Metric (M := M)} {B : Field (M := M)}
    {hn : IsNondegenerate B} (ν : UnitNullFiberMeasures r B hn) : Prop :=
  ∀ᵐ x ∂ManifoldVolume.geometricMeasure B,
    ν.law x univ = ENNReal.ofReal (auxiliaryEinsteinDensity r B hn x) ∧
    ∀ u v : TangentSpace Model x,
      let q (p : UnitNullFiber r B hn x) := unitNullFiberEval p u * unitNullFiberEval p v
      Integrable q (ν.law x) ∧ intrinsicEinstein B hn x u v = ∫ p, q p ∂ν.law x

/-- The angular measure is zero at almost every point of zero density. -/
theorem UnitNullFiberMeasures.ae_law_eq_zero_of_density_eq_zero {r : Metric (M := M)}
    {B : Field (M := M)} {hn : IsNondegenerate B} {ν : UnitNullFiberMeasures r B hn}
    (h : ν.HasMassAndMoments) :
    ∀ᵐ x ∂ManifoldVolume.geometricMeasure B, auxiliaryEinsteinDensity r B hn x = 0 → ν.law x = 0 := by
  filter_upwards [h] with x hx hZero
  exact Measure.measure_univ_eq_zero.mp (hx.1.trans (by rw [hZero, ENNReal.ofReal_zero]))

end Burnett.F08.IntrinsicBaseMarginal
