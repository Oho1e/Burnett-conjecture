import Burnett.Geometry.Cotangent.CosphereMeasure
import Burnett.Geometry.Cotangent.RadialExtension
import Burnett.Counterexamples.Bianchi.UnitNormalization

/-! The genuine negative radial map on the auxiliary unit cosphere. -/

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.UnitCosphere

open Function MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension (puncturedCotangent)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Reflection is the actual fiber scaling by `-1`, restricted to the unit bundle. -/
def antipode (r : Metric (M := M)) (p : Cosphere r) : Cosphere r :=
  ⟨cotangentScale (-1) p.val, by
    change dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) (cotangentScale (-1) p.val) = 1
    have hp : dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) p.val = 1 := p.property
    rw [dualEnergy_cotangentScale, hp]
    norm_num⟩

theorem antipode_val (r : Metric (M := M)) (p : Cosphere r) :
    (antipode r p).val = cotangentScale (-1) p.val := rfl

theorem projection_antipode (r : Metric (M := M)) (p : Cosphere r) :
    projection (antipode r p) = projection p := rfl

theorem antipode_involutive (r : Metric (M := M)) : Involutive (antipode r) := by
  intro p
  apply Subtype.ext
  simp only [antipode_val, CotangentAngularExtension.cotangentScale_mul, neg_mul_neg,
    one_mul, CotangentAngularExtension.cotangentScale_one]

theorem continuous_antipode (r : Metric (M := M)) : Continuous (antipode r) :=
  (continuous_cotangentScale.comp (continuous_const.prodMk continuous_subtype_val)).subtype_mk _

def antipodeHomeomorph (r : Metric (M := M)) : Cosphere r ≃ₜ Cosphere r where
  toFun := antipode r
  invFun := antipode r
  left_inv := antipode_involutive r
  right_inv := antipode_involutive r
  continuous_toFun := continuous_antipode r
  continuous_invFun := continuous_antipode r

theorem measurableEmbedding_antipode (r : Metric (M := M)) : MeasurableEmbedding (antipode r) :=
  (antipodeHomeomorph r).measurableEmbedding

theorem hamiltonian_antipode (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (p : Cosphere r) :
    hamiltonian B hn (antipode r p) = hamiltonian B hn p := by
  rw [hamiltonian, antipode_val, dualEnergy_cotangentScale, hamiltonian]
  norm_num

theorem antipode_preimage_null (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) :
    antipode r ⁻¹' {p | hamiltonian B hn p = 0} = {p : Cosphere r | hamiltonian B hn p = 0} := by
  ext p
  change hamiltonian B hn (antipode r p) = 0 ↔ hamiltonian B hn p = 0
  rw [hamiltonian_antipode]

theorem coe_mem_punctured (r : Metric (M := M)) (p : Cosphere r) : p.val ∈ puncturedCotangent :=
  CotangentUnitNormalization.unitShell_punctured r p.property

end Burnett.Geometry.UnitCosphere
