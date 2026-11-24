import Burnett.Geometry.BasisFrame
import Burnett.Geometry.InverseField
import Burnett.Geometry.ManifoldBilinear

/-! The pointwise signature of the covariant metric supplies a Lorentz frame
for the inverse matrix computed in an actual chart. -/

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.ManifoldBilinear

open Bundle Module Set Burnett.RicciSymbol
open ConnectionDifference InverseField ManifoldMetric ManifoldMetricTransition
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- Signature `(-,+,+,+)` in the tangent fibers of the original bilinear field. -/
def HasLorentzSignature (B : Field (M := M)) : Prop :=
  ∀ x : M, ∃ b : Basis Index ℝ (TangentSpace Model x),
    ∀ i j, B x (b i) (b j) = TensorFrame.standardInverse i j

private def linearFiberForm (B : Field (M := M)) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace Model x) :=
  LinearMap.mk₂ ℝ (fun u v => B x u v)
    (by intros; simp [map_add]) (by intros; simp [map_smul])
    (by intros; simp [map_add]) (by intros; simp [map_smul])

theorem HasLorentzSignature.isSymmetric {B : Field (M := M)}
    (hB : HasLorentzSignature B) : IsSymmetric B := by
  intro x u v
  obtain ⟨b, hb⟩ := hB x
  let G := linearFiberForm B x
  have hG (i j : Index) : G (b i) (b j) = TensorFrame.standardInverse i j := hb i j
  have hflip : G.flip = G := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change G (b j) (b i) = G (b i) (b j)
    rw [hG, hG]
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [TensorFrame.standardInverse, hij, Ne.symm hij, if_false]
  exact congrArg (fun A : LinearMap.BilinForm ℝ (TangentSpace Model x) => A v u) hflip

theorem HasLorentzSignature.isNondegenerate {B : Field (M := M)}
    (hB : HasLorentzSignature B) : IsNondegenerate B := by
  intro x
  obtain ⟨b, hb⟩ := hB x
  exact BasisFrame.nondegenerate_of_orthonormal (linearFiberForm B x) b hb

variable [IsManifold Model ∞ M]

/-- Transport a pointwise Lorentz basis through the inverse chart tangent
trivialization and take the genuine coordinate inverse of the metric. -/
theorem chartInverse_hasLorentzFrame (B : Field (M := M)) (hB : HasLorentzSignature B)
    (c : M) {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    Nonempty (TensorFrame.LorentzFrame
      (matrixInverse (metricComponents (coordinateBilinear B c) y))) := by
  let x := (chartAt CoordinateSpace c).symm y
  have hx : x ∈ (chartAt CoordinateSpace c).source := (chartAt CoordinateSpace c).symm_mapsTo hy
  let e : TangentSpace Model x ≃L[ℝ] CoordinateSpace :=
    (trivializationAt CoordinateSpace (TangentSpace Model) c).continuousLinearEquivAt ℝ x hx
  obtain ⟨b, hb⟩ := hB x
  let b' := b.map e.toLinearEquiv
  let G := coordinateBilinear B c y
  have hG (i j : Index) : G (b' i) (b' j) = TensorFrame.standardInverse i j := by
    have hFrame (i : Index) : tangentFrame c x (b' i) = b i := by
      change e.symm (b.map e.toLinearEquiv i) = b i
      rw [Basis.map_apply]
      exact e.symm_apply_apply (b i)
    change B x (tangentFrame c x (b' i)) (tangentFrame c x (b' j)) = _
    rw [hFrame, hFrame, hb]
  have hn := coordinateBilinear_nondegenerate B hB.isNondegenerate c hy
  have hs := coordinateBilinear_symmetric B hB.isSymmetric c y
  change Nonempty (TensorFrame.LorentzFrame
    (matrixInverse (FiberMetric.covariant G coordinateBasis)))
  rw [matrixInverse_covariant G hn hs coordinateBasis]
  exact ⟨BasisFrame.lorentzFrame G hn coordinateBasis b' hG⟩

end Burnett.Geometry.ManifoldBilinear
