import Burnett.Geometry.ChartVectorField

/-!
# The actual manifold scalar differential in a preferred tangent chart

The inverse and forward tangent frames are identified with the genuine
manifold derivatives of the chart and its inverse. The manifold chain
rule then identifies mfderiv f m applied to any actual tangent vector
field with the Frechet derivative of the scalar coordinate function.
Only f is assumed differentiable at the relevant point; V need not be
smooth, and no scalar transformation identity is an input.
-/

noncomputable section
namespace Burnett.Geometry.ChartDifferential
open Bundle Set
open scoped Manifold ContDiff Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ChartVectorField

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem tangentFrame_eq_mfderiv_symm (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    tangentFrame c m = mfderiv Model Model (chartAt CoordinateSpace c).symm
      (chartAt CoordinateSpace c m) := by
  simpa only [Model, mfld_simps, mfderivWithin_univ] using tangentFrame_eq_mfderivWithin c m hm

theorem fderiv_scalar_chart (f : M → ℝ) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source)
    (hf : MDifferentiableAt Model 𝓘(ℝ, ℝ) f m) (v : CoordinateSpace) :
    fderiv ℝ (f ∘ (chartAt CoordinateSpace c).symm) (chartAt CoordinateSpace c m) v =
      mfderiv Model 𝓘(ℝ, ℝ) f m (tangentFrame c m v) := by
  have hi := (mdifferentiable_chart (I := Model) c).mdifferentiableAt_symm
    ((chartAt CoordinateSpace c).mapsTo hm)
  have hc := mfderiv_comp_apply_of_eq (I := Model) (I' := Model) (I'' := 𝓘(ℝ, ℝ))
    (chartAt CoordinateSpace c m) hf hi ((chartAt CoordinateSpace c).left_inv hm) v
  rw [mfderiv_eq_fderiv, ← tangentFrame_eq_mfderiv_symm c m hm] at hc
  exact hc

theorem scalar_mfderiv_eq_chart (f : M → ℝ) (V : Field (M := M)) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source)
    (hf : MDifferentiableAt Model 𝓘(ℝ, ℝ) f m) :
    mfderiv Model 𝓘(ℝ, ℝ) f m (V m) =
      fderiv ℝ (f ∘ (chartAt CoordinateSpace c).symm) (chartAt CoordinateSpace c m)
        (frameVector V c m) := by
  rw [fderiv_scalar_chart f c m hm hf, tangentFrame_frameVector V c m hm]


theorem frameVector_eq_mfderiv_chart (V : Field (M := M)) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    frameVector V c m = mfderiv Model Model (chartAt CoordinateSpace c) m (V m) := by
  have he : (trivializationAt CoordinateSpace (TangentSpace Model) c).continuousLinearMapAt ℝ m =
      mfderiv Model Model (chartAt CoordinateSpace c) m := by
    simpa only [Model, mfld_simps] using
      TangentBundle.continuousLinearMapAt_trivializationAt (I := Model) hm
  rw [← he]
  let e := trivializationAt CoordinateSpace (TangentSpace Model) c
  change (e ⟨m, V m⟩).2 = e.continuousLinearMapAt ℝ m (V m)
  rw [e.continuousLinearMapAt_apply ℝ, e.coe_linearMapAt_of_mem hm]

theorem coordinateVector_eq_mfderiv_chart (V : Field (M := M)) (c : M)
    {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    coordinateVector V c y = mfderiv Model Model (chartAt CoordinateSpace c)
      ((chartAt CoordinateSpace c).symm y) (V ((chartAt CoordinateSpace c).symm y)) :=
  frameVector_eq_mfderiv_chart V c _ ((chartAt CoordinateSpace c).symm_mapsTo hy)

theorem scalar_mfderiv_eq_coordinate (f : M → ℝ) (V : Field (M := M)) (c : M)
    {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target)
    (hf : MDifferentiableAt Model 𝓘(ℝ, ℝ) f ((chartAt CoordinateSpace c).symm y)) :
    mfderiv Model 𝓘(ℝ, ℝ) f ((chartAt CoordinateSpace c).symm y)
        (V ((chartAt CoordinateSpace c).symm y)) =
      fderiv ℝ (f ∘ (chartAt CoordinateSpace c).symm) y (coordinateVector V c y) := by
  have h := scalar_mfderiv_eq_chart f V c ((chartAt CoordinateSpace c).symm y)
    ((chartAt CoordinateSpace c).symm_mapsTo hy) hf
  simpa only [(chartAt CoordinateSpace c).right_inv hy, coordinateVector] using h

end Burnett.Geometry.ChartDifferential
