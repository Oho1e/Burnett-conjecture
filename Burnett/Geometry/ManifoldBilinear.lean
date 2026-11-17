import Burnett.Geometry.ManifoldMetricTransition

/-!
# Global bilinear sections supply actual chart data

A field is a genuine continuous bilinear map on each actual tangent fiber.
IsSmooth is ContMDiff of its total-space section in the nested Hom bundle;
it contains no coordinate regularity conclusions. Chart smoothness follows
by evaluating this section on the already proved smooth tangent frames.
Symmetry and nondegeneracy are assumptions on the original fiber forms,
and their chart versions are derived using actual frame bijectivity.

This is general support for the symmetric nondegenerate fields underlying
Lorentz metrics. Lorentz signature and time orientation are not defined or
instantiated by this module. No physical tensor norm is identified with the
curried Hom norm.
-/

noncomputable section

open Bundle Set LinearMap
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition

namespace Burnett.Geometry.ManifoldBilinear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

abbrev Field := ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ

def IsSmooth (B : Field (M := M)) : Prop :=
  ContMDiff Model (Model.prod 𝓘(ℝ, CoordinateSpace →L[ℝ] CoordinateSpace →L[ℝ] ℝ)) ∞
    (fun m => TotalSpace.mk' (CoordinateSpace →L[ℝ] CoordinateSpace →L[ℝ] ℝ) m (B m))

theorem contMDiffOn_frameBilinear_apply (B : Field (M := M)) (hB : IsSmooth B)
    (c : M) (u v : CoordinateSpace) :
    ContMDiffOn Model 𝓘(ℝ, ℝ) ∞ (fun m => frameBilinear B c m u v)
      (chartAt CoordinateSpace c).source := by
  have hu := ManifoldMetric.contMDiffOn_frame (M := M) c u
  have hv := ManifoldMetric.contMDiffOn_frame (M := M) c v
  have h := hB.contMDiffOn.clm_bundle_apply₂ hu hv
  intro m hm
  have hh := h m hm
  simp only [contMDiffWithinAt_totalSpace] at hh
  exact hh.2

theorem contDiffOn_coordinateBilinear_apply (B : Field (M := M)) (hB : IsSmooth B)
    (c : M) (u v : CoordinateSpace) :
    ContDiffOn ℝ ∞ (fun y => coordinateBilinear B c y u v)
      (chartAt CoordinateSpace c).target := by
  exact ((contMDiffOn_frameBilinear_apply B hB c u v).comp
    contMDiffOn_chart_symm (chartAt CoordinateSpace c).symm_mapsTo).contDiffOn

theorem contDiffOn_metricComponents (B : Field (M := M)) (hB : IsSmooth B)
    (c : M) (i j : Index) :
    ContDiffOn ℝ ∞ (fun y => metricComponents (coordinateBilinear B c) y i j)
      (chartAt CoordinateSpace c).target :=
  contDiffOn_coordinateBilinear_apply B hB c (coordinateBasis i) (coordinateBasis j)


def IsSymmetric (B : Field (M := M)) : Prop :=
  ∀ m u v, B m u v = B m v u

def IsNondegenerate (B : Field (M := M)) : Prop :=
  ∀ m u, (∀ v, B m u v = 0) → u = 0

theorem tangentFrame_surjective (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    Function.Surjective (tangentFrame c m) := by
  let e := trivializationAt CoordinateSpace (TangentSpace Model) c
  exact (e.continuousLinearEquivAt ℝ m hm).symm.surjective

theorem coordinateBilinear_symmetric (B : Field (M := M)) (hB : IsSymmetric B)
    (c : M) (y : CoordinateSpace) : (coordinateBilinear B c y).IsSymm :=
  ⟨fun u v => hB ((chartAt CoordinateSpace c).symm y)
    (tangentFrame c ((chartAt CoordinateSpace c).symm y) u)
    (tangentFrame c ((chartAt CoordinateSpace c).symm y) v)⟩

theorem coordinateBilinear_nondegenerate (B : Field (M := M)) (hB : IsNondegenerate B)
    (c : M) {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    (coordinateBilinear B c y).Nondegenerate := by
  let m := (chartAt CoordinateSpace c).symm y
  have hm : m ∈ (chartAt CoordinateSpace c).source := (chartAt CoordinateSpace c).symm_mapsTo hy
  intro u hu
  apply ManifoldMetric.tangentFrame_injective c m hm
  have hz : tangentFrame c m u = 0 := hB m _ (fun v => by
    obtain ⟨w, rfl⟩ := tangentFrame_surjective c m hm v
    exact hu w)
  simpa only [map_zero] using hz

theorem contDiffOn_metricComponents_one (B : Field (M := M)) (hB : IsSmooth B)
    (c : M) (i j : Index) :
    ContDiffOn ℝ 1 (fun y => metricComponents (coordinateBilinear B c) y i j)
      (chartAt CoordinateSpace c).target :=
  (contDiffOn_metricComponents B hB c i j).of_le (by norm_num)

theorem continuousOn_components (B : Field (M := M)) (hB : IsSmooth B) (c : M) :
    ContinuousOn (metricComponents (coordinateBilinear B c)) (chartAt CoordinateSpace c).target := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact (contDiffOn_metricComponents B hB c i j).continuousOn

theorem eventually_coordinateBilinear_symmetric (B : Field (M := M)) (hB : IsSymmetric B)
    (c : M) (x : CoordinateSpace) :
    ∀ᶠ y in 𝓝 x, (coordinateBilinear B c y).IsSymm :=
  Filter.Eventually.of_forall (coordinateBilinear_symmetric B hB c)

theorem isSmooth_inner (r : Metric (M := M)) : IsSmooth r.inner := r.contMDiff

end Burnett.Geometry.ManifoldBilinear
