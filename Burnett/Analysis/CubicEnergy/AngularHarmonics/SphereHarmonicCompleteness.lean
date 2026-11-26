import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicOrthogonality
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false
set_option maxHeartbeats 7500000

noncomputable section

namespace Burnett.A06

open MvPolynomial Metric MeasureTheory Set
open scoped BigOperators ENNReal

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

private def spherePolynomialRestrictionAlg : SpherePolynomial →ₐ[ℝ] C(RoundSphere3, ℝ) where
  toFun := spherePolynomialRestriction
  map_one' := by
    ext x
    change spherePolynomialValue 1 x = 1
    exact map_one _
  map_zero' := map_zero spherePolynomialRestriction
  map_mul' P Q := by
    ext x
    change spherePolynomialValue (P * Q) x = spherePolynomialValue P x * spherePolynomialValue Q x
    exact map_mul _ P Q
  map_add' := map_add spherePolynomialRestriction
  commutes' c := by
    ext x
    rw [_root_.algebraMap_apply, smul_eq_mul, mul_one]
    change spherePolynomialValue (C c) x = c
    exact eval_C _

/-- Restrictions of real four-variable polynomials are uniformly dense on
the actual round unit sphere. -/
theorem spherePolynomialRestriction_denseRange : DenseRange spherePolynomialRestriction := by
  have sep : spherePolynomialRestrictionAlg.range.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i : Fin 4, (x : RotationSpace) i ≠ (y : RotationSpace) i := by
      by_contra! h
      exact hxy (Subtype.ext (PiLp.ext h))
    let f := spherePolynomialRestrictionAlg (X i)
    refine ⟨f, ⟨f, ⟨X i, rfl⟩, rfl⟩, ?_⟩
    change spherePolynomialValue (X i) x ≠ spherePolynomialValue (X i) y
    simpa [spherePolynomialValue] using hi
  intro f
  exact ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints _ sep f

private def continuousHarmonicSpan : Submodule ℝ C(RoundSphere3, ℝ) :=
  Submodule.span ℝ (range sphereHarmonicFamily)

private theorem sphereHarmonicRestriction_mem_span (d : ℕ) (H : sphereHarmonicSubmodule d) :
    sphereHomogeneousRestriction d H.val ∈ continuousHarmonicSpan := by
  let b := sphereHarmonicPolynomialBasis d
  let F := (sphereHomogeneousRestriction d).comp (sphereHarmonicSubmodule d).subtype
  change F H ∈ continuousHarmonicSpan
  have split := congrArg F (b.sum_repr H)
  rw [map_sum] at split
  simp only [map_smul] at split
  rw [← split]
  apply Submodule.sum_mem
  intro i _
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨⟨d, i⟩, rfl⟩

private theorem spherePolynomialRestriction_radiusSquared_mul (P : SpherePolynomial) :
    spherePolynomialRestriction (radiusSquared * P) = spherePolynomialRestriction P := by
  ext x
  have hn : ‖(x : RotationSpace)‖ ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm.mp x.property, one_pow]
  rw [EuclideanSpace.norm_sq_eq] at hn
  have hn' : spherePolynomialValue radiusSquared x = 1 := by
    simpa only [Real.norm_eq_abs, sq_abs, spherePolynomialValue, radiusSquared, map_sum, map_pow,
      eval_X] using hn
  change spherePolynomialValue (radiusSquared * P) x = spherePolynomialValue P x
  rw [show spherePolynomialValue (radiusSquared * P) x =
    spherePolynomialValue radiusSquared x * spherePolynomialValue P x from map_mul _ _ _, hn', one_mul]

private theorem sphereHomogeneousRestriction_mem_span (d : ℕ) :
    ∀ P : SphereHomogeneous d, sphereHomogeneousRestriction d P ∈ continuousHarmonicSpan := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro P
    by_cases hd : d ≤ 1
    · let H : sphereHarmonicSubmodule d := ⟨P, mem_sphereHarmonicSubmodule_iff.mpr
        (polynomialLaplacian_eq_zero_of_low_degree P.property hd)⟩
      exact sphereHarmonicRestriction_mem_span d H
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 2 := ⟨d - 2, by omega⟩
      obtain ⟨⟨H, Q⟩, hp⟩ := (sphereFischerEquiv k).surjective P
      have hP : (P : SpherePolynomial) =
          ((H.val : SphereHomogeneous (k + 2)) : SpherePolynomial) + radiusSquared * Q.val := by
        rw [← hp, sphereFischerEquiv_apply]
      change spherePolynomialRestriction (P : SpherePolynomial) ∈ continuousHarmonicSpan
      rw [hP, map_add, spherePolynomialRestriction_radiusSquared_mul]
      exact continuousHarmonicSpan.add_mem (sphereHarmonicRestriction_mem_span (k + 2) H)
        (ih k (by omega) Q)

/-- Fischer decomposition and \(r^2=1\) on the sphere give a finite harmonic
expansion for the restriction of every ambient real polynomial. -/
theorem spherePolynomialRestriction_mem_harmonicSpan (P : SpherePolynomial) :
    spherePolynomialRestriction P ∈ Submodule.span ℝ (range sphereHarmonicFamily) := by
  change spherePolynomialRestriction P ∈ continuousHarmonicSpan
  rw [← sum_homogeneousComponent P, map_sum]
  apply Submodule.sum_mem
  intro d _
  exact sphereHomogeneousRestriction_mem_span d
    ⟨homogeneousComponent d P, homogeneousComponent_isHomogeneous _ _⟩

/-- The real spherical harmonics span a dense subspace of the true round-sphere
\(L²\) space. -/
theorem sphereHarmonicFamilyLp_denseSpan :
    Dense (Submodule.span ℝ (range sphereHarmonicFamilyLp) : Set RoundSphereL2) := by
  let L : C(RoundSphere3, ℝ) →L[ℝ] RoundSphereL2 :=
    ContinuousMap.toLp 2 roundSphere3Measure ℝ
  have dL : DenseRange L :=
    ContinuousMap.toLp_denseRange (α := RoundSphere3) (E := ℝ) (p := 2)
      (μ := roundSphere3Measure) ℝ (by norm_num)
  have h := dL.comp spherePolynomialRestriction_denseRange L.continuous
  apply h.mono
  rintro _ ⟨P, rfl⟩
  have mm :
      continuousHarmonicSpan.map L.toLinearMap = Submodule.span ℝ (range sphereHarmonicFamilyLp) := by
    rw [continuousHarmonicSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← mm]
  exact ⟨spherePolynomialRestriction P, spherePolynomialRestriction_mem_harmonicSpan P, rfl⟩

/-- A Hilbert basis of the actual real \(L²(S³)\), indexed by degree and its
\((d+1)^2\) real harmonics. -/
def roundSphereHarmonicHilbertBasis : HilbertBasis SphereHarmonicIndex ℝ RoundSphereL2 :=
  HilbertBasis.mk sphereHarmonicFamilyLp_orthonormal
    (Submodule.dense_iff_topologicalClosure_eq_top.mp sphereHarmonicFamilyLp_denseSpan).ge

theorem roundSphereHarmonicHilbertBasis_apply (i : SphereHarmonicIndex) :
    roundSphereHarmonicHilbertBasis i = sphereHarmonicFamilyLp i := by
  unfold roundSphereHarmonicHilbertBasis
  exact congrFun (HilbertBasis.coe_mk _ _) i

/-- The Hilbert coefficient of a real continuous test is its integral against
the same actual real harmonic representative. -/
theorem roundSphereHarmonicHilbertBasis_repr_apply (f : C(RoundSphere3, ℝ)) (i : SphereHarmonicIndex) :
    roundSphereHarmonicHilbertBasis.repr (ContinuousMap.toLp 2 roundSphere3Measure ℝ f) i =
      ∫ x, f x * sphereHarmonicFamily i x ∂roundSphere3Measure := by
  rw [HilbertBasis.repr_apply_apply, roundSphereHarmonicHilbertBasis_apply, sphereHarmonicFamilyLp,
    ContinuousMap.inner_toLp]
  simp

theorem roundSphereHarmonicSeries_hasSum (f : C(RoundSphere3, ℝ)) :
    HasSum (fun i => (∫ x, f x * sphereHarmonicFamily i x ∂roundSphere3Measure) • sphereHarmonicFamilyLp i)
      (ContinuousMap.toLp 2 roundSphere3Measure ℝ f) := by
  simpa only [roundSphereHarmonicHilbertBasis_repr_apply, roundSphereHarmonicHilbertBasis_apply]
    using roundSphereHarmonicHilbertBasis.hasSum_repr (ContinuousMap.toLp 2 roundSphere3Measure ℝ f)

end Burnett.A06
