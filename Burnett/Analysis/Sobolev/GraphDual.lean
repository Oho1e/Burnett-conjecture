import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Topology.Algebra.Module.Basic

/- Tree-external construction for a genuine linear jet map J.  This generic
file does not identify an arbitrary J with the Sobolev jet of smooth tests. -/
noncomputable section

namespace Burnett.X02.GraphDual

variable {D A : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]

abbrev Graph (J : D →ₗ[ℝ] A) := ↥(LinearMap.range J).topologicalClosure

def testMap (J : D →ₗ[ℝ] A) : D →ₗ[ℝ] Graph J where
  toFun φ := ⟨J φ, (LinearMap.range J).le_topologicalClosure ⟨φ, rfl⟩⟩
  map_add' φ ψ := by
    apply Subtype.ext
    exact J.map_add φ ψ
  map_smul' a φ := by
    apply Subtype.ext
    exact J.map_smul a φ

theorem denseRange_testMap (J : D →ₗ[ℝ] A) : DenseRange (testMap J) := by
  intro x
  apply closure_subtype.mpr
  have himage : Subtype.val '' Set.range (testMap J) = (LinearMap.range J : Set A) := by
    ext a
    constructor
    · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
      exact ⟨φ, rfl⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨testMap J φ, ⟨φ, rfl⟩, rfl⟩
  rw [himage]
  exact x.property

def testRestriction (J : D →ₗ[ℝ] A) :
    (Graph J →L[ℝ] ℝ) →ₗ[ℝ] (D →ₗ[ℝ] ℝ) where
  toFun F := F.toLinearMap.comp (testMap J)
  map_add' F G := by ext φ; rfl
  map_smul' a F := by ext φ; rfl

theorem testRestriction_injective (J : D →ₗ[ℝ] A) :
    Function.Injective (testRestriction J) := by
  intro F G h
  apply DFunLike.coe_injective
  apply Continuous.ext_on (denseRange_testMap J) F.continuous G.continuous
  rintro _ ⟨φ, rfl⟩
  exact congrArg (fun L : D →ₗ[ℝ] ℝ => L φ) h

def coefficientFunctional (J : D →ₗ[ℝ] A) (c : A) : Graph J →L[ℝ] ℝ :=
  (innerSL ℝ c).comp (LinearMap.range J).topologicalClosure.subtypeL

theorem coefficientFunctional_apply (J : D →ₗ[ℝ] A) (c : A) (φ : D) :
    coefficientFunctional J c (testMap J φ) = inner ℝ c (J φ) := rfl

theorem norm_coefficientFunctional_le (J : D →ₗ[ℝ] A) (c : A) :
    ‖coefficientFunctional J c‖ ≤ ‖c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c)
  intro x
  exact norm_inner_le_norm c (x : A)

def coefficientMap (J : D →ₗ[ℝ] A) : A →L[ℝ] (Graph J →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := coefficientFunctional J
      map_add' := by intros; ext x; simp [coefficientFunctional]
      map_smul' := by intros; ext x; simp [coefficientFunctional] }
    1 (by intro c; simpa using norm_coefficientFunctional_le J c)

theorem coefficientFunctional_tendsto_zero {ι : Type*} (J : D →ₗ[ℝ] A)
    {l : Filter ι} {c : ι → A} (hc : Filter.Tendsto c l (nhds 0)) :
    Filter.Tendsto (fun i => coefficientFunctional J (c i)) l (nhds 0) := by
  change Filter.Tendsto ((coefficientMap J) ∘ c) l (nhds 0)
  simpa only [map_zero] using ((coefficientMap J).continuous.tendsto (0 : A)).comp hc

#print axioms denseRange_testMap
#print axioms testRestriction_injective
#print axioms norm_coefficientFunctional_le
#print axioms coefficientFunctional_tendsto_zero

end Burnett.X02.GraphDual
