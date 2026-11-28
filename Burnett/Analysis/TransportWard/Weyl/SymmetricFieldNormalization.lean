import Burnett.Analysis.TransportWard.Weyl.PointwiseVacuum

/-! A fixed orthonormal basis for the actual symmetric lower metric fields. -/

set_option autoImplicit false
set_option maxHeartbeats 4300000

noncomputable section

namespace Burnett.V03.Palatini

open Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open scoped BigOperators ContDiff Manifold

open private orderedMetricSlot from Burnett.Analysis.TransportWard.Weyl.PointwiseVacuum

local notation "I" => SymmetricMetricSlot
local notation "E" => CoordinateSpace

/-- The square root of the multiplicity of the independent entry in the
Euclidean ordered-pair contraction. -/
def symmetricMetricScale (i : I) : ℝ :=
  if i.val.1 = i.val.2 then 1 else Real.sqrt 2

theorem symmetricMetricScale_pos (i : I) : 0 < symmetricMetricScale i := by
  unfold symmetricMetricScale
  split_ifs <;> positivity

def orthonormalMetricDirection (i : I) : Mat :=
  (symmetricMetricScale i)⁻¹ • symmetricMetricDirection i

def normalizeMetricComponents (z : I → ℝ) (i : I) : ℝ :=
  symmetricMetricScale i * z i

theorem orthonormalMetricDirection_isSymmetric (i : I) :
    IsSymmetricTensor (orthonormalMetricDirection i) := by
  intro a b
  simp only [orthonormalMetricDirection, Matrix.smul_apply, smul_eq_mul,
    symmetricMetricDirection_isSymmetric i a b]

private theorem orderedMetricSlot_eq_iff (a b : Index) (i : I) :
    orderedMetricSlot a b = i ↔
      (a = i.val.1 ∧ b = i.val.2) ∨ (a = i.val.2 ∧ b = i.val.1) := by
  constructor
  · intro h
    have hpair := congrArg Subtype.val h
    change (min a b, max a b) = i.val at hpair
    by_cases hab : a ≤ b
    · rw [min_eq_left hab, max_eq_right hab] at hpair
      exact Or.inl ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
    · have hba : b ≤ a := le_of_not_ge hab
      rw [min_eq_right hba, max_eq_left hba] at hpair
      exact Or.inr ⟨congrArg Prod.snd hpair, congrArg Prod.fst hpair⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Subtype.ext (Prod.ext (min_eq_left i.2) (max_eq_right i.2))
    · exact Subtype.ext (Prod.ext (min_eq_right i.2) (max_eq_left i.2))

private theorem sum_symmetricMetricDirection (i : I) :
    (∑ a, ∑ b, symmetricMetricDirection i a b) = (symmetricMetricScale i)^2 := by
  classical
  by_cases hd : i.val.1 = i.val.2
  · have h (a b : Index) : symmetricMetricDirection i a b =
        if a = i.val.2 then (if b = i.val.2 then 1 else 0) else 0 := by
      by_cases ha : a = i.val.2 <;>
        simp [symmetricMetricDirection, orderedMetricSlot_eq_iff, hd, ha]
    simp [h, symmetricMetricScale, hd]
  · have h (a b : Index) : symmetricMetricDirection i a b =
        (if a = i.val.1 then (if b = i.val.2 then 1 else 0) else 0) +
          (if a = i.val.2 then (if b = i.val.1 then 1 else 0) else 0) := by
      by_cases ha : a = i.val.1
      · simp [symmetricMetricDirection, orderedMetricSlot_eq_iff, ha, hd]
      · by_cases ha' : a = i.val.2
        · simp [symmetricMetricDirection, orderedMetricSlot_eq_iff, ha', Ne.symm hd]
        · simp [symmetricMetricDirection, orderedMetricSlot_eq_iff, ha, ha']
    norm_num [h, Finset.sum_add_distrib, symmetricMetricScale, hd, Real.sq_sqrt]

/-- The Euclidean contraction uses all ordered entries. Each off-diagonal
basis tensor has entries `1/√2` in both transposed positions. -/
theorem orthonormalMetricDirection_ordered_pairing (i j : I) :
    (∑ a, ∑ b, orthonormalMetricDirection i a b * orthonormalMetricDirection j a b) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have h (a b : Index) : orthonormalMetricDirection i a b * orthonormalMetricDirection i a b =
        ((symmetricMetricScale i)⁻¹)^2 * symmetricMetricDirection i a b := by
      simp only [orthonormalMetricDirection, Matrix.smul_apply, smul_eq_mul, symmetricMetricDirection]
      split_ifs <;> ring
    simp only [h, ← Finset.mul_sum, sum_symmetricMetricDirection]
    have hd := (symmetricMetricScale_pos i).ne'
    field_simp
  · rw [if_neg hij]
    have h (a b : Index) : orthonormalMetricDirection i a b * orthonormalMetricDirection j a b = 0 := by
      simp only [orthonormalMetricDirection, Matrix.smul_apply, smul_eq_mul, symmetricMetricDirection]
      by_cases hi : orderedMetricSlot a b = i
      · have hj : orderedMetricSlot a b ≠ j := fun he => hij (hi.symm.trans he)
        simp [hj]
      · simp [hi]
    simp [h]

theorem assemble_orthonormalMetricDirection_normalize (z : I → ℝ) :
    assembleMetricComponents orthonormalMetricDirection (normalizeMetricComponents z) =
      assembleMetricComponents symmetricMetricDirection z := by
  rw [assembleMetricComponents_apply, assembleMetricComponents_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [normalizeMetricComponents, orthonormalMetricDirection, smul_smul]
  have h := (symmetricMetricScale_pos i).ne'
  rw [mul_comm (symmetricMetricScale i), mul_assoc, mul_inv_cancel₀ h, mul_one]

theorem assemble_orthonormalMetricDirection_at_slot (z : I → ℝ) (i : I) :
    assembleMetricComponents orthonormalMetricDirection (normalizeMetricComponents z)
      i.val.1 i.val.2 = z i := by
  rw [assemble_orthonormalMetricDirection_normalize, assemble_symmetricMetricDirection_at_slot]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The same lower metric tensor in the paper's orthonormal field coordinates. -/
theorem assembledCoordinateMetric_orthonormalMetricComponents
    (B : Field (M := M)) (hB : IsSymmetric B) (c : M) :
    assembledCoordinateMetric orthonormalMetricDirection
      (normalizeMetricComponents ∘ symmetricChartMetricComponents B c) =
        metricComponents (coordinateBilinear B c) := by
  rw [← assembledCoordinateMetric_symmetricChartMetricComponents B hB c]
  funext x
  exact assemble_orthonormalMetricDirection_normalize _

end Burnett.V03.Palatini
