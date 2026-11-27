import Burnett.Analysis.SpatialFreezing.FixedCubeFourier
import Mathlib.Analysis.Fourier.AddCircleMulti

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Set Topology Burnett.RicciSymbol
attribute [local instance] Real.fact_zero_lt_one

/-- The fixed unit-volume box used to identify the period \(1\) torus. -/
def centeredUnitFourierCube : Set (Index → ℝ) :=
  Icc (fun _ => -(1 / 2)) (fun _ => 1 / 2)

/-- Quotient each of the four rescaled spatial coordinates modulo one. -/
def centeredUnitTorusMod (x : Index → ℝ) : UnitAddTorus Index := fun j => (x j : UnitAddCircle)

theorem continuous_centered_unit_torus_mod : Continuous centeredUnitTorusMod :=
  continuous_pi fun j => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply j)

private def torusRepresentative (t : UnitAddTorus Index) : Index → ℝ :=
  fun j => ((AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (t j) :
    Ico (-(1 / 2 : ℝ)) (-(1 / 2) + 1)) : ℝ)

private theorem representative_mem (t : UnitAddTorus Index) : torusRepresentative t ∈ centeredUnitFourierCube := by
  constructor
  · intro j
    exact (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (t j)).2.1
  · intro j
    have h := (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (t j)).2.2
    change torusRepresentative t j < -(1 / 2) + 1 at h
    linarith

private theorem representative_mod (t : UnitAddTorus Index) :
    centeredUnitTorusMod (torusRepresentative t) = t := by
  funext j
  exact (AddCircle.equivIco (1 : ℝ) (-(1 / 2))).symm_apply_apply (t j)

private theorem centered_interval_boundary_mod :
    ((1 / 2 : ℝ) : UnitAddCircle) = ((-(1 / 2) : ℝ) : UnitAddCircle) := by
  calc
    _ = (((-(1 / 2) + 1 : ℝ) : UnitAddCircle)) :=
      congrArg ((↑) : ℝ → UnitAddCircle) (by norm_num)
    _ = _ := AddCircle.coe_add_period (1 : ℝ) (-(1 / 2))

private theorem representative_agrees {E : Type*} [Zero E]
    (f : (Index → ℝ) → E)
    (boundary : ∀ x ∈ centeredUnitFourierCube,
      (∃ j, x j = -(1 / 2) ∨ x j = 1 / 2) → f x = 0)
    (x : Index → ℝ) (hx : x ∈ centeredUnitFourierCube) :
    f (torusRepresentative (centeredUnitTorusMod x)) = f x := by
  let t := centeredUnitTorusMod x
  by_cases hFace : ∃ j, x j = 1 / 2
  · obtain ⟨j, hj⟩ := hFace
    have hRepFace : torusRepresentative t j = -(1 / 2) := by
      have hEq : ((torusRepresentative t j : ℝ) : UnitAddCircle) = ((-(1 / 2) : ℝ) : UnitAddCircle) := by
        calc
          _ = t j := congrFun (representative_mod t) j
          _ = ((1 / 2 : ℝ) : UnitAddCircle) := by change ((x j : ℝ) : UnitAddCircle) = _; rw [hj]
          _ = _ := centered_interval_boundary_mod
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (t j)).2 (by constructor <;> norm_num)).1 hEq
    exact (boundary _ (representative_mem t) ⟨j, Or.inl hRepFace⟩).trans
      (boundary _ hx ⟨j, Or.inr hj⟩).symm
  · have eq : torusRepresentative t = x := by
      funext j
      have le : x j ≤ 1 / 2 := hx.2 j
      have lt : x j < 1 / 2 := lt_of_le_of_ne le (fun h => hFace ⟨j, h⟩)
      have hI : x j ∈ Ico (-(1 / 2 : ℝ)) (-(1 / 2) + 1) :=
        ⟨hx.1 j, by linarith⟩
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (t j)).2 hI).1 (congrFun (representative_mod t) j)
    exact congrArg f eq

/-- A continuous profile that vanishes on the faces of the fixed cube gives
a continuous function on the actual four-dimensional unit torus, equal to
the profile on the entire closed cube. -/
theorem exists_centered_unit_torus_lift {E : Type*} [Zero E] [TopologicalSpace E]
    (f : (Index → ℝ) → E) (hf : Continuous f)
    (boundary : ∀ x ∈ centeredUnitFourierCube,
      (∃ j, x j = -(1 / 2) ∨ x j = 1 / 2) → f x = 0) :
    ∃ F : C(UnitAddTorus Index, E),
      ∀ x ∈ centeredUnitFourierCube, F (centeredUnitTorusMod x) = f x := by
  haveI : CompactSpace ↥centeredUnitFourierCube :=
    isCompact_iff_compactSpace.mp (isCompact_Icc (a := fun _ : Index => -(1 / 2 : ℝ))
      (b := fun _ : Index => 1 / 2))
  let q : ↥centeredUnitFourierCube → UnitAddTorus Index := centeredUnitTorusMod ∘ Subtype.val
  have qSurj (t : UnitAddTorus Index) : ∃ x, q x = t :=
    ⟨⟨torusRepresentative t, representative_mem t⟩, representative_mod t⟩
  have quotient : IsQuotientMap q := IsQuotientMap.of_surjective_continuous qSurj
    (continuous_centered_unit_torus_mod.comp continuous_subtype_val)
  have eq : (f ∘ torusRepresentative) ∘ q = f ∘ (Subtype.val : ↥centeredUnitFourierCube → _) :=
    funext fun x => representative_agrees f boundary x x.2
  have hContinuous : Continuous (f ∘ torusRepresentative) :=
    quotient.continuous_iff.mpr (eq.symm ▸ hf.comp continuous_subtype_val)
  exact ⟨⟨f ∘ torusRepresentative, hContinuous⟩, representative_agrees f boundary⟩

end Burnett.A03
