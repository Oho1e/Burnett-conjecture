import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The actual smooth compactly supported test graph in five L² components

This tree-external module uses C∞, the inner infinity in WithTop ℕ∞, rather
than analytic Cω. It constructs the real test submodule and its actual
Fréchet-derivative jet. No weak-derivative identification is asserted.
-/

noncomputable section

namespace Burnett.X02.SobolevTestJet

open MeasureTheory
open scoped ContDiff

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev ScalarL2 := MeasureTheory.Lp ℝ 2 (volume : Measure Space)
abbrev JetSpace := PiLp 2 (fun _ : Fin 5 => ScalarL2)

/-- All real smooth compactly supported tests, without a fixed support compact. -/
def Test : Submodule ℝ (Space → ℝ) where
  carrier := {φ | ContDiff ℝ ∞ φ ∧ HasCompactSupport φ}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' := fun hφ hψ => ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
  smul_mem' := by
    intro r φ hφ
    refine ⟨ContDiff.const_smul r hφ.1, ?_⟩
    simpa only [Pi.smul_apply, Pi.smul_apply'] using
      (hφ.2.smul_left (f := fun _ : Space => r))

abbrev D := ↥Test

theorem test_smooth (φ : D) : ContDiff ℝ ∞ (φ : Space → ℝ) := φ.property.1

theorem test_compactSupport (φ : D) : HasCompactSupport (φ : Space → ℝ) := φ.property.2

theorem test_differentiable (φ : D) : Differentiable ℝ (φ : Space → ℝ) :=
  (test_smooth φ).differentiable (by simp)

def directional (i : Fin 4) (φ : Space → ℝ) (x : Space) : ℝ :=
  fderiv ℝ φ x (EuclideanSpace.single i 1)

theorem test_memLp (φ : D) : MemLp (φ : Space → ℝ) 2 (volume : Measure Space) :=
  (test_smooth φ).continuous.memLp_of_hasCompactSupport (test_compactSupport φ)

theorem directional_continuous (i : Fin 4) (φ : D) :
    Continuous (directional i (φ : Space → ℝ)) := by
  exact ((test_smooth φ).continuous_fderiv_apply (by simp)).comp
    (continuous_id.prodMk continuous_const)

theorem directional_compactSupport (i : Fin 4) (φ : D) :
    HasCompactSupport (directional i (φ : Space → ℝ)) :=
  HasCompactSupport.fderiv_apply ℝ (test_compactSupport φ) (EuclideanSpace.single i 1)

theorem directional_memLp (i : Fin 4) (φ : D) :
    MemLp (directional i (φ : Space → ℝ)) 2 (volume : Measure Space) :=
  (directional_continuous i φ).memLp_of_hasCompactSupport (directional_compactSupport i φ)

theorem directional_add (i : Fin 4) (φ ψ : D) :
    directional i ((φ + ψ : D) : Space → ℝ) =
      directional i (φ : Space → ℝ) + directional i (ψ : Space → ℝ) := by
  funext x
  change fderiv ℝ ((φ : Space → ℝ) + (ψ : Space → ℝ)) x (EuclideanSpace.single i 1) = _
  rw [fderiv_add (test_differentiable φ x) (test_differentiable ψ x)]
  rfl

theorem directional_smul (i : Fin 4) (r : ℝ) (φ : D) :
    directional i ((r • φ : D) : Space → ℝ) = r • directional i (φ : Space → ℝ) := by
  funext x
  change fderiv ℝ (r • (φ : Space → ℝ)) x (EuclideanSpace.single i 1) = _
  rw [fderiv_const_smul (test_differentiable φ x) r]
  rfl

def valueLp (φ : D) : ScalarL2 := (test_memLp φ).toLp (φ : Space → ℝ)

def directionalLp (i : Fin 4) (φ : D) : ScalarL2 :=
  (directional_memLp i φ).toLp (directional i (φ : Space → ℝ))

theorem valueLp_add (φ ψ : D) : valueLp (φ + ψ) = valueLp φ + valueLp ψ :=
  MemLp.toLp_add (test_memLp φ) (test_memLp ψ)

theorem valueLp_smul (r : ℝ) (φ : D) : valueLp (r • φ) = r • valueLp φ :=
  MemLp.toLp_const_smul r (test_memLp φ)

theorem directionalLp_add (i : Fin 4) (φ ψ : D) :
    directionalLp i (φ + ψ) = directionalLp i φ + directionalLp i ψ := by
  calc
    _ = ((directional_memLp i φ).add (directional_memLp i ψ)).toLp
        (directional i (φ : Space → ℝ) + directional i (ψ : Space → ℝ)) :=
      MemLp.toLp_congr (directional_memLp i (φ + ψ))
        ((directional_memLp i φ).add (directional_memLp i ψ))
        (Filter.Eventually.of_forall fun x => congrFun (directional_add i φ ψ) x)
    _ = _ := MemLp.toLp_add (directional_memLp i φ) (directional_memLp i ψ)

theorem directionalLp_smul (i : Fin 4) (r : ℝ) (φ : D) :
    directionalLp i (r • φ) = r • directionalLp i φ := by
  calc
    _ = ((directional_memLp i φ).const_smul r).toLp
        (r • directional i (φ : Space → ℝ)) :=
      MemLp.toLp_congr (directional_memLp i (r • φ))
        ((directional_memLp i φ).const_smul r)
        (Filter.Eventually.of_forall fun x => congrFun (directional_smul i r φ) x)
    _ = _ := MemLp.toLp_const_smul r (directional_memLp i φ)

def jet (φ : D) : JetSpace :=
  WithLp.toLp 2 (Fin.cases (valueLp φ) (fun i => directionalLp i φ))

@[simp] theorem jet_zero_component (φ : D) : jet φ 0 = valueLp φ := rfl

@[simp] theorem jet_succ_component (φ : D) (i : Fin 4) :
    jet φ i.succ = directionalLp i φ := rfl

theorem jet_add (φ ψ : D) : jet (φ + ψ) = jet φ + jet ψ := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa only [jet_zero_component, PiLp.add_apply] using valueLp_add φ ψ
  · simpa only [jet_succ_component, PiLp.add_apply] using directionalLp_add i φ ψ

theorem jet_smul (r : ℝ) (φ : D) : jet (r • φ) = r • jet φ := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa only [jet_zero_component, PiLp.smul_apply] using valueLp_smul r φ
  · simpa only [jet_succ_component, PiLp.smul_apply] using directionalLp_smul i r φ

/-- The actual linear five-component jet map, with derivative coordinates. -/
def J : D →ₗ[ℝ] JetSpace where
  toFun := jet
  map_add' := jet_add
  map_smul' := jet_smul

def graphClosure : Submodule ℝ JetSpace := (LinearMap.range J).topologicalClosure

abbrev H1Space := ↥graphClosure

instance : CompleteSpace H1Space := by
  unfold H1Space graphClosure
  infer_instance

/-- The test graph map into its closure; injectivity is not asserted here. -/
def intoH1 : D →ₗ[ℝ] H1Space where
  toFun φ := ⟨J φ, (LinearMap.range J).le_topologicalClosure ⟨φ, rfl⟩⟩
  map_add' φ ψ := Subtype.ext (J.map_add φ ψ)
  map_smul' r φ := Subtype.ext (J.map_smul r φ)

end Burnett.X02.SobolevTestJet
